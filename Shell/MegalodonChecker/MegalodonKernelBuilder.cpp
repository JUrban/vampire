#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/SATInference.hpp"

#include <algorithm>
#include <limits>
#include <map>
#include <set>
#include <tuple>
#include <utility>

namespace Shell {
namespace MegalodonKernelBuilder {

namespace {

std::string quote(const std::string& value)
{
  std::string result = "\"";
  for (char ch : value) {
    switch (ch) {
      case '\\': result += "\\\\"; break;
      case '"': result += "\\\""; break;
      case '\n': result += "\\n"; break;
      case '\r': result += "\\r"; break;
      case '\t': result += "\\t"; break;
      default: result += ch; break;
    }
  }
  result += '"';
  return result;
}

MegalodonKernelSyntax::PrimitiveStep primitiveClauseStep(
  const std::string& rule,
  const std::string& id,
  const std::vector<std::string>& parentIds,
  const std::string& resultClause,
  const std::vector<std::pair<std::string, std::string>>& fields,
  const std::string& rendered)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = rule;
  step.id = id;
  step.rendered = rendered;
  step.builderOwned = true;
  step.parentIds = parentIds;
  step.hasResultClause = true;
  step.resultClause = resultClause;
  step.fields = fields;
  return step;
}

}

std::string PrimitiveChain::render(
  MegalodonKernelSyntax::PrimitiveStep primitive)
{
  const std::string rendered = primitive.rendered;
  _primitives[rendered] = std::move(primitive);
  return rendered;
}

bool PrimitiveChain::collect(
  const std::vector<std::string>& renderedSteps,
  std::vector<MegalodonKernelSyntax::PrimitiveStep>* primitiveSteps) const
{
  if (primitiveSteps == nullptr) {
    return true;
  }
  primitiveSteps->clear();
  for (const std::string& rendered : renderedSteps) {
    auto primitive = _primitives.find(rendered);
    if (primitive == _primitives.end()) {
      primitiveSteps->clear();
      return false;
    }
    primitiveSteps->push_back(primitive->second);
  }
  return true;
}

std::string skolemRefutationScopeBlock(
  const std::string& finalStep,
  const std::vector<MegalodonKernelSyntax::PrimitiveStep>& skolemSteps)
{
  if (finalStep.empty() || skolemSteps.empty()) {
    return "";
  }
  std::set<std::string> stepIds;
  std::set<std::string> symbols;
  std::string entries = "(entries";
  for (std::size_t index = 0; index < skolemSteps.size(); ++index) {
    const auto& step = skolemSteps[index];
    if (!step.builderOwned
      || step.rule != "skolem_formula"
      || step.id.empty()
      || step.certificateLocalSymbols.empty()
      || !stepIds.insert(step.id).second) {
      return "";
    }
    entries +=
      " (entry (index " + std::to_string(index) + ")"
      + " (step " + quote(step.id) + ") (symbols";
    for (const std::string& symbol : step.certificateLocalSymbols) {
      if (symbol.empty() || !symbols.insert(symbol).second) {
        return "";
      }
      entries += " " + quote(symbol);
    }
    entries += "))";
  }
  entries += ")";

  std::string dischargeOrder = "(discharge_order";
  for (auto step = skolemSteps.rbegin(); step != skolemSteps.rend(); ++step) {
    dischargeOrder += " " + quote(step->id);
  }
  dischargeOrder += ")";
  return
    "(skolem_scope_block \"smolka_refutation_v2\""
    " (final " + quote(finalStep) + ") "
    + entries + " " + dischargeOrder + ")";
}

std::string skolemRefutationUseBlock(
  const std::string& finalStep,
  const std::vector<MegalodonKernelSyntax::PrimitiveStep>& skolemSteps,
  const std::vector<MegalodonKernelSyntax::RenderedKernelSkolemUse>& uses)
{
  if (finalStep.empty() || skolemSteps.empty()) {
    return "";
  }
  std::map<std::pair<std::string, std::string>, std::size_t> declarations;
  for (const auto& step : skolemSteps) {
    if (!step.builderOwned
      || step.rule != "skolem_formula"
      || step.id.empty()
      || step.certificateLocalSymbols.empty()
      || step.certificateLocalSymbols.size()
        != step.certificateLocalSymbolDependencyCounts.size()) {
      return "";
    }
    for (std::size_t index = 0;
         index < step.certificateLocalSymbols.size();
         ++index) {
      const auto key = std::make_pair(
        step.id, step.certificateLocalSymbols[index]);
      if (key.second.empty()
        || !declarations.emplace(
          key, step.certificateLocalSymbolDependencyCounts[index]).second) {
        return "";
      }
    }
  }

  std::map<std::pair<std::string, std::string>,
    std::vector<MegalodonKernelSyntax::RenderedKernelSkolemUse>> grouped;
  std::set<std::tuple<std::string, std::string, std::string, std::string>> seen;
  for (const auto& use : uses) {
    const auto key = std::make_pair(use.skolemStep, use.symbol);
    auto declaration = declarations.find(key);
    if (declaration == declarations.end()
      || declaration->second != use.dependencyCount
      || use.unit.empty()
      || use.term.sexpr.empty()
      || !seen.emplace(
        use.skolemStep, use.symbol, use.unit, use.term.sexpr).second) {
      return "";
    }
    grouped[key].push_back(use);
  }

  std::string entries = "(entries";
  std::size_t entryIndex = 0;
  for (const auto& step : skolemSteps) {
    for (std::size_t symbolIndex = 0;
         symbolIndex < step.certificateLocalSymbols.size();
         ++symbolIndex) {
      const std::string& symbol = step.certificateLocalSymbols[symbolIndex];
      const auto key = std::make_pair(step.id, symbol);
      auto found = grouped.find(key);
      if (found == grouped.end() || found->second.empty()) {
        return "";
      }
      entries +=
        " (entry (index " + std::to_string(entryIndex++) + ")"
        + " (step " + quote(step.id) + ")"
        + " (symbol " + quote(symbol) + ")"
        + " (dependency_count "
        + std::to_string(step.certificateLocalSymbolDependencyCounts[symbolIndex])
        + ") (uses";
      for (std::size_t useIndex = 0;
           useIndex < found->second.size();
           ++useIndex) {
        const auto& use = found->second[useIndex];
        entries +=
          " (use (index " + std::to_string(useIndex) + ")"
          + " (unit " + quote(use.unit) + ")"
          + " (term " + use.term.sexpr + "))";
      }
      entries += "))";
    }
  }
  entries += ")";
  return
    "(skolem_use_block \"smolka_uses_v1\""
    " (final " + quote(finalStep) + ") " + entries + ")";
}

std::string avatarPrimitiveWithMetadata(
  const MegalodonKernelSyntax::PrimitiveStep& step)
{
  std::vector<std::pair<std::string, std::string>> fields{
    {"schema", MegalodonKernelSyntax::schema()},
    {"rule", step.rule},
    {"primitive_expansion", "prefix"},
    {"primitive_expansion_prefix", step.id},
    {"primitive_expansion_requires", step.rule},
  };
  fields.insert(fields.end(), step.fields.begin(), step.fields.end());
  if (step.hasResultClause) {
    fields.push_back({"result_clause", step.resultClause});
  }
  std::string rendered =
    "(step_extra " + quote(step.id) + " \"avatar_scope_v1\" (";
  for (std::size_t index = 0; index < fields.size(); ++index) {
    if (index != 0) {
      rendered += " ";
    }
    rendered += quote(fields[index].first + "=" + fields[index].second);
  }
  rendered += "))";
  return rendered + "\n  " + step.rendered;
}

MegalodonKernelSyntax::PrimitiveStep resolveStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& leftParent,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& rightParent,
  std::size_t leftPivot,
  std::size_t rightPivot,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string leftPivotText = std::to_string(leftPivot);
  const std::string rightPivotText = std::to_string(rightPivot);
  return primitiveClauseStep(
    "resolve",
    id,
    {leftParent.value, rightParent.value},
    result.sexpr,
    {{"pivot_left", leftPivotText}, {"pivot_right", rightPivotText}},
    "(resolve " + quote(id)
      + " (parents " + quote(leftParent.value) + " " + quote(rightParent.value) + ")"
      + " (pivot " + leftPivotText + " " + rightPivotText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep factorStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t leftLiteral,
  std::size_t rightLiteral,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string leftLiteralText = std::to_string(leftLiteral);
  const std::string rightLiteralText = std::to_string(rightLiteral);
  return primitiveClauseStep(
    "factor",
    id,
    {parent.value},
    result.sexpr,
    {{"literal_left", leftLiteralText}, {"literal_right", rightLiteralText}},
    "(factor " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literals " + leftLiteralText + " " + rightLiteralText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep equalitySymmetryStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string literalText = std::to_string(literal);
  return primitiveClauseStep(
    "equality_symmetry",
    id,
    {parent.value},
    result.sexpr,
    {{"literal", literalText}},
    "(equality_symmetry " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep substituteStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelSubstitution& substitution,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  return primitiveClauseStep(
    "substitute",
    id,
    {parent.value},
    result.sexpr,
    {{"substitution", substitution.sexpr}},
    "(substitute " + quote(id)
      + " (parent " + quote(parent.value) + ") " + substitution.sexpr
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep equalityResolutionStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields)
{
  const std::string literalText = std::to_string(literal);
  return primitiveClauseStep(
    "equality_resolution",
    id,
    {parent.value},
    result.sexpr,
    metadataFields,
    "(equality_resolution " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep equalityResolutionConstraintsStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelLiteral& selected,
  const MegalodonKernelSyntax::RenderedKernelClause& constraints,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields)
{
  const std::string literalText = std::to_string(literal);
  return primitiveClauseStep(
    "equality_resolution_constraints",
    id,
    {parent.value},
    result.sexpr,
    metadataFields,
    "(equality_resolution_constraints " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (selected " + selected.sexpr + ")"
      + " (constraints " + constraints.sexpr + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep paramodulateStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& equalityParent,
  std::size_t equalityLiteral,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& targetParent,
  std::size_t targetLiteral,
  const MegalodonKernelSyntax::RenderedKernelPosition& position,
  const MegalodonKernelSyntax::RenderedKernelTerm& from,
  const MegalodonKernelSyntax::RenderedKernelTerm& to,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string equalityLiteralText = std::to_string(equalityLiteral);
  const std::string targetLiteralText = std::to_string(targetLiteral);
  return primitiveClauseStep(
    "paramodulate",
    id,
    {equalityParent.value, targetParent.value},
    result.sexpr,
    {
      {"equality_literal", equalityLiteralText},
      {"target_literal", targetLiteralText},
      {"position", position.sexpr},
      {"from", from.sexpr},
      {"to", to.sexpr},
    },
    "(paramodulate " + quote(id)
      + " (equality " + quote(equalityParent.value) + " " + equalityLiteralText + ")"
      + " (target " + quote(targetParent.value) + " " + targetLiteralText + ") "
      + position.sexpr
      + " (from " + from.sexpr + ")"
      + " (to " + to.sexpr + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep foolAtomLiftStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFormula& target,
  const std::string& path,
  const std::vector<std::pair<
    std::string,
    MegalodonKernelSyntax::RenderedKernelType>>& context)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "fool_atom_lift";
  step.id = id;
  step.builderOwned = true;
  step.fields = {
    {"source_formula", source.sexpr},
    {"target_formula", target.sexpr},
    {"path", path},
  };
  std::string renderedContext = "(context";
  step.fields.push_back({"context_count", std::to_string(context.size())});
  for (std::size_t index = 0; index < context.size(); ++index) {
    renderedContext +=
      " (variable " + quote(context[index].first)
      + " " + context[index].second.sexpr + ")";
    step.fields.push_back({
      "context_" + std::to_string(index) + "_name",
      context[index].first,
    });
    step.fields.push_back({
      "context_" + std::to_string(index) + "_type",
      context[index].second.sexpr,
    });
  }
  renderedContext += ")";
  step.rendered =
    "(fool_atom_lift " + quote(id)
    + " (source (formula " + source.sexpr + "))"
    + " (target (formula " + target.sexpr + "))"
    + " (path " + quote(path) + ")"
    + " " + renderedContext
    + " (builder \"typed_v1\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep rectifyFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFormula& result,
  const MegalodonKernelSyntax::RenderedKernelRectifyRenamings& renamings)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "rectify_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields.push_back({"source_formula", source.sexpr});
  step.fields.push_back({
    "renaming_count",
    std::to_string(renamings.reportedCount),
  });
  if (renamings.hasVariableMap) {
    step.fields.push_back({
      "free_variable_map",
      renamings.variableMap.sexpr,
    });
  }

  std::string renderedRenamings;
  if (!renamings.renamings.empty()) {
    renderedRenamings = " (renamings";
    for (const auto& renaming : renamings.renamings) {
      renderedRenamings +=
        " (renaming (source (formula " + renaming.source.sexpr + ")) "
        + renaming.substitution.sexpr
        + " (ambient_variable_map " + renaming.ambientVariableMap.sexpr + ")"
        + " (target (formula " + renaming.target.sexpr + ")))";
      const std::string prefix =
        "renaming_" + std::to_string(renaming.index);
      step.fields.push_back({prefix + "_source", renaming.source.sexpr});
      step.fields.push_back({prefix + "_target", renaming.target.sexpr});
      step.fields.push_back({
        prefix + "_substitution",
        renaming.substitution.sexpr,
      });
      step.fields.push_back({
        prefix + "_ambient_variable_map",
        renaming.ambientVariableMap.sexpr,
      });
    }
    renderedRenamings += ")";
  }
  const std::string renderedVariableMap =
    renamings.hasVariableMap ? renamings.variableMap.sexpr : "(subst)";
  step.rendered =
    "(rectify_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + "))"
    + " (free_variable_map " + renderedVariableMap + ")"
    + renderedRenamings
    + " (result (formula " + result.sexpr + ")))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep cnfLiteralStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  return primitiveClauseStep(
    "cnf_literal",
    id,
    {parent.value},
    result.sexpr,
    {},
    "(cnf_literal " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep ennfFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelEnnfTrace& trace,
  const MegalodonKernelSyntax::RenderedKernelFormula& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  const std::string renderedTrace =
    MegalodonKernelSyntax::renderEnnfTrace(trace);
  step.rule = "ennf_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {
    {"source_formula", source.sexpr},
    {"ennf_trace", renderedTrace},
    {"selection_source", "nnf_v1"},
    {"primitive_lowering_source", "nnf_v1"},
  };
  step.rendered =
    "(ennf_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + "))"
    + " (trace " + renderedTrace + ")"
    + " (result (formula " + result.sexpr + "))"
    + " (builder \"typed_v1\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep skolemFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const std::vector<MegalodonKernelSyntax::RenderedKernelScopedSkolemBranch>& branches,
  const MegalodonKernelSyntax::RenderedKernelFormula& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "skolem_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {
    {"source_formula", source.sexpr},
    {"branch_count", std::to_string(branches.size())},
    {"path_encoding", "binary_kernel_term_v1"},
    {"selection_source", "skolem_v1"},
    {"primitive_lowering_source", "skolem_v1"},
  };

  std::string renderedBranches = "(branches";
  for (const auto& branch : branches) {
    const std::string prefix = "branch_" + std::to_string(branch.index);
    step.fields.push_back({prefix + "_source", branch.source.sexpr});
    step.fields.push_back({prefix + "_target", branch.target.sexpr});
    std::string renderedPath = "(path";
    for (std::size_t child : branch.path) {
      renderedPath += " " + std::to_string(child);
    }
    renderedPath += ")";
    step.fields.push_back({prefix + "_path", renderedPath});
    step.fields.push_back({prefix + "_normalization", branch.normalization});
    step.fields.push_back({
      prefix + "_context_count",
      std::to_string(branch.context.size()),
    });
    step.fields.push_back({
      prefix + "_witness_count",
      std::to_string(branch.witnesses.size()),
    });

    renderedBranches +=
      " (branch (index " + std::to_string(branch.index) + ")"
      + " " + renderedPath
      + " (normalization " + quote(branch.normalization) + ")"
      + " (source (formula " + branch.source.sexpr + "))"
      + " (ambient";
    for (const auto& variable : branch.ambient) {
      renderedBranches +=
        " (variable " + quote(variable.variable) + " " + variable.type.sexpr + ")";
    }
    renderedBranches += ")";
    renderedBranches += " (context";
    for (const auto& variable : branch.context) {
      renderedBranches +=
        " (variable " + quote(variable.variable) + " " + variable.type.sexpr + ")";
    }
    renderedBranches += ") (witnesses";
    for (std::size_t witnessIndex = 0;
         witnessIndex < branch.witnesses.size();
         ++witnessIndex) {
      const auto& witness = branch.witnesses[witnessIndex];
      step.certificateLocalSymbols.push_back(witness.symbol);
      step.certificateLocalSymbolDependencyCounts.push_back(
        witness.dependencies.size());
      const std::string witnessPrefix =
        prefix + "_witness_" + std::to_string(witnessIndex);
      step.fields.push_back({witnessPrefix + "_symbol", witness.symbol});
      step.fields.push_back({
        witnessPrefix + "_replaced_variable",
        witness.replacedVariable,
      });
      step.fields.push_back({witnessPrefix + "_sort", witness.replacedSort.sexpr});
      step.fields.push_back({witnessPrefix + "_term", witness.witnessTerm.sexpr});
      step.fields.push_back({
        witnessPrefix + "_dependency_count",
        std::to_string(witness.dependencies.size()),
      });

      renderedBranches +=
        " (witness (index " + std::to_string(witnessIndex) + ")"
        + " (kind " + quote(witness.typeVariable ? "type" : "term") + ")"
        + " (symbol " + quote(witness.symbol) + ")"
        + " (replaced_variable " + quote(witness.replacedVariable) + ")"
        + " (sort " + witness.replacedSort.sexpr + ")"
        + " (term " + witness.witnessTerm.sexpr + ")"
        + " (dependencies";
      for (const auto& dependency : witness.dependencies) {
        renderedBranches +=
          " (variable " + quote(dependency.variable) + " "
          + dependency.type.sexpr + ")";
      }
      renderedBranches += "))";
    }
    renderedBranches +=
      ") (target (formula " + branch.target.sexpr + ")))";
  }
  renderedBranches += ")";
  step.rendered =
    "(skolem_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + ")) "
    + renderedBranches
    + " (result (formula " + result.sexpr + "))"
    + " (builder \"typed_v2\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep cnfFormulaClauseStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  std::size_t index,
  std::size_t count,
  const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string renderedProjection =
    MegalodonKernelSyntax::renderCnfProjection(projection);
  return primitiveClauseStep(
    "cnf_formula_clause",
    id,
    {parent.value},
    result.sexpr,
    {
      {"source_formula", source.sexpr},
      {"clause_index", std::to_string(index)},
      {"clause_count", std::to_string(count)},
      {"cnf_projection", renderedProjection},
    },
    "(cnf_formula_clause " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (source (formula " + source.sexpr + "))"
      + " (index " + std::to_string(index) + ")"
      + " (count " + std::to_string(count) + ")"
      + " (projection " + renderedProjection + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep avatarComponentStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  return primitiveClauseStep(
    "avatar_component",
    id,
    {},
    result.sexpr,
    {
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_component " + quote(id) + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep avatarDefinitionStep(
  const std::string& id,
  unsigned splitVariable,
  bool splitPositive,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string splitVariableText = std::to_string(splitVariable);
  const std::string splitPositiveText = splitPositive ? "true" : "false";
  return primitiveClauseStep(
    "avatar_definition",
    id,
    {},
    result.sexpr,
    {
      {"split_variable", splitVariableText},
      {"split_positive", splitPositiveText},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_definition " + quote(id)
      + " (split " + splitVariableText + " " + splitPositiveText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep splitDependencyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& owner,
  const std::vector<MegalodonKernelSyntax::RenderedKernelSplitDependencyItem>& dependencies,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  std::string renderedDependencies = "(dependencies";
  for (const auto& dependency : dependencies) {
    if (!dependency.hasComponentClauseSexpr) {
      continue;
    }
    renderedDependencies +=
      " (dependency " + std::to_string(dependency.split.variable)
      + " " + (dependency.split.positive ? "true" : "false")
      + " (component " + dependency.componentClauseSexpr.sexpr + "))";
  }
  renderedDependencies += ")";
  return primitiveClauseStep(
    "split_dependency",
    id,
    {owner.value},
    result.sexpr,
    {
      {"dependency_count", std::to_string(dependencies.size())},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(split_dependency " + quote(id)
      + " (owner " + quote(owner.value) + ") "
      + renderedDependencies
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep avatarSplitStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& parents,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  for (const auto& parent : parents) {
    parentIds.push_back(parent.value);
    renderedParents += " " + quote(parent.value);
  }
  renderedParents += ")";
  return primitiveClauseStep(
    "avatar_split",
    id,
    parentIds,
    result.sexpr,
    {
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_split " + quote(id) + " " + renderedParents
      + " (result " + result.sexpr + "))");
}

namespace {

using SatLiteral = MegalodonKernelSyntax::RenderedKernelSatLiteral;
using SatClause = std::vector<SatLiteral>;

enum class ExactSatOperationKind {
  Resolve,
  Factor,
  Permute,
};

struct ExactSatOperation {
  ExactSatOperationKind kind = ExactSatOperationKind::Permute;
  unsigned rightParent = 0;
  std::size_t leftIndex = 0;
  std::size_t rightIndex = 0;
  SatClause result;
};

std::string renderSatClause(const SatClause& clause)
{
  std::string rendered = "(sat_clause";
  for (const SatLiteral& literal : clause) {
    rendered +=
      " (lit " + std::to_string(literal.variable)
      + " " + (literal.positive ? "true" : "false") + ")";
  }
  return rendered + ")";
}

bool satLiteralLess(const SatLiteral& left, const SatLiteral& right)
{
  if (left.variable != right.variable) {
    return left.variable < right.variable;
  }
  return left.positive < right.positive;
}

bool sameSatClauseMultiset(SatClause left, SatClause right)
{
  std::sort(left.begin(), left.end(), satLiteralLess);
  std::sort(right.begin(), right.end(), satLiteralLess);
  return left == right;
}

bool complementarySatLiterals(const SatLiteral& left, const SatLiteral& right)
{
  return left.variable == right.variable && left.positive != right.positive;
}

SatClause removeSatLiteral(const SatClause& clause, std::size_t index)
{
  SatClause result;
  result.reserve(clause.size() - 1);
  for (std::size_t current = 0; current < clause.size(); ++current) {
    if (current != index) {
      result.push_back(clause[current]);
    }
  }
  return result;
}

void factorSatClause(SatClause& clause, std::vector<ExactSatOperation>& operations)
{
  while (true) {
    bool found = false;
    for (std::size_t left = 0; left < clause.size() && !found; ++left) {
      for (std::size_t right = left + 1; right < clause.size(); ++right) {
        if (clause[left] != clause[right]) {
          continue;
        }
        clause = removeSatLiteral(clause, right);
        ExactSatOperation operation;
        operation.kind = ExactSatOperationKind::Factor;
        operation.leftIndex = left;
        operation.rightIndex = right;
        operation.result = clause;
        operations.push_back(std::move(operation));
        found = true;
        break;
      }
    }
    if (!found) {
      return;
    }
  }
}

bool lowerOrderedSatResolution(
  const SatClause& current,
  const std::vector<std::pair<unsigned, SatClause>>& parents,
  std::size_t parentIndex,
  const SatClause& target,
  std::vector<ExactSatOperation>& operations)
{
  if (parentIndex == parents.size()) {
    return sameSatClauseMultiset(current, target);
  }
  const auto& [rightParent, rightClause] = parents[parentIndex];
  for (std::size_t leftIndex = 0; leftIndex < current.size(); ++leftIndex) {
    for (std::size_t rightIndex = 0; rightIndex < rightClause.size(); ++rightIndex) {
      if (!complementarySatLiterals(current[leftIndex], rightClause[rightIndex])) {
        continue;
      }
      const std::size_t checkpoint = operations.size();
      SatClause next = removeSatLiteral(current, leftIndex);
      SatClause rightRest = removeSatLiteral(rightClause, rightIndex);
      next.insert(next.end(), rightRest.begin(), rightRest.end());
      ExactSatOperation operation;
      operation.kind = ExactSatOperationKind::Resolve;
      operation.rightParent = rightParent;
      operation.leftIndex = leftIndex;
      operation.rightIndex = rightIndex;
      operation.result = next;
      operations.push_back(std::move(operation));
      factorSatClause(next, operations);
      if (lowerOrderedSatResolution(
            next, parents, parentIndex + 1, target, operations)) {
        return true;
      }
      operations.resize(checkpoint);
    }
  }
  return false;
}

bool lowerAvatarSatProof(
  const std::vector<MegalodonKernelSyntax::RenderedKernelSatProofStep>& sourceSteps,
  std::string& rendered,
  std::size_t& exactStepCount,
  std::size_t& rupStepCount)
{
  unsigned maximumSourceId = 0;
  for (const auto& step : sourceSteps) {
    maximumSourceId = std::max(maximumSourceId, step.id);
  }
  if (maximumSourceId == std::numeric_limits<unsigned>::max()) {
    return false;
  }
  unsigned nextSyntheticId = maximumSourceId + 1;
  std::map<unsigned, SatClause> checked;
  rendered = "(sat_proof";
  exactStepCount = 0;
  rupStepCount = 0;
  for (const auto& step : sourceSteps) {
    if (step.id == 0 || checked.find(step.id) != checked.end()) {
      return false;
    }
    if (step.kind == "input") {
      checked.emplace(step.id, step.literals);
      rendered +=
        " (sat_input " + std::to_string(step.id)
        + " " + renderSatClause(step.literals) + ")";
      ++exactStepCount;
      continue;
    }
    if (step.kind != "rup" || step.parents.empty()) {
      return false;
    }
    ++rupStepCount;
    std::vector<std::pair<unsigned, SatClause>> parents;
    for (const auto& parent : step.parents) {
      const auto found = checked.find(parent.id);
      if (found == checked.end()) {
        return false;
      }
      parents.emplace_back(parent.id, found->second);
    }
    SatClause initial = parents.front().second;
    std::vector<ExactSatOperation> operations;
    factorSatClause(initial, operations);
    if (!lowerOrderedSatResolution(
          initial, parents, 1, step.literals, operations)) {
      return false;
    }
    const SatClause finalClause = operations.empty() ? initial : operations.back().result;
    if (operations.empty() || finalClause != step.literals) {
      ExactSatOperation permutation;
      permutation.kind = ExactSatOperationKind::Permute;
      permutation.result = step.literals;
      operations.push_back(std::move(permutation));
    }
    unsigned currentId = parents.front().first;
    for (std::size_t index = 0; index < operations.size(); ++index) {
      const ExactSatOperation& operation = operations[index];
      const bool finalOperation = index + 1 == operations.size();
      if (!finalOperation && nextSyntheticId == 0) {
        return false;
      }
      const unsigned operationId =
        finalOperation ? step.id : nextSyntheticId++;
      switch (operation.kind) {
        case ExactSatOperationKind::Resolve:
          rendered +=
            " (sat_resolve " + std::to_string(operationId)
            + " (left " + std::to_string(currentId)
            + " " + std::to_string(operation.leftIndex) + ")"
            + " (right " + std::to_string(operation.rightParent)
            + " " + std::to_string(operation.rightIndex) + ")"
            + " (result " + renderSatClause(operation.result) + "))";
          break;
        case ExactSatOperationKind::Factor:
          rendered +=
            " (sat_factor " + std::to_string(operationId)
            + " (parent " + std::to_string(currentId) + ")"
            + " (literals " + std::to_string(operation.leftIndex)
            + " " + std::to_string(operation.rightIndex) + ")"
            + " (result " + renderSatClause(operation.result) + "))";
          break;
        case ExactSatOperationKind::Permute:
          rendered +=
            " (sat_permute " + std::to_string(operationId)
            + " (parent " + std::to_string(currentId) + ")"
            + " (result " + renderSatClause(operation.result) + "))";
          break;
      }
      currentId = operationId;
      ++exactStepCount;
    }
    checked.emplace(step.id, step.literals);
  }
  rendered += ")";
  return !sourceSteps.empty();
}

}

bool collectAvatarSatProof(
  SAT::SATClause* root,
  MegalodonKernelSyntax::RenderedKernelAvatarRefutation* refutation)
{
  if (root == nullptr || refutation == nullptr) {
    return false;
  }
  struct CompareSATClauses {
    bool operator()(SAT::SATClause* left, SAT::SATClause* right) const
    {
      return left->number < right->number;
    }
  };
  std::set<SAT::SATClause*, CompareSATClauses> proof;
  std::vector<SAT::SATClause*> todo{root};
  while (!todo.empty()) {
    SAT::SATClause* current = todo.back();
    todo.pop_back();
    if (current == nullptr || !proof.insert(current).second) {
      continue;
    }
    SAT::SATInference* inference = current->inference();
    if (inference == nullptr || inference->getType() != SAT::SATInference::PROP_INF) {
      continue;
    }
    auto* prop = static_cast<SAT::PropInference*>(inference);
    for (SAT::SATClause* parent : Lib::iterTraits(prop->getPremises()->iter())) {
      todo.push_back(parent);
    }
  }

  refutation->inputs.clear();
  refutation->proofSteps.clear();
  refutation->hasSatRefutationClause = true;
  refutation->satRefutationClause =
    MegalodonKernelSyntax::clause(renderSatClause(
      [&]() {
        SatClause literals;
        for (SAT::SATLiteral literal : root->iter()) {
          literals.push_back({literal.var(), literal.positive()});
        }
        return literals;
      }()));
  std::size_t proofIndex = 0;
  std::size_t inputIndex = 0;
  for (SAT::SATClause* clause : proof) {
    MegalodonKernelSyntax::RenderedKernelSatProofStep step;
    step.index = proofIndex++;
    step.id = clause->number;
    for (SAT::SATLiteral literal : clause->iter()) {
      step.literals.push_back({literal.var(), literal.positive()});
    }
    step.hasClause = true;
    step.clause = MegalodonKernelSyntax::clause(renderSatClause(step.literals));
    SAT::SATInference* inference = clause->inference();
    if (inference == nullptr) {
      return false;
    }
    if (inference->getType() == SAT::SATInference::FO_CONVERSION) {
      Kernel::Unit* origin = inference->foConversion()->getOrigin();
      if (origin == nullptr) {
        return false;
      }
      step.kind = "input";
      step.hasOriginUnit = true;
      step.originUnit =
        MegalodonKernelSyntax::unitRef("u" + std::to_string(origin->number()));
      MegalodonKernelSyntax::RenderedKernelSatInput input;
      input.index = inputIndex++;
      input.hasClause = true;
      input.clause = step.clause;
      input.hasOriginUnit = true;
      input.originUnit = step.originUnit;
      refutation->inputs.push_back(std::move(input));
    } else if (inference->getType() == SAT::SATInference::PROP_INF) {
      step.kind = "rup";
      auto* prop = static_cast<SAT::PropInference*>(inference);
      std::size_t parentIndex = 0;
      for (SAT::SATClause* parent : Lib::iterTraits(prop->getPremises()->iter())) {
        MegalodonKernelSyntax::RenderedKernelSatProofParent renderedParent;
        renderedParent.index = parentIndex++;
        renderedParent.id = parent->number;
        SatClause parentLiterals;
        for (SAT::SATLiteral literal : parent->iter()) {
          parentLiterals.push_back({literal.var(), literal.positive()});
        }
        renderedParent.hasClause = true;
        renderedParent.clause =
          MegalodonKernelSyntax::clause(renderSatClause(parentLiterals));
        step.parents.push_back(std::move(renderedParent));
      }
    } else {
      return false;
    }
    refutation->proofSteps.push_back(std::move(step));
  }
  return true;
}

bool avatarRefutationStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelAvatarRefutation& refutation,
  MegalodonKernelSyntax::PrimitiveStep* result)
{
  if (result == nullptr || !refutation.hasResultClause) {
    return false;
  }
  std::string satProof;
  std::size_t exactStepCount = 0;
  std::size_t rupStepCount = 0;
  if (!lowerAvatarSatProof(
        refutation.proofSteps, satProof, exactStepCount, rupStepCount)) {
    return false;
  }
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  std::string renderedSatClauses = "(sat_clauses";
  for (const auto& input : refutation.inputs) {
    if (!input.hasOriginUnit || !input.hasClause) {
      return false;
    }
    parentIds.push_back(input.originUnit.value);
    renderedParents += " " + quote(input.originUnit.value);
    renderedSatClauses += " " + input.clause.sexpr;
  }
  renderedParents += ")";
  renderedSatClauses += ")";
  *result = primitiveClauseStep(
    "avatar_refutation",
    id,
    parentIds,
    refutation.resultClause.sexpr,
    {
      {"sat_input_count", std::to_string(refutation.inputs.size())},
      {"sat_proof_format", "resolution_v1"},
      {"sat_lowering_source", "rup_resolution_v1"},
      {"sat_proof_step_count", std::to_string(exactStepCount)},
      {"sat_rup_source_step_count", std::to_string(rupStepCount)},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_refutation " + quote(id) + " " + renderedParents
      + " " + renderedSatClauses + " " + satProof
      + " (result " + refutation.resultClause.sexpr + "))");
  return true;
}

namespace {

using KernelSymbol = std::pair<bool, unsigned>;

void collectFormulaSymbols(Kernel::Formula* formula, std::set<KernelSymbol>& symbols);

void collectTermSymbols(Kernel::TermList term, std::set<KernelSymbol>& symbols)
{
  if (term.isVar()) {
    return;
  }
  if (term.isApplication()) {
    collectTermSymbols(term.lhs(), symbols);
    collectTermSymbols(term.rhs(), symbols);
    return;
  }
  if (!term.isTerm()) {
    return;
  }
  Kernel::Term* value = term.term();
  if (value->isSpecial()) {
    const Kernel::Term::SpecialTermData* data = value->getSpecialData();
    switch (value->specialFunctor()) {
      case Kernel::SpecialFunctor::FORMULA:
        collectFormulaSymbols(data->getFormula(), symbols);
        return;
      case Kernel::SpecialFunctor::ITE:
        collectFormulaSymbols(data->getITECondition(), symbols);
        for (unsigned index = 0; index < value->arity(); ++index) {
          collectTermSymbols(*value->nthArgument(index), symbols);
        }
        return;
      case Kernel::SpecialFunctor::LET:
        collectFormulaSymbols(data->getLetBinding(), symbols);
        for (unsigned index = 0; index < value->arity(); ++index) {
          collectTermSymbols(*value->nthArgument(index), symbols);
        }
        return;
      case Kernel::SpecialFunctor::LAMBDA:
        collectTermSymbols(data->getLambdaExp(), symbols);
        return;
      case Kernel::SpecialFunctor::MATCH:
        for (unsigned index = 0; index < value->arity(); ++index) {
          collectTermSymbols(*value->nthArgument(index), symbols);
        }
        return;
    }
  }
  if (!env.signature->getFunction(value->functor())->interpreted()) {
    symbols.insert({true, value->functor()});
  }
  for (unsigned index = 0; index < value->numTermArguments(); ++index) {
    collectTermSymbols(value->termArg(index), symbols);
  }
}

void collectLiteralSymbols(Kernel::Literal* literal, std::set<KernelSymbol>& symbols)
{
  if (!env.signature->getPredicate(literal->functor())->interpreted()) {
    symbols.insert({false, literal->functor()});
  }
  for (unsigned index = 0; index < literal->arity(); ++index) {
    collectTermSymbols(*literal->nthArgument(index), symbols);
  }
}

void collectFormulaSymbols(Kernel::Formula* formula, std::set<KernelSymbol>& symbols)
{
  switch (formula->connective()) {
    case Kernel::LITERAL:
      collectLiteralSymbols(formula->literal(), symbols);
      return;
    case Kernel::AND:
    case Kernel::OR: {
      Kernel::FormulaList::Iterator iterator(formula->args());
      while (iterator.hasNext()) {
        collectFormulaSymbols(iterator.next(), symbols);
      }
      return;
    }
    case Kernel::IMP:
    case Kernel::IFF:
    case Kernel::XOR:
      collectFormulaSymbols(formula->left(), symbols);
      collectFormulaSymbols(formula->right(), symbols);
      return;
    case Kernel::NOT:
      collectFormulaSymbols(formula->uarg(), symbols);
      return;
    case Kernel::FORALL:
    case Kernel::EXISTS:
      collectFormulaSymbols(formula->qarg(), symbols);
      return;
    case Kernel::BOOL_TERM:
      collectTermSymbols(formula->getBooleanTerm(), symbols);
      return;
    case Kernel::TRUE:
    case Kernel::FALSE:
    case Kernel::NAME:
      return;
    default:
      return;
  }
}

}

std::vector<MegalodonKernelSyntax::RenderedKernelSkolemBranchScopeSymbol>
sourceSignatureScope(
  Kernel::Formula* formula,
  const std::function<std::string(unsigned)>& functionName,
  const std::function<std::string(unsigned)>& predicateName)
{
  std::set<KernelSymbol> symbols;
  collectFormulaSymbols(formula, symbols);
  std::map<std::string, std::string> scopedNames;
  for (const KernelSymbol& symbol : symbols) {
    const std::string name = symbol.first
      ? functionName(symbol.second)
      : predicateName(symbol.second);
    if (!name.empty()) {
      const Kernel::Signature::Symbol* signatureSymbol = symbol.first
        ? env.signature->getFunction(symbol.second)
        : env.signature->getPredicate(symbol.second);
      const std::string role = signatureSymbol->introduced()
        ? "source_vampire_introduced"
        : "source_input_signature";
      auto existing = scopedNames.find(name);
      if (existing == scopedNames.end() || role == "source_input_signature") {
        scopedNames[name] = role;
      }
    }
  }
  std::vector<MegalodonKernelSyntax::RenderedKernelSkolemBranchScopeSymbol> result;
  for (const auto& entry : scopedNames) {
    result.push_back({result.size(), entry.first, entry.second});
  }
  return result;
}

}
}
