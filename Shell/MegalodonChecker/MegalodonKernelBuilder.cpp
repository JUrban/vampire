#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Environment.hpp"

#include <map>
#include <set>
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

MegalodonKernelSyntax::PrimitiveStep avatarRefutationStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& parents,
  const std::vector<MegalodonKernelSyntax::RenderedKernelClause>& satClauses,
  const std::string& satProof,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  for (const auto& parent : parents) {
    parentIds.push_back(parent.value);
    renderedParents += " " + quote(parent.value);
  }
  renderedParents += ")";
  std::string renderedSatClauses = "(sat_clauses";
  for (const auto& clause : satClauses) {
    renderedSatClauses += " " + clause.sexpr;
  }
  renderedSatClauses += ")";
  return primitiveClauseStep(
    "avatar_refutation",
    id,
    parentIds,
    result.sexpr,
    {
      {"sat_input_count", std::to_string(satClauses.size())},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_refutation " + quote(id) + " " + renderedParents
      + " " + renderedSatClauses
      + (satProof.empty() ? "" : " " + satProof)
      + " (result " + result.sexpr + "))");
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
