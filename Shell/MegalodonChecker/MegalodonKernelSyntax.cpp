#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"

#include <cstddef>
#include <utility>

namespace Shell {
namespace MegalodonKernelSyntax {

const std::string& schema()
{
  static const std::string value = "prover9-small-kernel-v1";
  return value;
}

std::vector<std::string> requiredPrimitivesForRule(const std::string& rule)
{
  static const std::vector<std::pair<std::string, std::vector<std::string>>> contracts = {
    {"fool_formula", {"fool_atom_lift"}},
    {"rectify_formula", {"rectify_formula"}},
    {"formula_normalize", {"ennf_formula"}},
    {"skolemize", {"skolem_formula"}},
    {"cnf_clause", {"cnf_literal", "cnf_formula_clause"}},
    {"formula_copy", {"formula_copy", "formula_term_copy"}},
    {"fool_exhaustiveness", {"fool_exhaustiveness"}},
    {"truth_conflict", {"truth_conflict"}},
    {"equality_resolution", {"equality_resolution", "equality_resolution_constraints"}},
    {"equality_factoring", {"equality_factoring", "equality_factoring_constraints"}},
    {"avatar_component", {"avatar_component"}},
    {"avatar_split", {"avatar_split"}},
    {"avatar_refutation", {"avatar_refutation"}},
    {"avatar_definition", {"avatar_definition"}},
    {"split_dependency", {"split_dependency"}},
    {"superposition", {"paramodulate"}},
    {"rewrite", {"paramodulate"}},
    {"subsumption_resolution", {"resolve"}},
    {"unit_resulting_resolution", {"resolve"}},
    {"resolution", {"resolve"}},
    {"factoring", {"factor"}},
    {"instantiation", {"substitute"}},
  };

  for (const auto& contract : contracts) {
    if (contract.first == rule) {
      return contract.second;
    }
  }
  return {};
}

RenderedKernelUnitRef unitRef(const std::string& value)
{
  return {value};
}

RenderedKernelTerm term(const std::string& sexpr)
{
  return {sexpr};
}

RenderedKernelFormula formula(const std::string& sexpr)
{
  return {sexpr};
}

RenderedKernelLiteral literal(const std::string& sexpr)
{
  return {sexpr};
}

RenderedKernelClause clause(const std::string& sexpr)
{
  return {sexpr};
}

RenderedKernelSubstitution substitution(const std::string& sexpr)
{
  return {sexpr};
}

RenderedKernelPosition position(const std::string& sexpr)
{
  return {sexpr};
}

RenderedKernelType type(const std::string& sexpr)
{
  return {sexpr};
}

std::vector<RenderedKernelLiteral> literals(const std::vector<std::string>& sexprs)
{
  std::vector<RenderedKernelLiteral> rendered;
  rendered.reserve(sexprs.size());
  for (const std::string& sexpr : sexprs) {
    rendered.push_back(literal(sexpr));
  }
  return rendered;
}

MigrationField migrationField(const std::string& rendered)
{
  return {rendered};
}

RenderedKernelPrimitiveParentSubstitution primitiveParentSubstitution(
  std::size_t parentIndex,
  const RenderedKernelSubstitution& substitution)
{
  return {parentIndex, substitution};
}

PrimitiveExpansion primitiveExpansion(
  const std::string& prefix,
  const std::string& primitiveRule)
{
  return {prefix, primitiveRule};
}

void appendPrimitiveExpansion(
  std::vector<std::string>& fields,
  const PrimitiveExpansion& expansion)
{
  fields.push_back("primitive_expansion=prefix");
  fields.push_back("primitive_expansion_prefix=" + expansion.prefix);
  fields.push_back("primitive_expansion_requires=" + expansion.requiredRule);
}

MegalodonKernelStep kernelStep(
  const std::string& id,
  const std::string& rule)
{
  MegalodonKernelStep step;
  step.id = id;
  step.rule = rule;
  return step;
}

void addField(
  MegalodonKernelStep& step,
  const std::string& field)
{
  step.migrationFields.push_back(migrationField(field));
}

void addFields(
  MegalodonKernelStep& step,
  const std::vector<std::string>& fields)
{
  for (const std::string& field : fields) {
    addField(step, field);
  }
}

void addPrimitiveExpansion(
  MegalodonKernelStep& step,
  const PrimitiveExpansion& expansion)
{
  step.primitiveExpansions.push_back(expansion);
}

void addPrimitiveParentSubstitution(
  MegalodonKernelStep& step,
  const RenderedKernelPrimitiveParentSubstitution& substitution)
{
  step.primitiveParentSubstitutions.push_back(substitution);
}

void setSubsumptionResolutionPivot(
  MegalodonKernelStep& step,
  const RenderedKernelSubsumptionResolutionPivot& pivot)
{
  step.hasSubsumptionResolutionPivot = true;
  step.subsumptionResolutionPivot = pivot;
}

void addSkolemIntroducedSymbol(
  MegalodonKernelStep& step,
  const RenderedKernelSkolemIntroducedSymbol& introduced)
{
  step.skolemIntroducedSymbols.push_back(introduced);
}

void setConclusion(
  MegalodonKernelStep& step,
  const RenderedKernelConclusion& conclusion)
{
  step.hasConclusion = true;
  step.conclusion = conclusion;
}

void addParent(
  MegalodonKernelStep& step,
  const RenderedKernelParent& parent)
{
  step.hasParents = true;
  step.parents.push_back(parent);
}

void setParentList(
  MegalodonKernelStep& step)
{
  step.hasParents = true;
}

void appendLiteralSelection(
  std::vector<std::string>& fields,
  const RenderedKernelLiteralSelection& selection)
{
  if (selection.hasLiteral) {
    fields.push_back(selection.prefix + "=" + selection.literal.sexpr);
  }
  if (!selection.hasParent) {
    return;
  }
  fields.push_back(selection.prefix + "_parent_index=" + std::to_string(selection.parentIndex));
  fields.push_back(selection.prefix + "_literal_index=" + std::to_string(selection.literalIndex));
  fields.push_back(selection.prefix + "_parent_unit=" + selection.parentUnit.value);
  if (selection.hasSubstituted) {
    fields.push_back(selection.prefix + "_substituted=" + selection.substituted.sexpr);
  }
}

void appendRewrite(
  std::vector<std::string>& fields,
  const RenderedKernelRewrite& rewrite)
{
  if (rewrite.hasTargetSubstituted) {
    fields.push_back("target_substituted=" + rewrite.targetSubstituted.sexpr);
  }
  if (rewrite.hasEqualitySubstituted) {
    fields.push_back("equality_substituted=" + rewrite.equalitySubstituted.sexpr);
  }
  if (rewrite.hasTargetLocation) {
    fields.push_back("target_parent_index=" + std::to_string(rewrite.targetParentIndex));
    fields.push_back("target_literal_index=" + std::to_string(rewrite.targetLiteralIndex));
  }
  if (rewrite.hasEqualityLocation) {
    fields.push_back("equality_parent_index=" + std::to_string(rewrite.equalityParentIndex));
    fields.push_back("equality_literal_index=" + std::to_string(rewrite.equalityLiteralIndex));
  }
  if (rewrite.hasDirection) {
    fields.push_back("rewrite_direction=" + rewrite.direction);
  }
  if (rewrite.hasPosition) {
    fields.push_back("rewrite_position=" + rewrite.position.sexpr);
  }
  if (rewrite.hasFrom) {
    fields.push_back("from=" + rewrite.from.sexpr);
  }
  if (rewrite.hasTo) {
    fields.push_back("to=" + rewrite.to.sexpr);
  }
  if (rewrite.hasRewrittenTarget) {
    fields.push_back("rewritten_target=" + rewrite.rewrittenTarget.sexpr);
  }
}

void appendUrrTraceStep(
  std::vector<std::string>& fields,
  const RenderedKernelUrrTraceStep& step)
{
  const std::string prefix = "trace_step_" + std::to_string(step.index);
  if (step.hasUnitParent) {
    fields.push_back(prefix + "_unit_parent=" + step.unitParent.value);
  }
  if (step.hasUnitParentClause) {
    fields.push_back(prefix + "_unit_parent_clause=" + step.unitParentClause.sexpr);
  }
  if (step.hasSelected) {
    fields.push_back(prefix + "_selected=" + step.selected.sexpr);
  }
  if (step.hasSelectedSubstituted) {
    fields.push_back(prefix + "_selected_substituted=" + step.selectedSubstituted.sexpr);
  }
  if (step.hasUnitSubstituted) {
    fields.push_back(prefix + "_unit_substituted=" + step.unitSubstituted.sexpr);
  }
  if (step.hasRemainingAfter) {
    fields.push_back(prefix + "_remaining_after=" + step.remainingAfter.sexpr);
  }
}

namespace {

bool hasFieldWithPrefix(
  const std::vector<std::string>& fields,
  const std::string& prefix)
{
  for (const std::string& field : fields) {
    if (field.rfind(prefix, 0) == 0) {
      return true;
    }
  }
  return false;
}

void appendConclusionFields(
  std::vector<std::string>& fields,
  const RenderedKernelConclusion& conclusion)
{
  fields.push_back("conclusion_unit=" + conclusion.unit.value);
  fields.push_back("vampire_rule=" + conclusion.vampireRule);
  if (conclusion.hasClause) {
    fields.push_back("conclusion_clause=" + conclusion.clause.sexpr);
    if (!hasFieldWithPrefix(fields, "result_clause=")) {
      fields.push_back("result_clause=" + conclusion.clause.sexpr);
    }
    if (conclusion.hasResultLiterals) {
      fields.push_back("result_literal_count=" + std::to_string(conclusion.resultLiterals.size()));
      for (std::size_t literalIndex = 0; literalIndex < conclusion.resultLiterals.size(); ++literalIndex) {
        fields.push_back(
          "result_literal_" + std::to_string(literalIndex) + "="
          + conclusion.resultLiterals[literalIndex].sexpr);
      }
    }
    return;
  }
  if (conclusion.hasFormula) {
    fields.push_back("conclusion_formula=" + conclusion.formula.sexpr);
    if (!hasFieldWithPrefix(fields, "result_formula=")) {
      fields.push_back("result_formula=" + conclusion.formula.sexpr);
    }
  }
}

void appendParentFields(
  std::vector<std::string>& fields,
  const std::vector<RenderedKernelParent>& parents)
{
  fields.push_back("parent_count=" + std::to_string(parents.size()));
  for (std::size_t parentIndex = 0; parentIndex < parents.size(); ++parentIndex) {
    const RenderedKernelParent& parent = parents[parentIndex];
    const std::string prefix = "parent_" + std::to_string(parentIndex);
    fields.push_back(prefix + "_unit=" + parent.unit.value);
    if (parent.hasClause) {
      fields.push_back(prefix + "_clause=" + parent.clause.sexpr);
    }
    if (parent.hasLiterals) {
      fields.push_back(prefix + "_literal_count=" + std::to_string(parent.literals.size()));
      for (std::size_t literalIndex = 0; literalIndex < parent.literals.size(); ++literalIndex) {
        fields.push_back(
          prefix + "_literal_" + std::to_string(literalIndex) + "=" + parent.literals[literalIndex].sexpr);
      }
    }
    if (parent.hasSubstitution) {
      fields.push_back(prefix + "_substitution=" + parent.substitution.sexpr);
    }
    if (parent.hasSubstitutedLiterals) {
      fields.push_back(
        prefix + "_substituted_literal_count=" + std::to_string(parent.substitutedLiterals.size()));
      for (std::size_t literalIndex = 0; literalIndex < parent.substitutedLiterals.size(); ++literalIndex) {
        fields.push_back(
          prefix + "_substituted_literal_" + std::to_string(literalIndex)
          + "=" + parent.substitutedLiterals[literalIndex].sexpr);
      }
    }
  }
}

void appendPrimitiveParentSubstitutionFields(
  std::vector<std::string>& fields,
  const std::vector<RenderedKernelPrimitiveParentSubstitution>& substitutions)
{
  for (const RenderedKernelPrimitiveParentSubstitution& substitution : substitutions) {
    fields.push_back(
      "primitive_parent_" + std::to_string(substitution.parentIndex)
      + "_substitution=" + substitution.substitution.sexpr);
  }
}

void appendSubsumptionResolutionPivotFields(
  std::vector<std::string>& fields,
  const RenderedKernelSubsumptionResolutionPivot& pivot)
{
  fields.push_back("main_parent_index=" + std::to_string(pivot.mainParentIndex));
  fields.push_back("side_parent_index=" + std::to_string(pivot.sideParentIndex));
  if (pivot.hasSideSubstitution) {
    fields.push_back("side_substitution=" + pivot.sideSubstitution.sexpr);
  }
  if (pivot.hasSidePivot) {
    fields.push_back("side_pivot=" + pivot.sidePivot.sexpr);
  }
  if (pivot.hasSidePivotLocation) {
    fields.push_back("side_pivot_parent_index=" + std::to_string(pivot.sidePivotParentIndex));
    fields.push_back("side_pivot_literal_index=" + std::to_string(pivot.sidePivotLiteralIndex));
    fields.push_back("side_pivot_parent_unit=" + pivot.sidePivotParentUnit.value);
  }
  if (pivot.hasSidePivotSubstituted) {
    fields.push_back("side_pivot_substituted=" + pivot.sidePivotSubstituted.sexpr);
  }
  if (pivot.sidePivotMatchesBySymmetry) {
    fields.push_back("side_pivot_matches_by_symmetry=1");
  }
}

void appendSkolemDependencyFields(
  std::vector<std::string>& fields,
  const std::string& prefix,
  const RenderedKernelSkolemDependency& dependency)
{
  if (dependency.hasTerm) {
    fields.push_back(prefix + "_term=" + dependency.term.sexpr);
  }
  if (dependency.hasVariable) {
    fields.push_back(prefix + "_var=" + dependency.variable);
  }
  if (dependency.hasSort) {
    fields.push_back(prefix + "_sort=" + dependency.sort);
  }
  if (dependency.hasSortSexpr) {
    fields.push_back(prefix + "_sort_sexpr=" + dependency.sortSexpr.sexpr);
  }
}

void appendSkolemIntroducedSymbolFields(
  std::vector<std::string>& fields,
  const std::vector<RenderedKernelSkolemIntroducedSymbol>& introducedSymbols)
{
  if (introducedSymbols.empty()) {
    return;
  }
  fields.push_back("introduced_count=" + std::to_string(introducedSymbols.size()));
  for (const RenderedKernelSkolemIntroducedSymbol& introduced : introducedSymbols) {
    const std::string prefix = "introduced_" + std::to_string(introduced.index);
    if (introduced.hasKind) {
      fields.push_back(prefix + "_kind=" + introduced.kind);
    }
    if (introduced.hasRawSymbol) {
      fields.push_back(prefix + "_raw_symbol=" + introduced.rawSymbol);
    }
    if (introduced.hasReplacedVariable) {
      fields.push_back(prefix + "_replaced_var=" + introduced.replacedVariable);
    }
    if (introduced.hasSymbol) {
      fields.push_back(prefix + "_symbol=" + introduced.symbol);
    }
    if (introduced.hasDeclaration) {
      fields.push_back(prefix + "_declaration=" + introduced.declaration);
    }
    if (introduced.hasReplacedVariableSort) {
      fields.push_back(prefix + "_replaced_var_sort=" + introduced.replacedVariableSort);
    }
    if (introduced.hasReplacedVariableSortSexpr) {
      fields.push_back(prefix + "_replaced_var_sort_sexpr=" + introduced.replacedVariableSortSexpr.sexpr);
    }
    if (introduced.hasWitnessTerm) {
      fields.push_back(prefix + "_witness_term=" + introduced.witnessTerm.sexpr);
    }
    if (introduced.hasWitnessSort) {
      fields.push_back(prefix + "_witness_sort=" + introduced.witnessSort);
    }
    if (introduced.hasWitnessSortSexpr) {
      fields.push_back(prefix + "_witness_sort_sexpr=" + introduced.witnessSortSexpr.sexpr);
    }
    if (introduced.hasSourceVariableApplicationCount) {
      fields.push_back(
        prefix + "_source_variable_application_count="
        + std::to_string(introduced.sourceVariableApplicationCount));
    }
    if (!introduced.dependencies.empty()) {
      fields.push_back(prefix + "_dependency_count=" + std::to_string(introduced.dependencies.size()));
      for (std::size_t dependencyIndex = 0;
           dependencyIndex < introduced.dependencies.size();
           ++dependencyIndex) {
        appendSkolemDependencyFields(
          fields,
          prefix + "_dependency_" + std::to_string(dependencyIndex),
          introduced.dependencies[dependencyIndex]);
      }
    }
    if (introduced.hasChoicePrinciple) {
      fields.push_back(prefix + "_choice_principle=" + introduced.choicePrinciple);
    }
  }
}

}

std::vector<std::string> kernelStepFields(const MegalodonKernelStep& step)
{
  std::vector<std::string> fields;
  fields.push_back("schema=" + schema());
  fields.push_back("rule=" + step.rule);
  for (const PrimitiveExpansion& expansion : step.primitiveExpansions) {
    appendPrimitiveExpansion(fields, expansion);
  }
  for (const MigrationField& field : step.migrationFields) {
    fields.push_back(field.rendered);
  }
  appendPrimitiveParentSubstitutionFields(fields, step.primitiveParentSubstitutions);
  if (step.hasSubsumptionResolutionPivot) {
    appendSubsumptionResolutionPivotFields(fields, step.subsumptionResolutionPivot);
  }
  appendSkolemIntroducedSymbolFields(fields, step.skolemIntroducedSymbols);
  if (step.hasConclusion) {
    appendConclusionFields(fields, step.conclusion);
  }
  if (step.hasParents) {
    appendParentFields(fields, step.parents);
  }
  return fields;
}

bool appendFixedPrimitiveExpansionForRule(
  std::vector<std::string>& fields,
  const std::string& prefix,
  const std::string& rule)
{
  const auto required = requiredPrimitivesForRule(rule);
  if (required.size() != 1) {
    return false;
  }
  appendPrimitiveExpansion(fields, primitiveExpansion(prefix, required[0]));
  return true;
}

}
}
