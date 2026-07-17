#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"

#include <algorithm>
#include <cstddef>
#include <utility>

namespace Shell {
namespace MegalodonKernelSyntax {

const std::string& schema()
{
  static const std::string value = "prover9-small-kernel-v1";
  return value;
}

std::vector<std::string> structuralRules()
{
  return {
    "predicate_definition",
    "predicate_definition_fold",
    "predicate_definition_fold_chain",
  };
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

std::vector<std::string> supportedRules()
{
  std::vector<std::string> rules = structuralRules();
  static const std::vector<std::string> contractRules = {
    "fool_formula",
    "rectify_formula",
    "formula_normalize",
    "skolemize",
    "cnf_clause",
    "formula_copy",
    "fool_exhaustiveness",
    "truth_conflict",
    "equality_resolution",
    "equality_factoring",
    "avatar_component",
    "avatar_split",
    "avatar_refutation",
    "avatar_definition",
    "split_dependency",
    "superposition",
    "rewrite",
    "subsumption_resolution",
    "unit_resulting_resolution",
    "resolution",
    "factoring",
    "instantiation",
  };
  rules.insert(rules.end(), contractRules.begin(), contractRules.end());
  return rules;
}

bool isSupportedRule(const std::string& rule)
{
  const auto rules = supportedRules();
  for (const std::string& supported : rules) {
    if (supported == rule) {
      return true;
    }
  }
  return false;
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

bool appendPrimitiveExpansionChainFields(
  std::vector<std::string>& fields,
  const std::string& expansion,
  const std::string& finalRule)
{
  std::vector<std::pair<std::string, std::string>> primitiveSteps;
  std::vector<std::string> requiredRules;
  unsigned depth = 0;
  for (std::size_t pos = 0; pos < expansion.size(); ++pos) {
    if (expansion[pos] == '(') {
      if (depth == 0) {
        std::size_t cursor = pos + 1;
        while (cursor < expansion.size() && expansion[cursor] == ' ') {
          ++cursor;
        }
        std::size_t ruleStart = cursor;
        while (cursor < expansion.size()
          && expansion[cursor] != ' '
          && expansion[cursor] != '\n'
          && expansion[cursor] != '\t'
          && expansion[cursor] != ')') {
          ++cursor;
        }
        if (ruleStart != cursor) {
          std::string rule = expansion.substr(ruleStart, cursor - ruleStart);
          if (rule != finalRule
            && rule != "step_variable_sorts"
            && rule != "step_extra") {
            std::size_t quoteStart = expansion.find('"', cursor);
            if (quoteStart != std::string::npos) {
              std::size_t quoteEnd = expansion.find('"', quoteStart + 1);
              if (quoteEnd != std::string::npos) {
                std::string id =
                  expansion.substr(quoteStart + 1, quoteEnd - quoteStart - 1);
                primitiveSteps.push_back({rule, id});
                if (std::find(requiredRules.begin(), requiredRules.end(), rule)
                  == requiredRules.end()) {
                  requiredRules.push_back(rule);
                }
              }
            }
          }
        }
      }
      ++depth;
      continue;
    }
    if (expansion[pos] == ')' && depth > 0) {
      --depth;
    }
  }
  if (primitiveSteps.empty()) {
    return false;
  }
  fields.push_back("primitive_expansion_step_count=" + std::to_string(primitiveSteps.size()));
  for (std::size_t i = 0; i < primitiveSteps.size(); ++i) {
    fields.push_back(
      "primitive_expansion_step_" + std::to_string(i) + "_rule=" + primitiveSteps[i].first);
    fields.push_back(
      "primitive_expansion_step_" + std::to_string(i) + "_id=" + primitiveSteps[i].second);
  }
  fields.push_back("primitive_expansion_requires_count=" + std::to_string(requiredRules.size()));
  for (std::size_t i = 0; i < requiredRules.size(); ++i) {
    fields.push_back(
      "primitive_expansion_requires_" + std::to_string(i) + "=" + requiredRules[i]);
  }
  return true;
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

void setSourceFormulaTransform(
  MegalodonKernelStep& step,
  const RenderedKernelSourceFormulaTransform& transform)
{
  step.hasSourceFormulaTransform = true;
  step.sourceFormulaTransform = transform;
}

void setRectifyRenamings(
  MegalodonKernelStep& step,
  const RenderedKernelRectifyRenamings& renamings)
{
  step.hasRectifyRenamings = true;
  step.rectifyRenamings = renamings;
}

void setCnfClause(
  MegalodonKernelStep& step,
  const RenderedKernelCnfClause& cnfClause)
{
  step.hasCnfClause = true;
  step.cnfClause = cnfClause;
}

void setDefinitionFold(
  MegalodonKernelStep& step,
  const RenderedKernelDefinitionFold& definitionFold)
{
  step.hasDefinitionFold = true;
  step.definitionFold = definitionFold;
}

void setUrrTrace(
  MegalodonKernelStep& step,
  const RenderedKernelUrrTrace& urrTrace)
{
  step.hasUrrTrace = true;
  step.urrTrace = urrTrace;
}

void setAvatarComponent(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarComponent& avatarComponent)
{
  step.hasAvatarComponent = true;
  step.avatarComponent = avatarComponent;
}

void setAvatarDefinition(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarDefinition& avatarDefinition)
{
  step.hasAvatarDefinition = true;
  step.avatarDefinition = avatarDefinition;
}

void setSplitDependency(
  MegalodonKernelStep& step,
  const RenderedKernelSplitDependency& splitDependency)
{
  step.hasSplitDependency = true;
  step.splitDependency = splitDependency;
}

void setAvatarSplit(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarSplitStep& avatarSplit)
{
  step.hasAvatarSplit = true;
  step.avatarSplit = avatarSplit;
}

void setAvatarRefutation(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarRefutation& avatarRefutation)
{
  step.hasAvatarRefutation = true;
  step.avatarRefutation = avatarRefutation;
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

void appendSourceFormulaTransformFields(
  std::vector<std::string>& fields,
  const RenderedKernelSourceFormulaTransform& transform)
{
  fields.push_back("source_unit=" + transform.sourceUnit.value);
  fields.push_back("parent_0_unit=" + transform.sourceUnit.value);
  fields.push_back("source_formula=" + transform.sourceFormula.sexpr);
  fields.push_back("parent_0_formula=" + transform.sourceFormula.sexpr);
  fields.push_back("proof_parent_count=" + std::to_string(transform.proofParentCount));
  fields.push_back("result_formula=" + transform.resultFormula.sexpr);
  if (transform.hasCopyKind) {
    fields.push_back("copy_kind=" + transform.copyKind);
  }
  if (transform.hasNormalFormRule) {
    fields.push_back("normal_form_rule=" + transform.normalFormRule);
  }
  if (!transform.transformationPairs.empty()) {
    fields.push_back("transformation_pair_count=" + std::to_string(transform.transformationPairs.size()));
    for (const RenderedKernelTransformationPair& pair : transform.transformationPairs) {
      const std::string prefix = "pair_" + std::to_string(pair.index);
      fields.push_back(prefix + "_source=" + pair.source.sexpr);
      fields.push_back(prefix + "_target=" + pair.target.sexpr);
      if (pair.hasPath) {
        fields.push_back(prefix + "_path=" + pair.path);
      }
      if (pair.hasKind) {
        fields.push_back(prefix + "_kind=" + pair.kind);
      }
    }
  }
}

void appendRectifyRenamingFields(
  std::vector<std::string>& fields,
  const RenderedKernelRectifyRenamings& renamings)
{
  fields.push_back("renaming_count=" + std::to_string(renamings.reportedCount));
  for (const RenderedKernelRectifyRenaming& renaming : renamings.renamings) {
    const std::string prefix = "renaming_" + std::to_string(renaming.index);
    if (renaming.hasSource) {
      fields.push_back(prefix + "_source=" + renaming.source.sexpr);
    }
    if (renaming.hasTarget) {
      fields.push_back(prefix + "_target=" + renaming.target.sexpr);
    }
    if (renaming.hasSubstitution) {
      fields.push_back(prefix + "_substitution=" + renaming.substitution.sexpr);
    }
  }
  if (renamings.truncated) {
    fields.push_back("renaming_truncated=1");
  }
}

void appendCnfClauseFields(
  std::vector<std::string>& fields,
  const RenderedKernelCnfClause& cnfClause)
{
  fields.push_back("source_unit=" + cnfClause.sourceUnit.value);
  fields.push_back("parent_0_unit=" + cnfClause.sourceUnit.value);
  fields.push_back("proof_parent_count=" + std::to_string(cnfClause.proofParentCount));
  fields.push_back("source_kind=" + cnfClause.sourceKind);
  if (cnfClause.hasSourceClause) {
    fields.push_back("source_clause=" + cnfClause.sourceClause.sexpr);
    fields.push_back("parent_0_clause=" + cnfClause.sourceClause.sexpr);
  }
  if (cnfClause.hasSourceFormula) {
    fields.push_back("source_formula=" + cnfClause.sourceFormula.sexpr);
    fields.push_back("parent_0_formula=" + cnfClause.sourceFormula.sexpr);
  }
  if (cnfClause.hasResultClause) {
    fields.push_back("result_clause=" + cnfClause.resultClause.sexpr);
  }
  if (cnfClause.hasParentClauseCount) {
    fields.push_back("parent_clause_count=" + std::to_string(cnfClause.parentClauseCount));
  }
  if (cnfClause.hasClauseParentUnit) {
    fields.push_back("clause_parent_unit=" + cnfClause.clauseParentUnit.value);
  }
  if (cnfClause.hasClauseIndex) {
    fields.push_back("clause_index=" + std::to_string(cnfClause.clauseIndex));
  }
  if (cnfClause.hasClauseCount) {
    fields.push_back("clause_count=" + std::to_string(cnfClause.clauseCount));
  }
}

void appendDefinitionFoldFields(
  std::vector<std::string>& fields,
  const RenderedKernelDefinitionFold& definitionFold)
{
  fields.push_back("source_unit=" + definitionFold.sourceUnit.value);
  if (definitionFold.hasSourceFormula) {
    fields.push_back("source_formula=" + definitionFold.sourceFormula.sexpr);
  }
  fields.push_back("definition_count=" + std::to_string(definitionFold.definitions.size()));
  for (const RenderedKernelDefinitionParent& definition : definitionFold.definitions) {
    const std::string prefix = "definition_" + std::to_string(definition.index);
    fields.push_back(prefix + "_unit=" + definition.unit.value);
    if (definition.hasFormula) {
      fields.push_back(prefix + "_formula=" + definition.formula.sexpr);
    }
    if (definition.hasSymbol) {
      fields.push_back(prefix + "_symbol=" + definition.symbol);
    }
  }
  if (definitionFold.hasResultFormula) {
    fields.push_back("result_formula=" + definitionFold.resultFormula.sexpr);
  }
}

void appendUrrTraceFields(
  std::vector<std::string>& fields,
  const RenderedKernelUrrTrace& trace)
{
  if (trace.hasMainParent) {
    fields.push_back("trace_main_parent_unit=" + trace.mainParent.value);
  }
  fields.push_back("trace_step_count=" + std::to_string(trace.steps.size()));
  for (const RenderedKernelUrrTraceStep& step : trace.steps) {
    appendUrrTraceStep(fields, step);
  }
  if (trace.hasRemaining) {
    fields.push_back("trace_remaining=" + trace.remaining.sexpr);
  }
}

void appendAvatarComponentFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarComponent& component)
{
  if (component.hasResultClause) {
    fields.push_back("result_clause=" + component.resultClause.sexpr);
  }
  fields.push_back("literal_count=" + std::to_string(component.literalCount));
  for (std::size_t literalIndex = 0; literalIndex < component.literals.size(); ++literalIndex) {
    fields.push_back(
      "literal_" + std::to_string(literalIndex) + "=" + component.literals[literalIndex].sexpr);
  }
  fields.push_back("split_count=" + std::to_string(component.splitCount));
  for (const RenderedKernelAvatarSplit& split : component.splits) {
    const std::string prefix = "split_" + std::to_string(split.index);
    fields.push_back(prefix + "_level=" + std::to_string(split.level));
    fields.push_back(prefix + "_var=" + std::to_string(split.variable));
    fields.push_back(prefix + "_positive=" + std::string(split.positive ? "1" : "0"));
  }
}

void appendAvatarDefinitionFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarDefinition& definition)
{
  fields.push_back("component_split_level=" + std::to_string(definition.componentSplit.level));
  fields.push_back("component_split_var=" + std::to_string(definition.componentSplit.variable));
  fields.push_back(
    "component_split_positive="
    + std::string(definition.componentSplit.positive ? "1" : "0"));
  if (definition.hasComponentClause) {
    fields.push_back("component_clause=" + definition.componentClause);
  }
  if (definition.hasComponentClauseSexpr) {
    fields.push_back("component_clause_sexpr=" + definition.componentClauseSexpr.sexpr);
  }
  fields.push_back(
    "component_clause_variable_sort_count="
    + std::to_string(definition.componentClauseVariableSorts.size()));
  for (std::size_t sortIndex = 0; sortIndex < definition.componentClauseVariableSorts.size(); ++sortIndex) {
    fields.push_back(
      "component_clause_variable_sort_" + std::to_string(sortIndex) + "="
      + definition.componentClauseVariableSorts[sortIndex]);
  }
  fields.push_back(
    "component_clause_db_sort_count="
    + std::to_string(definition.componentClauseDbSorts.size()));
  for (std::size_t sortIndex = 0; sortIndex < definition.componentClauseDbSorts.size(); ++sortIndex) {
    fields.push_back(
      "component_clause_db_sort_" + std::to_string(sortIndex) + "="
      + definition.componentClauseDbSorts[sortIndex]);
  }
  if (definition.hasResultClause) {
    fields.push_back("result_clause=" + definition.resultClause.sexpr);
  }
}

void appendSplitDependencyItemFields(
  std::vector<std::string>& fields,
  const RenderedKernelSplitDependencyItem& dependency)
{
  const std::string prefix = "dependency_" + std::to_string(dependency.index);
  fields.push_back(prefix + "_split_level=" + std::to_string(dependency.split.level));
  fields.push_back(prefix + "_split_var=" + std::to_string(dependency.split.variable));
  fields.push_back(
    prefix + "_split_positive="
    + std::string(dependency.split.positive ? "1" : "0"));
  if (dependency.hasComponentClause) {
    fields.push_back(prefix + "_component_clause=" + dependency.componentClause);
  }
  if (dependency.hasComponentClauseSexpr) {
    fields.push_back(
      prefix + "_component_clause_sexpr=" + dependency.componentClauseSexpr.sexpr);
  }
  fields.push_back(
    prefix + "_component_clause_variable_sort_count="
    + std::to_string(dependency.componentClauseVariableSorts.size()));
  for (std::size_t sortIndex = 0; sortIndex < dependency.componentClauseVariableSorts.size(); ++sortIndex) {
    fields.push_back(
      prefix + "_component_clause_variable_sort_" + std::to_string(sortIndex)
      + "=" + dependency.componentClauseVariableSorts[sortIndex]);
  }
  fields.push_back(
    prefix + "_component_clause_db_sort_count="
    + std::to_string(dependency.componentClauseDbSorts.size()));
  for (std::size_t sortIndex = 0; sortIndex < dependency.componentClauseDbSorts.size(); ++sortIndex) {
    fields.push_back(
      prefix + "_component_clause_db_sort_" + std::to_string(sortIndex)
      + "=" + dependency.componentClauseDbSorts[sortIndex]);
  }
  for (const MigrationField& field : dependency.componentClauseExtraFields) {
    fields.push_back(field.rendered);
  }
}

void appendSplitDependencyFields(
  std::vector<std::string>& fields,
  const RenderedKernelSplitDependency& splitDependency)
{
  for (const RenderedKernelSplitDependencyItem& dependency : splitDependency.dependencies) {
    appendSplitDependencyItemFields(fields, dependency);
  }
  fields.push_back("dependency_count=" + std::to_string(splitDependency.dependencies.size()));
  if (splitDependency.hasResultClause) {
    fields.push_back("result_clause=" + splitDependency.resultClause.sexpr);
  }
}

void appendAvatarSatLiteralFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarSatLiteral& literal)
{
  const std::string prefix = "sat_literal_" + std::to_string(literal.index);
  fields.push_back(prefix + "_var=" + std::to_string(literal.variable));
  fields.push_back(prefix + "_positive=" + std::string(literal.positive ? "1" : "0"));
}

void appendAvatarComponentParentFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarComponentParent& parent)
{
  const std::string legacyPrefix = "component_parent_" + std::to_string(parent.parentIndex);
  fields.push_back(legacyPrefix + "_unit=" + parent.unit.value);
  fields.push_back(legacyPrefix + "_split_level=" + std::to_string(parent.split.level));
  fields.push_back(legacyPrefix + "_split_var=" + std::to_string(parent.split.variable));
  fields.push_back(
    legacyPrefix + "_split_positive=" + std::string(parent.split.positive ? "1" : "0"));
  if (parent.hasClause) {
    fields.push_back(legacyPrefix + "_clause=" + parent.clause);
  }

  const std::string refPrefix = "component_parent_ref_" + std::to_string(parent.refIndex);
  fields.push_back(refPrefix + "_unit=u" + parent.unit.value);
  fields.push_back(refPrefix + "_split_level=" + std::to_string(parent.split.level));
  fields.push_back(refPrefix + "_split_var=" + std::to_string(parent.split.variable));
  fields.push_back(
    refPrefix + "_split_positive=" + std::string(parent.split.positive ? "1" : "0"));
  if (parent.hasClauseSexpr) {
    fields.push_back(refPrefix + "_clause=" + parent.clauseSexpr.sexpr);
  }
}

void appendAvatarLiteralClassFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarLiteralClass& literalClass)
{
  const std::string prefix = "literal_class_" + std::to_string(literalClass.index);
  fields.push_back(prefix + "_literal_count=" + std::to_string(literalClass.literalCount));
  for (std::size_t literalIndex = 0; literalIndex < literalClass.literals.size(); ++literalIndex) {
    fields.push_back(
      prefix + "_literal_" + std::to_string(literalIndex) + "="
      + literalClass.literals[literalIndex]);
  }
  if (literalClass.hasMatchedSplitLevel) {
    fields.push_back(
      prefix + "_matched_split_level=" + std::to_string(literalClass.matchedSplitLevel));
  }
}

void appendAvatarParentVarBindingFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarParentVarBinding& binding)
{
  const std::string prefix = "parent_var_binding_" + std::to_string(binding.index);
  fields.push_back(prefix + "_parent_var=" + binding.parentVar);
  if (binding.hasComponentVar) {
    fields.push_back(prefix + "_component_var=" + binding.componentVar);
  }
  if (binding.hasSplitVar) {
    fields.push_back(prefix + "_split_var=" + std::to_string(binding.splitVar));
  }
}

void appendAvatarSplitFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarSplitStep& split)
{
  fields.push_back("source_unit=" + split.sourceUnit.value);
  if (split.hasSourceClause) {
    fields.push_back("source_clause=" + split.sourceClause.sexpr);
    fields.push_back("parent_0_clause=" + split.sourceClause.sexpr);
  }
  if (split.hasResultClause) {
    fields.push_back("result_clause=" + split.resultClause.sexpr);
  } else if (split.hasResultFormula) {
    fields.push_back("result_formula=" + split.resultFormula.sexpr);
  }

  fields.push_back("rule=" + split.vampireRule);
  if (split.hasSourceText) {
    fields.push_back("source=" + split.sourceText);
  }
  if (split.hasTargetText) {
    fields.push_back("target=" + split.targetText);
  }

  for (const RenderedKernelAvatarSplit& previous : split.previousSplits) {
    const std::string prefix = "previous_split_" + std::to_string(previous.index);
    fields.push_back(prefix + "_level=" + std::to_string(previous.level));
    fields.push_back(prefix + "_var=" + std::to_string(previous.variable));
    fields.push_back(prefix + "_positive=" + std::string(previous.positive ? "1" : "0"));
  }
  fields.push_back("previous_split_count=" + std::to_string(split.previousSplits.size()));

  for (const RenderedKernelAvatarSatLiteral& literal : split.satLiterals) {
    appendAvatarSatLiteralFields(fields, literal);
  }
  if (!split.satLiterals.empty()) {
    fields.push_back("sat_literal_count=" + std::to_string(split.satLiterals.size()));
  }

  for (const RenderedKernelAvatarComponentParent& parent : split.componentParents) {
    appendAvatarComponentParentFields(fields, parent);
  }
  fields.push_back("component_parent_count=" + std::to_string(split.componentParentCount));
  fields.push_back("component_parent_ref_count=" + std::to_string(split.componentParents.size()));

  for (const RenderedKernelAvatarLiteralClass& literalClass : split.literalClasses) {
    appendAvatarLiteralClassFields(fields, literalClass);
  }
  fields.push_back("literal_class_count=" + std::to_string(split.literalClasses.size()));

  for (const RenderedKernelAvatarParentVarBinding& binding : split.parentVarBindings) {
    appendAvatarParentVarBindingFields(fields, binding);
  }
  fields.push_back("parent_var_binding_count=" + std::to_string(split.parentVarBindings.size()));
}

void appendSatInputFields(
  std::vector<std::string>& fields,
  const RenderedKernelSatInput& input)
{
  const std::string prefix = "sat_input_" + std::to_string(input.index);
  if (input.hasClause) {
    fields.push_back(prefix + "_clause=" + input.clause.sexpr);
  }
  if (input.hasOriginUnit) {
    fields.push_back(prefix + "_origin_unit=" + input.originUnit.value);
  }
}

void appendSatProofParentFields(
  std::vector<std::string>& fields,
  const std::string& stepPrefix,
  const RenderedKernelSatProofParent& parent)
{
  const std::string prefix = stepPrefix + "_parent_" + std::to_string(parent.index);
  fields.push_back(prefix + "_id=" + std::to_string(parent.id));
  if (parent.hasClause) {
    fields.push_back(prefix + "_clause=" + parent.clause.sexpr);
  }
}

void appendSatProofStepFields(
  std::vector<std::string>& fields,
  const RenderedKernelSatProofStep& step)
{
  const std::string prefix = "sat_proof_step_" + std::to_string(step.index);
  fields.push_back(prefix + "_id=" + std::to_string(step.id));
  if (step.hasClause) {
    fields.push_back(prefix + "_clause=" + step.clause.sexpr);
  }
  fields.push_back(prefix + "_kind=" + step.kind);
  if (step.hasOriginUnit) {
    fields.push_back(prefix + "_origin_unit=" + step.originUnit.value);
  }
  for (const RenderedKernelSatProofParent& parent : step.parents) {
    appendSatProofParentFields(fields, prefix, parent);
  }
  if (step.kind == "rup" || !step.parents.empty()) {
    fields.push_back(prefix + "_parent_count=" + std::to_string(step.parents.size()));
  }
}

void appendAvatarRefutationFields(
  std::vector<std::string>& fields,
  const RenderedKernelAvatarRefutation& refutation)
{
  if (refutation.hasResultClause) {
    fields.push_back("result_clause=" + refutation.resultClause.sexpr);
  }
  if (refutation.hasSatRefutationClause) {
    fields.push_back("sat_refutation_clause=" + refutation.satRefutationClause.sexpr);
  }
  for (const RenderedKernelSatInput& input : refutation.inputs) {
    appendSatInputFields(fields, input);
  }
  fields.push_back("sat_input_count=" + std::to_string(refutation.inputs.size()));
  fields.push_back("sat_proof_step_count=" + std::to_string(refutation.proofSteps.size()));
  for (const RenderedKernelSatProofStep& step : refutation.proofSteps) {
    appendSatProofStepFields(fields, step);
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
  if (step.hasSourceFormulaTransform) {
    appendSourceFormulaTransformFields(fields, step.sourceFormulaTransform);
  }
  if (step.hasRectifyRenamings) {
    appendRectifyRenamingFields(fields, step.rectifyRenamings);
  }
  if (step.hasCnfClause) {
    appendCnfClauseFields(fields, step.cnfClause);
  }
  if (step.hasDefinitionFold) {
    appendDefinitionFoldFields(fields, step.definitionFold);
  }
  if (step.hasUrrTrace) {
    appendUrrTraceFields(fields, step.urrTrace);
  }
  if (step.hasAvatarComponent) {
    appendAvatarComponentFields(fields, step.avatarComponent);
  }
  if (step.hasAvatarDefinition) {
    appendAvatarDefinitionFields(fields, step.avatarDefinition);
  }
  if (step.hasSplitDependency) {
    appendSplitDependencyFields(fields, step.splitDependency);
  }
  if (step.hasAvatarSplit) {
    appendAvatarSplitFields(fields, step.avatarSplit);
  }
  if (step.hasAvatarRefutation) {
    appendAvatarRefutationFields(fields, step.avatarRefutation);
  }
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
