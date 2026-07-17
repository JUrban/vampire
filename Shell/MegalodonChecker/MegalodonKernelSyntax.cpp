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
  step.fields.push_back(field);
}

void addFields(
  MegalodonKernelStep& step,
  const std::vector<std::string>& fields)
{
  step.fields.insert(step.fields.end(), fields.begin(), fields.end());
}

void addPrimitiveExpansion(
  MegalodonKernelStep& step,
  const PrimitiveExpansion& expansion)
{
  step.primitiveExpansions.push_back(expansion);
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
    fields.push_back(selection.prefix + "=" + selection.literal);
  }
  if (!selection.hasParent) {
    return;
  }
  fields.push_back(selection.prefix + "_parent_index=" + std::to_string(selection.parentIndex));
  fields.push_back(selection.prefix + "_literal_index=" + std::to_string(selection.literalIndex));
  fields.push_back(selection.prefix + "_parent_unit=" + selection.parentUnit);
  if (selection.hasSubstituted) {
    fields.push_back(selection.prefix + "_substituted=" + selection.substituted);
  }
}

void appendRewrite(
  std::vector<std::string>& fields,
  const RenderedKernelRewrite& rewrite)
{
  if (rewrite.hasTargetSubstituted) {
    fields.push_back("target_substituted=" + rewrite.targetSubstituted);
  }
  if (rewrite.hasEqualitySubstituted) {
    fields.push_back("equality_substituted=" + rewrite.equalitySubstituted);
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
    fields.push_back("rewrite_position=" + rewrite.position);
  }
  if (rewrite.hasFrom) {
    fields.push_back("from=" + rewrite.from);
  }
  if (rewrite.hasTo) {
    fields.push_back("to=" + rewrite.to);
  }
  if (rewrite.hasRewrittenTarget) {
    fields.push_back("rewritten_target=" + rewrite.rewrittenTarget);
  }
}

void appendUrrTraceStep(
  std::vector<std::string>& fields,
  const RenderedKernelUrrTraceStep& step)
{
  const std::string prefix = "trace_step_" + std::to_string(step.index);
  if (step.hasUnitParent) {
    fields.push_back(prefix + "_unit_parent=" + step.unitParent);
  }
  if (step.hasUnitParentClause) {
    fields.push_back(prefix + "_unit_parent_clause=" + step.unitParentClause);
  }
  if (step.hasSelected) {
    fields.push_back(prefix + "_selected=" + step.selected);
  }
  if (step.hasSelectedSubstituted) {
    fields.push_back(prefix + "_selected_substituted=" + step.selectedSubstituted);
  }
  if (step.hasUnitSubstituted) {
    fields.push_back(prefix + "_unit_substituted=" + step.unitSubstituted);
  }
  if (step.hasRemainingAfter) {
    fields.push_back(prefix + "_remaining_after=" + step.remainingAfter);
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
  fields.push_back("conclusion_unit=" + conclusion.unit);
  fields.push_back("vampire_rule=" + conclusion.vampireRule);
  if (conclusion.hasClause) {
    fields.push_back("conclusion_clause=" + conclusion.clause);
    if (!hasFieldWithPrefix(fields, "result_clause=")) {
      fields.push_back("result_clause=" + conclusion.clause);
    }
    if (conclusion.hasResultLiterals) {
      fields.push_back("result_literal_count=" + std::to_string(conclusion.resultLiterals.size()));
      for (std::size_t literalIndex = 0; literalIndex < conclusion.resultLiterals.size(); ++literalIndex) {
        fields.push_back(
          "result_literal_" + std::to_string(literalIndex) + "=" + conclusion.resultLiterals[literalIndex]);
      }
    }
    return;
  }
  if (conclusion.hasFormula) {
    fields.push_back("conclusion_formula=" + conclusion.formula);
    if (!hasFieldWithPrefix(fields, "result_formula=")) {
      fields.push_back("result_formula=" + conclusion.formula);
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
    fields.push_back(prefix + "_unit=" + parent.unit);
    if (parent.hasClause) {
      fields.push_back(prefix + "_clause=" + parent.clause);
    }
    if (parent.hasLiterals) {
      fields.push_back(prefix + "_literal_count=" + std::to_string(parent.literals.size()));
      for (std::size_t literalIndex = 0; literalIndex < parent.literals.size(); ++literalIndex) {
        fields.push_back(
          prefix + "_literal_" + std::to_string(literalIndex) + "=" + parent.literals[literalIndex]);
      }
    }
    if (parent.hasSubstitution) {
      fields.push_back(prefix + "_substitution=" + parent.substitution);
    }
    if (parent.hasSubstitutedLiterals) {
      fields.push_back(
        prefix + "_substituted_literal_count=" + std::to_string(parent.substitutedLiterals.size()));
      for (std::size_t literalIndex = 0; literalIndex < parent.substitutedLiterals.size(); ++literalIndex) {
        fields.push_back(
          prefix + "_substituted_literal_" + std::to_string(literalIndex)
          + "=" + parent.substitutedLiterals[literalIndex]);
      }
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
  fields.insert(fields.end(), step.fields.begin(), step.fields.end());
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
