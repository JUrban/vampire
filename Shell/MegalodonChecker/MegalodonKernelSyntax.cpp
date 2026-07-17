#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"

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
