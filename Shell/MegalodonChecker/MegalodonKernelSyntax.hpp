#ifndef __MEGALODON_KERNEL_SYNTAX__
#define __MEGALODON_KERNEL_SYNTAX__

#include <string>
#include <vector>

namespace Shell {
namespace MegalodonKernelSyntax {

struct PrimitiveExpansion {
  std::string prefix;
  std::string requiredRule;
};

struct RenderedKernelConclusion {
  std::string unit;
  std::string vampireRule;
  bool hasClause = false;
  std::string clause;
  bool hasFormula = false;
  std::string formula;
  bool hasResultLiterals = false;
  std::vector<std::string> resultLiterals;
};

struct RenderedKernelParent {
  std::string unit;
  bool hasClause = false;
  std::string clause;
  bool hasLiterals = false;
  std::vector<std::string> literals;
  bool hasSubstitution = false;
  std::string substitution;
  bool hasSubstitutedLiterals = false;
  std::vector<std::string> substitutedLiterals;
};

struct RenderedKernelLiteralSelection {
  std::string prefix;
  bool hasLiteral = false;
  std::string literal;
  bool hasParent = false;
  int parentIndex = -1;
  int literalIndex = -1;
  std::string parentUnit;
  bool hasSubstituted = false;
  std::string substituted;
};

struct RenderedKernelRewrite {
  bool hasTargetSubstituted = false;
  std::string targetSubstituted;
  bool hasEqualitySubstituted = false;
  std::string equalitySubstituted;
  bool hasTargetLocation = false;
  int targetParentIndex = -1;
  int targetLiteralIndex = -1;
  bool hasEqualityLocation = false;
  int equalityParentIndex = -1;
  int equalityLiteralIndex = -1;
  bool hasDirection = false;
  std::string direction;
  bool hasPosition = false;
  std::string position;
  bool hasFrom = false;
  std::string from;
  bool hasTo = false;
  std::string to;
  bool hasRewrittenTarget = false;
  std::string rewrittenTarget;
};

struct MegalodonKernelStep {
  std::string id;
  std::string rule;
  std::vector<PrimitiveExpansion> primitiveExpansions;
  std::vector<std::string> fields;
  bool hasConclusion = false;
  RenderedKernelConclusion conclusion;
  bool hasParents = false;
  std::vector<RenderedKernelParent> parents;
};

const std::string& schema();

std::vector<std::string> requiredPrimitivesForRule(const std::string& rule);

PrimitiveExpansion primitiveExpansion(
  const std::string& prefix,
  const std::string& primitiveRule);

void appendPrimitiveExpansion(
  std::vector<std::string>& fields,
  const PrimitiveExpansion& expansion);

MegalodonKernelStep kernelStep(
  const std::string& id,
  const std::string& rule);

void addField(
  MegalodonKernelStep& step,
  const std::string& field);

void addFields(
  MegalodonKernelStep& step,
  const std::vector<std::string>& fields);

void addPrimitiveExpansion(
  MegalodonKernelStep& step,
  const PrimitiveExpansion& expansion);

void setConclusion(
  MegalodonKernelStep& step,
  const RenderedKernelConclusion& conclusion);

void addParent(
  MegalodonKernelStep& step,
  const RenderedKernelParent& parent);

void setParentList(
  MegalodonKernelStep& step);

void appendLiteralSelection(
  std::vector<std::string>& fields,
  const RenderedKernelLiteralSelection& selection);

void appendRewrite(
  std::vector<std::string>& fields,
  const RenderedKernelRewrite& rewrite);

std::vector<std::string> kernelStepFields(const MegalodonKernelStep& step);

bool appendFixedPrimitiveExpansionForRule(
  std::vector<std::string>& fields,
  const std::string& prefix,
  const std::string& rule);

}
}

#endif
