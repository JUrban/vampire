#ifndef __MEGALODON_KERNEL_SYNTAX__
#define __MEGALODON_KERNEL_SYNTAX__

#include <cstddef>
#include <string>
#include <vector>

namespace Shell {
namespace MegalodonKernelSyntax {

struct PrimitiveExpansion {
  std::string prefix;
  std::string requiredRule;
};

struct RenderedKernelUnitRef {
  std::string value;
};

struct RenderedKernelTerm {
  std::string sexpr;
};

struct RenderedKernelFormula {
  std::string sexpr;
};

struct RenderedKernelLiteral {
  std::string sexpr;
};

struct RenderedKernelClause {
  std::string sexpr;
};

struct RenderedKernelSubstitution {
  std::string sexpr;
};

struct RenderedKernelPosition {
  std::string sexpr;
};

struct MigrationField {
  std::string rendered;
};

struct RenderedKernelConclusion {
  RenderedKernelUnitRef unit;
  std::string vampireRule;
  bool hasClause = false;
  RenderedKernelClause clause;
  bool hasFormula = false;
  RenderedKernelFormula formula;
  bool hasResultLiterals = false;
  std::vector<RenderedKernelLiteral> resultLiterals;
};

struct RenderedKernelParent {
  RenderedKernelUnitRef unit;
  bool hasClause = false;
  RenderedKernelClause clause;
  bool hasLiterals = false;
  std::vector<RenderedKernelLiteral> literals;
  bool hasSubstitution = false;
  RenderedKernelSubstitution substitution;
  bool hasSubstitutedLiterals = false;
  std::vector<RenderedKernelLiteral> substitutedLiterals;
};

struct RenderedKernelLiteralSelection {
  std::string prefix;
  bool hasLiteral = false;
  RenderedKernelLiteral literal;
  bool hasParent = false;
  int parentIndex = -1;
  int literalIndex = -1;
  RenderedKernelUnitRef parentUnit;
  bool hasSubstituted = false;
  RenderedKernelLiteral substituted;
};

struct RenderedKernelRewrite {
  bool hasTargetSubstituted = false;
  RenderedKernelLiteral targetSubstituted;
  bool hasEqualitySubstituted = false;
  RenderedKernelLiteral equalitySubstituted;
  bool hasTargetLocation = false;
  int targetParentIndex = -1;
  int targetLiteralIndex = -1;
  bool hasEqualityLocation = false;
  int equalityParentIndex = -1;
  int equalityLiteralIndex = -1;
  bool hasDirection = false;
  std::string direction;
  bool hasPosition = false;
  RenderedKernelPosition position;
  bool hasFrom = false;
  RenderedKernelTerm from;
  bool hasTo = false;
  RenderedKernelTerm to;
  bool hasRewrittenTarget = false;
  RenderedKernelLiteral rewrittenTarget;
};

struct RenderedKernelUrrTraceStep {
  std::size_t index = 0;
  bool hasUnitParent = false;
  RenderedKernelUnitRef unitParent;
  bool hasUnitParentClause = false;
  RenderedKernelClause unitParentClause;
  bool hasSelected = false;
  RenderedKernelLiteral selected;
  bool hasSelectedSubstituted = false;
  RenderedKernelLiteral selectedSubstituted;
  bool hasUnitSubstituted = false;
  RenderedKernelLiteral unitSubstituted;
  bool hasRemainingAfter = false;
  RenderedKernelClause remainingAfter;
};

struct RenderedKernelPrimitiveParentSubstitution {
  std::size_t parentIndex = 0;
  RenderedKernelSubstitution substitution;
};

struct RenderedKernelSubsumptionResolutionPivot {
  std::size_t mainParentIndex = 0;
  std::size_t sideParentIndex = 0;
  bool hasSideSubstitution = false;
  RenderedKernelSubstitution sideSubstitution;
  bool hasSidePivot = false;
  RenderedKernelLiteral sidePivot;
  bool hasSidePivotLocation = false;
  std::size_t sidePivotParentIndex = 0;
  std::size_t sidePivotLiteralIndex = 0;
  RenderedKernelUnitRef sidePivotParentUnit;
  bool hasSidePivotSubstituted = false;
  RenderedKernelLiteral sidePivotSubstituted;
  bool sidePivotMatchesBySymmetry = false;
};

struct MegalodonKernelStep {
  std::string id;
  std::string rule;
  std::vector<PrimitiveExpansion> primitiveExpansions;
  std::vector<MigrationField> migrationFields;
  std::vector<RenderedKernelPrimitiveParentSubstitution> primitiveParentSubstitutions;
  bool hasSubsumptionResolutionPivot = false;
  RenderedKernelSubsumptionResolutionPivot subsumptionResolutionPivot;
  bool hasConclusion = false;
  RenderedKernelConclusion conclusion;
  bool hasParents = false;
  std::vector<RenderedKernelParent> parents;
};

const std::string& schema();

std::vector<std::string> requiredPrimitivesForRule(const std::string& rule);

RenderedKernelUnitRef unitRef(const std::string& value);
RenderedKernelTerm term(const std::string& sexpr);
RenderedKernelFormula formula(const std::string& sexpr);
RenderedKernelLiteral literal(const std::string& sexpr);
RenderedKernelClause clause(const std::string& sexpr);
RenderedKernelSubstitution substitution(const std::string& sexpr);
RenderedKernelPosition position(const std::string& sexpr);
std::vector<RenderedKernelLiteral> literals(const std::vector<std::string>& sexprs);
MigrationField migrationField(const std::string& rendered);
RenderedKernelPrimitiveParentSubstitution primitiveParentSubstitution(
  std::size_t parentIndex,
  const RenderedKernelSubstitution& substitution);

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

void addPrimitiveParentSubstitution(
  MegalodonKernelStep& step,
  const RenderedKernelPrimitiveParentSubstitution& substitution);

void setSubsumptionResolutionPivot(
  MegalodonKernelStep& step,
  const RenderedKernelSubsumptionResolutionPivot& pivot);

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

void appendUrrTraceStep(
  std::vector<std::string>& fields,
  const RenderedKernelUrrTraceStep& step);

std::vector<std::string> kernelStepFields(const MegalodonKernelStep& step);

bool appendFixedPrimitiveExpansionForRule(
  std::vector<std::string>& fields,
  const std::string& prefix,
  const std::string& rule);

}
}

#endif
