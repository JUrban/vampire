#ifndef __MEGALODON_KERNEL_SYNTAX__
#define __MEGALODON_KERNEL_SYNTAX__

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

namespace Shell {
namespace MegalodonKernelSyntax {

struct PrimitiveExpansion {
  std::string prefix;
  std::string requiredRule;
};

struct PrimitiveStep {
  std::string rule;
  std::string id;
  std::string rendered;
  std::vector<std::string> parentIds;
  bool hasResultClause = false;
  std::string resultClause;
  std::vector<std::pair<std::string, std::string>> fields;
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

struct RenderedKernelType {
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

struct RenderedKernelUrrTrace {
  bool hasMainParent = false;
  RenderedKernelUnitRef mainParent;
  std::vector<RenderedKernelUrrTraceStep> steps;
  bool hasRemaining = false;
  RenderedKernelClause remaining;
};

struct RenderedKernelAvatarSplit {
  std::size_t index = 0;
  unsigned level = 0;
  unsigned variable = 0;
  bool positive = false;
};

struct RenderedKernelAvatarComponent {
  bool hasResultClause = false;
  RenderedKernelClause resultClause;
  std::size_t literalCount = 0;
  std::vector<RenderedKernelLiteral> literals;
  std::size_t splitCount = 0;
  std::vector<RenderedKernelAvatarSplit> splits;
};

struct RenderedKernelAvatarDefinition {
  RenderedKernelAvatarSplit componentSplit;
  bool hasComponentClause = false;
  std::string componentClause;
  bool hasComponentClauseSexpr = false;
  RenderedKernelClause componentClauseSexpr;
  std::vector<std::string> componentClauseVariableSorts;
  std::vector<std::string> componentClauseDbSorts;
  bool hasResultClause = false;
  RenderedKernelClause resultClause;
};

struct RenderedKernelSplitDependencyItem {
  std::size_t index = 0;
  RenderedKernelAvatarSplit split;
  bool hasComponentClause = false;
  std::string componentClause;
  bool hasComponentClauseSexpr = false;
  RenderedKernelClause componentClauseSexpr;
  std::vector<std::string> componentClauseVariableSorts;
  std::vector<std::string> componentClauseDbSorts;
  std::vector<MigrationField> componentClauseExtraFields;
};

struct RenderedKernelSplitDependency {
  std::vector<RenderedKernelSplitDependencyItem> dependencies;
  bool hasResultClause = false;
  RenderedKernelClause resultClause;
};

struct RenderedKernelAvatarSatLiteral {
  std::size_t index = 0;
  unsigned variable = 0;
  bool positive = false;
};

struct RenderedKernelAvatarComponentParent {
  std::size_t parentIndex = 0;
  std::size_t refIndex = 0;
  RenderedKernelUnitRef unit;
  RenderedKernelAvatarSplit split;
  bool hasClause = false;
  std::string clause;
  bool hasClauseSexpr = false;
  RenderedKernelClause clauseSexpr;
};

struct RenderedKernelAvatarLiteralClass {
  std::size_t index = 0;
  std::size_t literalCount = 0;
  std::vector<std::string> literals;
  bool hasMatchedSplitLevel = false;
  unsigned matchedSplitLevel = 0;
};

struct RenderedKernelAvatarParentVarBinding {
  std::size_t index = 0;
  std::string parentVar;
  bool hasComponentVar = false;
  std::string componentVar;
  bool hasSplitVar = false;
  unsigned splitVar = 0;
};

struct RenderedKernelAvatarSplitStep {
  RenderedKernelUnitRef sourceUnit;
  bool hasSourceClause = false;
  RenderedKernelClause sourceClause;
  bool hasResultClause = false;
  RenderedKernelClause resultClause;
  bool hasResultFormula = false;
  RenderedKernelFormula resultFormula;
  std::string vampireRule;
  bool hasSourceText = false;
  std::string sourceText;
  bool hasTargetText = false;
  std::string targetText;
  std::vector<RenderedKernelAvatarSplit> previousSplits;
  std::vector<RenderedKernelAvatarSatLiteral> satLiterals;
  std::vector<RenderedKernelAvatarComponentParent> componentParents;
  std::size_t componentParentCount = 0;
  std::vector<RenderedKernelAvatarLiteralClass> literalClasses;
  std::vector<RenderedKernelAvatarParentVarBinding> parentVarBindings;
};

struct RenderedKernelSatInput {
  std::size_t index = 0;
  bool hasClause = false;
  RenderedKernelClause clause;
  bool hasOriginUnit = false;
  RenderedKernelUnitRef originUnit;
};

struct RenderedKernelSatProofParent {
  std::size_t index = 0;
  unsigned id = 0;
  bool hasClause = false;
  RenderedKernelClause clause;
};

struct RenderedKernelSatProofStep {
  std::size_t index = 0;
  unsigned id = 0;
  bool hasClause = false;
  RenderedKernelClause clause;
  std::string kind;
  bool hasOriginUnit = false;
  RenderedKernelUnitRef originUnit;
  std::vector<RenderedKernelSatProofParent> parents;
};

struct RenderedKernelAvatarRefutation {
  bool hasResultClause = false;
  RenderedKernelClause resultClause;
  bool hasSatRefutationClause = false;
  RenderedKernelClause satRefutationClause;
  std::vector<RenderedKernelSatInput> inputs;
  std::vector<RenderedKernelSatProofStep> proofSteps;
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

struct RenderedKernelSkolemDependency {
  bool hasTerm = false;
  RenderedKernelTerm term;
  bool hasVariable = false;
  std::string variable;
  bool hasSort = false;
  std::string sort;
  bool hasSortSexpr = false;
  RenderedKernelType sortSexpr;
};

struct RenderedKernelSkolemIntroducedSymbol {
  std::size_t index = 0;
  bool hasKind = false;
  std::string kind;
  bool hasRawSymbol = false;
  std::string rawSymbol;
  bool hasReplacedVariable = false;
  std::string replacedVariable;
  bool hasSymbol = false;
  std::string symbol;
  bool hasDeclaration = false;
  std::string declaration;
  bool hasReplacedVariableSort = false;
  std::string replacedVariableSort;
  bool hasReplacedVariableSortSexpr = false;
  RenderedKernelType replacedVariableSortSexpr;
  bool hasWitnessTerm = false;
  RenderedKernelTerm witnessTerm;
  bool hasWitnessSort = false;
  std::string witnessSort;
  bool hasWitnessSortSexpr = false;
  RenderedKernelType witnessSortSexpr;
  bool hasSourceVariableApplicationCount = false;
  std::size_t sourceVariableApplicationCount = 0;
  std::vector<RenderedKernelSkolemDependency> dependencies;
  bool hasChoicePrinciple = false;
  std::string choicePrinciple;
};

struct RenderedKernelQuantifiedVariable {
  std::string kind;
  std::string variable;
  RenderedKernelType type;
};

struct RenderedKernelTypedVariable {
  std::string variable;
  RenderedKernelType type;
};

struct RenderedKernelFormulaChild {
  std::size_t index = 0;
  std::string role;
  RenderedKernelFormula formula;
};

struct RenderedKernelSkolemMacroEdge {
  std::size_t index = 0;
  std::size_t parentIndex = 0;
  RenderedKernelUnitRef unit;
  std::vector<std::pair<std::string, RenderedKernelType>> binders;
  std::vector<RenderedKernelQuantifiedVariable> formulaQuantifiedVariables;
  std::vector<RenderedKernelTypedVariable> formulaFreeVariables;
  std::vector<RenderedKernelFormulaChild> formulaChildren;
  std::vector<RenderedKernelQuantifiedVariable> sourceQuantifiedVariables;
  std::vector<RenderedKernelTypedVariable> sourceFreeVariables;
  std::vector<RenderedKernelFormulaChild> sourceChildren;
  std::vector<RenderedKernelQuantifiedVariable> targetQuantifiedVariables;
  std::vector<RenderedKernelTypedVariable> targetFreeVariables;
  std::vector<RenderedKernelFormulaChild> targetChildren;
  bool hasFormulaShape = false;
  std::string formulaConnective;
  std::size_t formulaExistsCount = 0;
  std::size_t formulaForallCount = 0;
  std::size_t formulaAndCount = 0;
  std::size_t formulaOrCount = 0;
  std::size_t formulaImpCount = 0;
  bool hasFormula = false;
  RenderedKernelFormula formula;
  bool hasSourceShape = false;
  std::string sourceConnective;
  std::size_t sourceExistsCount = 0;
  std::size_t sourceForallCount = 0;
  std::size_t sourceAndCount = 0;
  std::size_t sourceOrCount = 0;
  std::size_t sourceImpCount = 0;
  bool hasSource = false;
  RenderedKernelFormula source;
  bool hasTargetShape = false;
  std::string targetConnective;
  std::size_t targetExistsCount = 0;
  std::size_t targetForallCount = 0;
  std::size_t targetAndCount = 0;
  std::size_t targetOrCount = 0;
  std::size_t targetImpCount = 0;
  bool hasTarget = false;
  RenderedKernelFormula target;
  bool hasProofContract = false;
};

struct RenderedKernelSkolemProofContract {
  std::string version = "choice_macro_v1";
  std::string primitiveRule = "skolem_formula";
  RenderedKernelUnitRef sourceUnit;
  RenderedKernelFormula sourceFormula;
  RenderedKernelFormula resultFormula;
  std::size_t proofParentCount = 0;
  std::size_t introducedCount = 0;
  std::size_t macroEdgeCount = 0;
  bool usesClassicalChoice = false;
};

struct RenderedKernelTransformationPair {
  std::size_t index = 0;
  RenderedKernelFormula source;
  RenderedKernelFormula target;
  bool hasPath = false;
  std::string path;
  bool hasKind = false;
  std::string kind;
};

struct RenderedKernelSourceFormulaTransform {
  RenderedKernelUnitRef sourceUnit;
  RenderedKernelFormula sourceFormula;
  RenderedKernelFormula resultFormula;
  std::size_t proofParentCount = 1;
  bool hasCopyKind = false;
  std::string copyKind;
  bool hasNormalFormRule = false;
  std::string normalFormRule;
  std::vector<RenderedKernelTransformationPair> transformationPairs;
};

struct RenderedKernelRectifyRenaming {
  std::size_t index = 0;
  bool hasSource = false;
  RenderedKernelFormula source;
  bool hasTarget = false;
  RenderedKernelFormula target;
  bool hasSubstitution = false;
  RenderedKernelSubstitution substitution;
};

struct RenderedKernelRectifyRenamings {
  std::size_t reportedCount = 0;
  std::vector<RenderedKernelRectifyRenaming> renamings;
  bool truncated = false;
  bool hasVariableMap = false;
  RenderedKernelSubstitution variableMap;
};

struct RenderedKernelCnfClause {
  RenderedKernelUnitRef sourceUnit;
  std::string sourceKind;
  std::size_t proofParentCount = 1;
  bool hasSourceClause = false;
  RenderedKernelClause sourceClause;
  bool hasSourceFormula = false;
  RenderedKernelFormula sourceFormula;
  bool hasResultClause = false;
  RenderedKernelClause resultClause;
  bool hasParentClauseCount = false;
  std::size_t parentClauseCount = 0;
  bool hasClauseParentUnit = false;
  RenderedKernelUnitRef clauseParentUnit;
  bool hasClauseIndex = false;
  std::size_t clauseIndex = 0;
  bool hasClauseCount = false;
  std::size_t clauseCount = 0;
};

struct RenderedKernelDefinitionParent {
  std::size_t index = 0;
  RenderedKernelUnitRef unit;
  bool hasFormula = false;
  RenderedKernelFormula formula;
  bool hasSymbol = false;
  std::string symbol;
};

struct RenderedKernelDefinitionFold {
  RenderedKernelUnitRef sourceUnit;
  bool hasSourceFormula = false;
  RenderedKernelFormula sourceFormula;
  std::vector<RenderedKernelDefinitionParent> definitions;
  bool hasResultFormula = false;
  RenderedKernelFormula resultFormula;
};

struct RenderedKernelPredicateDefinitionVariable {
  std::size_t index = 0;
  std::string renderedSort;
};

struct RenderedKernelPredicateDefinition {
  std::string introducedSymbol;
  bool hasSort = false;
  std::string sort;
  bool hasDefiniendumSymbol = false;
  std::string definiendumSymbol;
  bool hasBodyFormula = false;
  RenderedKernelFormula bodyFormula;
  bool hasResultFormula = false;
  RenderedKernelFormula resultFormula;
  std::vector<RenderedKernelPredicateDefinitionVariable> bodyVariables;
  std::string proofShape = "classical_definitional_split";
  std::string classicalPrinciple = "xm";
  std::string positiveBranch = "definition_body";
  std::string negativeBranch = "negated_definiendum";
};

struct MegalodonKernelStep {
  std::string id;
  std::string rule;
  std::vector<PrimitiveExpansion> primitiveExpansions;
  std::vector<MigrationField> migrationFields;
  std::vector<RenderedKernelPrimitiveParentSubstitution> primitiveParentSubstitutions;
  bool hasSubsumptionResolutionPivot = false;
  RenderedKernelSubsumptionResolutionPivot subsumptionResolutionPivot;
  std::vector<RenderedKernelSkolemIntroducedSymbol> skolemIntroducedSymbols;
  bool hasSkolemSourceFormulaQuantifiedVariables = false;
  std::vector<RenderedKernelQuantifiedVariable> skolemSourceFormulaQuantifiedVariables;
  bool hasSkolemResultFormulaQuantifiedVariables = false;
  std::vector<RenderedKernelQuantifiedVariable> skolemResultFormulaQuantifiedVariables;
  bool hasSkolemSourceFormulaFreeVariables = false;
  std::vector<RenderedKernelTypedVariable> skolemSourceFormulaFreeVariables;
  bool hasSkolemResultFormulaFreeVariables = false;
  std::vector<RenderedKernelTypedVariable> skolemResultFormulaFreeVariables;
  bool hasSkolemMacroEdges = false;
  std::vector<RenderedKernelSkolemMacroEdge> skolemMacroEdges;
  bool hasSkolemProofContract = false;
  RenderedKernelSkolemProofContract skolemProofContract;
  bool hasSourceFormulaTransform = false;
  RenderedKernelSourceFormulaTransform sourceFormulaTransform;
  bool hasRectifyRenamings = false;
  RenderedKernelRectifyRenamings rectifyRenamings;
  bool hasCnfClause = false;
  RenderedKernelCnfClause cnfClause;
  bool hasDefinitionFold = false;
  RenderedKernelDefinitionFold definitionFold;
  bool hasPredicateDefinition = false;
  RenderedKernelPredicateDefinition predicateDefinition;
  bool hasUrrTrace = false;
  RenderedKernelUrrTrace urrTrace;
  bool hasAvatarComponent = false;
  RenderedKernelAvatarComponent avatarComponent;
  bool hasAvatarDefinition = false;
  RenderedKernelAvatarDefinition avatarDefinition;
  bool hasSplitDependency = false;
  RenderedKernelSplitDependency splitDependency;
  bool hasAvatarSplit = false;
  RenderedKernelAvatarSplitStep avatarSplit;
  bool hasAvatarRefutation = false;
  RenderedKernelAvatarRefutation avatarRefutation;
  bool hasConclusion = false;
  RenderedKernelConclusion conclusion;
  bool hasParents = false;
  std::vector<RenderedKernelParent> parents;
};

const std::string& schema();

std::vector<std::string> structuralRules();
std::vector<std::string> supportedRules();
bool isSupportedRule(const std::string& rule);
std::vector<std::string> requiredPrimitivesForRule(const std::string& rule);

RenderedKernelUnitRef unitRef(const std::string& value);
RenderedKernelTerm term(const std::string& sexpr);
RenderedKernelFormula formula(const std::string& sexpr);
RenderedKernelLiteral literal(const std::string& sexpr);
RenderedKernelClause clause(const std::string& sexpr);
RenderedKernelSubstitution substitution(const std::string& sexpr);
RenderedKernelPosition position(const std::string& sexpr);
RenderedKernelType type(const std::string& sexpr);
std::vector<RenderedKernelLiteral> literals(const std::vector<std::string>& sexprs);
MigrationField migrationField(const std::string& rendered);
RenderedKernelPrimitiveParentSubstitution primitiveParentSubstitution(
  std::size_t parentIndex,
  const RenderedKernelSubstitution& substitution);

PrimitiveExpansion primitiveExpansion(
  const std::string& prefix,
  const std::string& primitiveRule);

PrimitiveStep primitiveStep(
  const std::string& rule,
  const std::string& id,
  const std::string& rendered);

PrimitiveStep primitiveClauseStep(
  const std::string& rule,
  const std::string& id,
  const std::vector<std::string>& parentIds,
  const std::string& resultClause,
  const std::vector<std::pair<std::string, std::string>>& fields,
  const std::string& rendered);

void appendPrimitiveExpansion(
  std::vector<std::string>& fields,
  const PrimitiveExpansion& expansion);

bool appendPrimitiveExpansionChainFields(
  std::vector<std::string>& fields,
  const std::string& expansion,
  const std::string& finalRule,
  const std::string& expectedFinalId = "");

bool appendPrimitiveExpansionChainFields(
  std::vector<std::string>& fields,
  const std::vector<PrimitiveStep>& primitiveSteps,
  const std::string& expectedFinalId = "");

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

void addSkolemIntroducedSymbol(
  MegalodonKernelStep& step,
  const RenderedKernelSkolemIntroducedSymbol& introduced);

void setSkolemSourceFormulaQuantifiedVariables(
  MegalodonKernelStep& step,
  const std::vector<RenderedKernelQuantifiedVariable>& variables);

void setSkolemResultFormulaQuantifiedVariables(
  MegalodonKernelStep& step,
  const std::vector<RenderedKernelQuantifiedVariable>& variables);

void setSkolemSourceFormulaFreeVariables(
  MegalodonKernelStep& step,
  const std::vector<RenderedKernelTypedVariable>& variables);

void setSkolemResultFormulaFreeVariables(
  MegalodonKernelStep& step,
  const std::vector<RenderedKernelTypedVariable>& variables);

void addSkolemMacroEdge(
  MegalodonKernelStep& step,
  const RenderedKernelSkolemMacroEdge& edge);

void setSkolemProofContract(
  MegalodonKernelStep& step,
  const RenderedKernelSkolemProofContract& contract);

void setSourceFormulaTransform(
  MegalodonKernelStep& step,
  const RenderedKernelSourceFormulaTransform& transform);

void setRectifyRenamings(
  MegalodonKernelStep& step,
  const RenderedKernelRectifyRenamings& renamings);

void setCnfClause(
  MegalodonKernelStep& step,
  const RenderedKernelCnfClause& cnfClause);

void setDefinitionFold(
  MegalodonKernelStep& step,
  const RenderedKernelDefinitionFold& definitionFold);

void setPredicateDefinition(
  MegalodonKernelStep& step,
  const RenderedKernelPredicateDefinition& predicateDefinition);

void setUrrTrace(
  MegalodonKernelStep& step,
  const RenderedKernelUrrTrace& urrTrace);

void setAvatarComponent(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarComponent& avatarComponent);

void setAvatarDefinition(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarDefinition& avatarDefinition);

void setSplitDependency(
  MegalodonKernelStep& step,
  const RenderedKernelSplitDependency& splitDependency);

void setAvatarSplit(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarSplitStep& avatarSplit);

void setAvatarRefutation(
  MegalodonKernelStep& step,
  const RenderedKernelAvatarRefutation& avatarRefutation);

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
