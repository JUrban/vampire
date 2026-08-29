#ifndef __MEGALODON_PROOF_EXPANDER__
#define __MEGALODON_PROOF_EXPANDER__

#include "Kernel/Formula.hpp"
#include "Kernel/Term.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"

#include <cstddef>
#include <string>
#include <utility>
#include <variant>
#include <vector>

namespace Shell {
namespace MegalodonProofExpander {

using Environment = std::vector<std::pair<unsigned, Kernel::TermList>>;
using VariableSorts = std::vector<std::pair<unsigned, Kernel::TermList>>;

struct Application {
  unsigned functionSymbol = 0;
  Kernel::TermList term;
  bool requiresGrounding = true;
  bool skolemOwner = false;
};

struct GroundTerm {
  Kernel::TermList sort;
  Kernel::TermList term;
  bool requiresExistingApplication = false;
  unsigned functionSymbol = 0;
};

struct FunctionDefinition {
  unsigned functionSymbol = 0;
  std::vector<unsigned> parameters;
  Kernel::TermList body;
};

struct Step {
  std::string id;
  std::vector<std::string> parentIds;
  std::vector<std::string> parametricParentIds;
  Environment parentSubstitution;
  VariableSorts freeVariableSorts;
  std::vector<Application> applications;
};

struct Instance {
  std::size_t index = 0;
  std::string stepId;
  bool parametric = false;
  Environment environment;
  std::vector<std::size_t> parentInstances;
  std::vector<Environment> parentEnvironments;
  std::vector<Application> applications;
  std::vector<Application> sourceApplications;
};

struct Expansion {
  std::string version;
  std::string finalStep;
  std::vector<Instance> instances;
};

struct ChoiceProofStep {
  MegalodonKernelSyntax::PrimitiveStep primitive;
  bool hasParameterContract = false;
  std::vector<std::pair<std::string, std::string>> parameters;
};

struct ChoiceTermDefinition {
  std::string stepId;
  std::string symbol;
  std::string resultType;
  std::vector<std::pair<std::string, std::string>> parameters;
  std::string body;
  std::string resultClause;
};

struct SubstituteClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef parent;
  MegalodonKernelSyntax::RenderedKernelSubstitution substitution;
  MegalodonKernelSyntax::RenderedKernelClause result;
  std::string producerProof;
};

struct EqualitySymmetryClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef parent;
  std::size_t literal = 0;
  MegalodonKernelSyntax::RenderedKernelClause result;
  std::string producerProof;
};

struct ResolveClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef leftParent;
  MegalodonKernelSyntax::RenderedKernelUnitRef rightParent;
  std::size_t leftPivot = 0;
  std::size_t rightPivot = 0;
  MegalodonKernelSyntax::RenderedKernelClause result;
  bool hasIvyProgram = false;
  std::vector<std::string> leftLiterals;
  std::vector<std::string> rightLiterals;
  std::vector<std::string> resultLiterals;
  std::string producerProof;
};

struct ParamodulateClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef equalityParent;
  MegalodonKernelSyntax::RenderedKernelUnitRef targetParent;
  std::size_t equalityLiteral = 0;
  std::size_t targetLiteral = 0;
  MegalodonKernelSyntax::RenderedKernelPosition position;
  MegalodonKernelSyntax::RenderedKernelTerm from;
  MegalodonKernelSyntax::RenderedKernelTerm to;
  MegalodonKernelSyntax::RenderedKernelClause result;
  bool hasIvyProgram = false;
  std::vector<std::string> equalityLiterals;
  std::vector<std::string> targetLiterals;
  std::string rewrittenLiteral;
  std::vector<std::string> resultLiterals;
  bool rewriteSymmetry = false;
  std::string producerProof;
};

struct FactorClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef parent;
  std::size_t leftLiteral = 0;
  std::size_t rightLiteral = 0;
  MegalodonKernelSyntax::RenderedKernelClause result;
  bool hasIvyProgram = false;
  std::vector<std::string> sourceLiterals;
  std::vector<std::string> resultLiterals;
  std::string producerProof;
};

using ClauseStep = std::variant<
  SubstituteClauseStep,
  EqualitySymmetryClauseStep,
  ResolveClauseStep,
  ParamodulateClauseStep,
  FactorClauseStep>;

struct ClauseStepRequest {
  ClauseStep step;
  std::vector<std::string> trailingRecords;
};

struct ClauseExpansion {
  std::vector<MegalodonKernelSyntax::PrimitiveStep> primitives;
  std::vector<std::string> renderedSteps;
  std::string rendered;
};

struct FormulaTransportNode {
  std::size_t index = 0;
  std::string primitive;
  Kernel::Formula* source = nullptr;
  Kernel::Formula* target = nullptr;
  Environment sourceVariableMap;
  Environment targetVariableMap;
  bool preserveSourceNegativeEqualityOrientation = false;
  bool preserveTargetNegativeEqualityOrientation = false;
  VariableSorts context;
  std::vector<FormulaTransportNode> children;
};

struct FormulaTransportRequest {
  Kernel::Formula* source = nullptr;
  Kernel::Formula* target = nullptr;
  Environment freeVariableMap;
  bool preserveSourceNegativeEqualityOrientation = false;
};

struct GoalReplayStep {
  std::string id;
  std::vector<std::string> parentIds;
  std::string sourceRole;
  bool source = false;
  bool final = false;
  MegalodonKernelSyntax::RenderedKernelFormula formula;
};

struct AvatarContradictionProofRequest {
  std::string parentId;
  std::vector<std::string> parentArguments;
  std::vector<std::string> sourceLiterals;
  std::vector<std::string> resultLiterals;
};

struct AvatarComponentDefinition {
  std::string id;
  unsigned splitVariable = 0;
  bool splitPositive = false;
  std::vector<std::string> componentLiterals;
  std::vector<std::pair<std::string, MegalodonKernelSyntax::RenderedKernelType>>
    componentVariables;
};

struct AvatarComponentProofRequest {
  std::vector<std::string> resultLiterals;
  std::vector<std::pair<std::string, MegalodonKernelSyntax::RenderedKernelType>>
    resultVariables;
  std::vector<AvatarComponentDefinition> definitions;
};

bool expandGroundProof(
  const std::vector<Step>& steps,
  const std::string& finalStep,
  const std::vector<GroundTerm>& groundTerms,
  const std::vector<FunctionDefinition>& functionDefinitions,
  Expansion& result,
  std::string& error);

bool expandChoiceNormalizedProof(
  const std::vector<ChoiceProofStep>& steps,
  const std::vector<MegalodonKernelSyntax::PrimitiveStep>& skolemSteps,
  const std::vector<ChoiceTermDefinition>& termDefinitions,
  const std::string& finalStep,
  MegalodonKernelSyntax::RenderedKernelChoiceProof& result,
  std::string& error);

bool expandClauseProof(
  const std::vector<ClauseStepRequest>& requests,
  const std::string& finalStep,
  ClauseExpansion& result,
  std::string& error);

bool expandFormulaTransport(
  const FormulaTransportRequest& request,
  FormulaTransportNode& result,
  std::string& error);

bool expandGoalReplay(
  const std::vector<GoalReplayStep>& steps,
  const std::string& finalStep,
  MegalodonKernelSyntax::RenderedKernelGoalReplay& result,
  std::string& error);

bool expandAvatarContradictionProof(
  const AvatarContradictionProofRequest& request,
  std::string& result,
  std::string& error);

bool expandAvatarDefinitionProof(
  const MegalodonKernelSyntax::RenderedKernelAvatarDefinition& request,
  std::string& resultFormula,
  std::string& result,
  std::string& error);

bool expandAvatarComponentProof(
  const AvatarComponentProofRequest& request,
  std::string& result,
  std::string& error);

bool expandAvatarSplitProof(
  const MegalodonKernelSyntax::RenderedKernelAvatarSplitStep& request,
  std::string& result,
  std::string& error);

bool expandAvatarSatProjectionProof(
  const std::string& parentId,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseProjectionProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandCnfFormulaClauseProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::string& sourceFormula,
  const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandFoolFormulaProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
  std::string& result,
  std::string& error);

bool expandEnnfFormulaProof(
  const std::string& stepId,
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const MegalodonKernelSyntax::RenderedKernelEnnfTrace& trace,
  std::string& result,
  std::string& error);

bool buildFoolFormulaProgram(
  const std::string& sourceFormula,
  const std::string& targetFormula,
  MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
  std::string& error);

bool expandAvatarSatResolutionProof(
  const std::string& leftParentId,
  const std::vector<std::string>& leftLiterals,
  std::size_t leftPivot,
  const std::string& rightParentId,
  const std::vector<std::string>& rightLiterals,
  std::size_t rightPivot,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseResolutionProof(
  const std::string& leftParentId,
  const std::vector<std::string>& leftParentArguments,
  const std::vector<std::string>& leftLiterals,
  std::size_t leftPivot,
  const std::string& rightParentId,
  const std::vector<std::string>& rightParentArguments,
  const std::vector<std::string>& rightLiterals,
  std::size_t rightPivot,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseEqualityResolutionProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseEqualitySymmetryProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseTruthConflictProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseInstantiationProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArgumentTerms,
  std::string& result,
  std::string& error);

bool expandClauseSubstitutionProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArgumentTerms,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseEqualityFactoringProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArgumentTerms,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  std::size_t otherLiteral,
  const std::string& selectedSharedTerm,
  const std::string& otherOtherTerm,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error);

bool expandClauseParamodulationProof(
  const std::string& equalityParentId,
  const std::vector<std::string>& equalityParentArguments,
  const std::vector<std::string>& equalityLiterals,
  std::size_t equalityLiteral,
  const std::string& targetParentId,
  const std::vector<std::string>& targetParentArguments,
  const std::vector<std::string>& targetLiterals,
  std::size_t targetLiteral,
  const std::vector<unsigned>& position,
  const std::string& from,
  const std::string& to,
  const std::string& rewrittenLiteral,
  const std::vector<std::string>& resultLiterals,
  bool rewriteSymmetry,
  std::string& result,
  std::string& error);

}
}

#endif
