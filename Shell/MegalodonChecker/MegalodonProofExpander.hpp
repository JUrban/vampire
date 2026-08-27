#ifndef __MEGALODON_PROOF_EXPANDER__
#define __MEGALODON_PROOF_EXPANDER__

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
};

struct GroundTerm {
  Kernel::TermList sort;
  Kernel::TermList term;
  bool requiresExistingApplication = false;
  unsigned functionSymbol = 0;
};

struct Step {
  std::string id;
  std::vector<std::string> parentIds;
  Environment parentSubstitution;
  VariableSorts freeVariableSorts;
  std::vector<Application> applications;
};

struct Instance {
  std::size_t index = 0;
  std::string stepId;
  Environment environment;
  std::vector<std::size_t> parentInstances;
  std::vector<Application> applications;
};

struct Expansion {
  std::string version;
  std::string finalStep;
  std::vector<Instance> instances;
};

struct SubstituteClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef parent;
  MegalodonKernelSyntax::RenderedKernelSubstitution substitution;
  MegalodonKernelSyntax::RenderedKernelClause result;
};

struct EqualitySymmetryClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef parent;
  std::size_t literal = 0;
  MegalodonKernelSyntax::RenderedKernelClause result;
};

struct ResolveClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef leftParent;
  MegalodonKernelSyntax::RenderedKernelUnitRef rightParent;
  std::size_t leftPivot = 0;
  std::size_t rightPivot = 0;
  MegalodonKernelSyntax::RenderedKernelClause result;
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
};

struct FactorClauseStep {
  std::string id;
  MegalodonKernelSyntax::RenderedKernelUnitRef parent;
  std::size_t leftLiteral = 0;
  std::size_t rightLiteral = 0;
  MegalodonKernelSyntax::RenderedKernelClause result;
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

bool expandGroundProof(
  const std::vector<Step>& steps,
  const std::string& finalStep,
  const std::vector<GroundTerm>& groundTerms,
  Expansion& result,
  std::string& error);

bool expandClauseProof(
  const std::vector<ClauseStepRequest>& requests,
  const std::string& finalStep,
  ClauseExpansion& result,
  std::string& error);

}
}

#endif
