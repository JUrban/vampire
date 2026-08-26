#ifndef __MEGALODON_KERNEL_BUILDER__
#define __MEGALODON_KERNEL_BUILDER__

#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"

#include <functional>
#include <map>
#include <string>
#include <vector>

namespace Kernel {
class Formula;
}

namespace SAT {
class SATClause;
}

namespace Shell {
namespace MegalodonKernelBuilder {

class PrimitiveChain {
public:
  std::string render(MegalodonKernelSyntax::PrimitiveStep primitive);
  bool collect(
    const std::vector<std::string>& renderedSteps,
    std::vector<MegalodonKernelSyntax::PrimitiveStep>* primitiveSteps) const;

private:
  std::map<std::string, MegalodonKernelSyntax::PrimitiveStep> _primitives;
};

std::string avatarPrimitiveWithMetadata(
  const MegalodonKernelSyntax::PrimitiveStep& step);

MegalodonKernelSyntax::PrimitiveStep resolveStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& leftParent,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& rightParent,
  std::size_t leftPivot,
  std::size_t rightPivot,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep factorStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t leftLiteral,
  std::size_t rightLiteral,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep equalitySymmetryStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep substituteStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelSubstitution& substitution,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep equalityResolutionStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields);

MegalodonKernelSyntax::PrimitiveStep equalityResolutionConstraintsStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelLiteral& selected,
  const MegalodonKernelSyntax::RenderedKernelClause& constraints,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields);

MegalodonKernelSyntax::PrimitiveStep paramodulateStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& equalityParent,
  std::size_t equalityLiteral,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& targetParent,
  std::size_t targetLiteral,
  const MegalodonKernelSyntax::RenderedKernelPosition& position,
  const MegalodonKernelSyntax::RenderedKernelTerm& from,
  const MegalodonKernelSyntax::RenderedKernelTerm& to,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep foolAtomLiftStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFormula& target,
  const std::string& path,
  const std::vector<std::pair<
    std::string,
    MegalodonKernelSyntax::RenderedKernelType>>& context);

MegalodonKernelSyntax::PrimitiveStep rectifyFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFormula& result,
  const MegalodonKernelSyntax::RenderedKernelRectifyRenamings& renamings);

MegalodonKernelSyntax::PrimitiveStep ennfFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelEnnfTrace& trace,
  const MegalodonKernelSyntax::RenderedKernelFormula& result);

MegalodonKernelSyntax::PrimitiveStep skolemFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const std::vector<MegalodonKernelSyntax::RenderedKernelScopedSkolemBranch>& branches,
  const MegalodonKernelSyntax::RenderedKernelFormula& result);

MegalodonKernelSyntax::PrimitiveStep cnfLiteralStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep cnfFormulaClauseStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  std::size_t index,
  std::size_t count,
  const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep avatarComponentStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep avatarDefinitionStep(
  const std::string& id,
  unsigned splitVariable,
  bool splitPositive,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep splitDependencyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& owner,
  const std::vector<MegalodonKernelSyntax::RenderedKernelSplitDependencyItem>& dependencies,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

MegalodonKernelSyntax::PrimitiveStep avatarSplitStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& parents,
  const MegalodonKernelSyntax::RenderedKernelClause& result);

bool collectAvatarSatProof(
  SAT::SATClause* root,
  MegalodonKernelSyntax::RenderedKernelAvatarRefutation* refutation);

bool avatarRefutationStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelAvatarRefutation& refutation,
  MegalodonKernelSyntax::PrimitiveStep* result);

std::vector<MegalodonKernelSyntax::RenderedKernelSkolemBranchScopeSymbol>
sourceSignatureScope(
  Kernel::Formula* formula,
  const std::function<std::string(unsigned)>& functionName,
  const std::function<std::string(unsigned)>& predicateName);

}
}

#endif
