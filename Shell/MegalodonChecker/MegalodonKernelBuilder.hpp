#ifndef __MEGALODON_KERNEL_BUILDER__
#define __MEGALODON_KERNEL_BUILDER__

#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"

#include <functional>
#include <string>
#include <vector>

namespace Kernel {
class Formula;
}

namespace Shell {
namespace MegalodonKernelBuilder {

MegalodonKernelSyntax::PrimitiveStep primitiveClauseStep(
  const std::string& rule,
  const std::string& id,
  const std::vector<std::string>& parentIds,
  const std::string& resultClause,
  const std::vector<std::pair<std::string, std::string>>& fields,
  const std::string& rendered);

std::vector<MegalodonKernelSyntax::RenderedKernelSkolemBranchScopeSymbol>
sourceSignatureScope(
  Kernel::Formula* formula,
  const std::function<std::string(unsigned)>& functionName,
  const std::function<std::string(unsigned)>& predicateName);

}
}

#endif
