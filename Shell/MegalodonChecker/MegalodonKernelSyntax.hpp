#ifndef __MEGALODON_KERNEL_SYNTAX__
#define __MEGALODON_KERNEL_SYNTAX__

#include <string>
#include <vector>

namespace Shell {
namespace MegalodonKernelSyntax {

const std::string& schema();

std::vector<std::string> requiredPrimitivesForRule(const std::string& rule);

}
}

#endif
