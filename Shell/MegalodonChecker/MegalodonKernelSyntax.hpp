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

struct MegalodonKernelStep {
  std::string id;
  std::string rule;
  std::vector<PrimitiveExpansion> primitiveExpansions;
  std::vector<std::string> fields;
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

std::vector<std::string> kernelStepFields(const MegalodonKernelStep& step);

bool appendFixedPrimitiveExpansionForRule(
  std::vector<std::string>& fields,
  const std::string& prefix,
  const std::string& rule);

}
}

#endif
