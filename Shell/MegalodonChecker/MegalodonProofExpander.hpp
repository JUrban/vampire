#ifndef __MEGALODON_PROOF_EXPANDER__
#define __MEGALODON_PROOF_EXPANDER__

#include "Kernel/Term.hpp"

#include <cstddef>
#include <string>
#include <utility>
#include <vector>

namespace Shell {
namespace MegalodonProofExpander {

using Environment = std::vector<std::pair<unsigned, Kernel::TermList>>;

struct Application {
  unsigned functionSymbol = 0;
  Kernel::TermList term;
};

struct Step {
  std::string id;
  std::vector<std::string> parentIds;
  Environment parentSubstitution;
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

bool expandGroundProof(
  const std::vector<Step>& steps,
  const std::string& finalStep,
  Expansion& result,
  std::string& error);

}
}

#endif
