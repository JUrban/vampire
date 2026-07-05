#ifndef __MEGALODON_CHECKER__
#define __MEGALODON_CHECKER__

#include "Kernel/InferenceStore.hpp"
#include "Shell/InferenceReplay.hpp"

#include <ostream>
#include <string>

namespace Shell {

class MegalodonChecker : public Kernel::InferenceStore::AbstractProofPrinter {
public:
  MegalodonChecker(std::ostream& out, Kernel::InferenceStore* is);
  ~MegalodonChecker() override;

  void print() override;
  void printStep(Kernel::Unit* u) override;

private:
  bool inferenceNeedsReplayInformation(const Kernel::InferenceRule& rule) const;
  std::string quote(const std::string& value) const;
  std::string parents(Kernel::Unit* u) const;
  std::string unitKind(Kernel::Unit* u) const;

  InferenceReplayer _replayer;
};

} // namespace Shell

#endif // __MEGALODON_CHECKER__
