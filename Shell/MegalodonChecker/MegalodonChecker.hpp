#ifndef __MEGALODON_CHECKER__
#define __MEGALODON_CHECKER__

#include "Kernel/InferenceStore.hpp"
#include "Shell/InferenceReplay.hpp"

#include <ostream>
#include <map>
#include <string>
#include <vector>

namespace Shell {

class MegalodonChecker : public Kernel::InferenceStore::AbstractProofPrinter {
public:
  MegalodonChecker(std::ostream& out, Kernel::InferenceStore* is);
  ~MegalodonChecker() override;

  void print() override;
  void printStep(Kernel::Unit* u) override;

private:
  struct Hypothesis {
    std::string proposition;
    std::string proof;
    Kernel::Formula* formula;
  };

  bool inferenceNeedsReplayInformation(const Kernel::InferenceRule& rule) const;
  void printMegalodonSourceCandidate();
  bool tryMegalodonSource(Kernel::Formula* formula, std::vector<std::string>& lines);
  bool formulaToMegalodon(Kernel::Formula* formula, std::string& result);
  bool literalToMegalodon(Kernel::Literal* literal, std::string& result);
  bool termToMegalodon(Kernel::TermList term, std::string& result);
  bool sortToMegalodon(Kernel::TermList sort, std::string& result);
  bool proofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp);
  bool quantifiedPropHypothesis(Kernel::Formula* formula, std::string& binderName, Kernel::Formula*& body);
  std::string functionName(unsigned functor);
  std::string predicateName(unsigned predicate);
  std::string functionDeclaration(unsigned functor, const std::string& name);
  std::string predicateDeclaration(unsigned predicate, const std::string& name);
  std::string variableName(unsigned var) const;
  std::string parenthesize(const std::string& value) const;
  std::string quote(const std::string& value) const;
  std::string parents(Kernel::Unit* u) const;
  std::string unitKind(Kernel::Unit* u) const;

  InferenceReplayer _replayer;
  std::map<unsigned, std::string> _functions;
  std::map<unsigned, std::string> _predicates;
  bool _usesEquality = false;
};

} // namespace Shell

#endif // __MEGALODON_CHECKER__
