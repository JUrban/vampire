#ifndef __MEGALODON_CHECKER__
#define __MEGALODON_CHECKER__

#include "Kernel/InferenceStore.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"

#include <cstddef>
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
  void printMegalodonClaimSkeleton();
  bool tryMegalodonSource(Kernel::Formula* formula, const std::vector<Hypothesis>& assumptions, std::vector<std::string>& lines);
  bool tryMegalodonClaimSkeleton(Kernel::Formula* formula, const std::vector<Hypothesis>& assumptions, std::vector<std::string>& lines);
  bool formulaToMegalodon(Kernel::Formula* formula, std::string& result);
  bool formulaToMegalodon(Kernel::Formula* formula, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result);
  bool conjunctionToMegalodon(const std::vector<Kernel::Formula*>& conjuncts, std::size_t begin, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result);
  std::string existentialNameForSort(const std::string& sort) const;
  bool literalToMegalodon(Kernel::Literal* literal, std::string& result);
  bool skeletonLiteralToMegalodon(Kernel::Literal* literal, std::string& result);
  bool skeletonSplitLiteralToMegalodon(unsigned split, std::string& result);
  bool skeletonClauseToMegalodon(Kernel::Clause* clause, std::string& result);
  bool skeletonDisjunctionToMegalodon(const std::vector<std::string>& literals, std::string& result);
  bool signedNameToMegalodon(const std::string& name, std::string& result);
  std::string recoverMegalodonSymbolName(const std::string& tptpName, const std::string& fallbackPrefix);
  std::string decodeMegalodonTptpName(const std::string& tptpName) const;
  std::string sanitizeMegalodonName(const std::string& name, const std::string& fallbackPrefix) const;
  bool termToMegalodon(Kernel::TermList term, std::string& result);
  bool termToMegalodon(Kernel::TermList term, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result);
  bool termToMegalodonReplacing(Kernel::TermList term, Kernel::TermList needle, const std::string& replacement, std::string& result);
  bool formulaToMegalodonReplacing(Kernel::Formula* formula, Kernel::TermList needle, const std::string& replacement, std::string& result);
  bool sortToMegalodon(Kernel::TermList sort, std::string& result);
  bool proofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp);
  bool conjunctionIntroductionProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp);
  bool conjunctionIntroductionProofTerm(const std::vector<Kernel::Formula*>& conjuncts, std::size_t begin, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp);
  bool conjunctionProjectionProofTerm(Kernel::Formula* source, const std::string& sourceProof, Kernel::Formula* goal, std::string& result);
  bool conjunctionProjectionProofTerm(const std::vector<Kernel::Formula*>& conjuncts, std::size_t begin, const std::string& sourceProof, const std::string& goalText, std::string& result);
  bool equalityRewriteProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result);
  bool equalitySimplificationProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp);
  bool equalityRewriteScript(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::vector<std::string>& lines);
  bool equalityNormalizationScript(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::vector<std::string>& lines);
  bool hypothesisApplicationProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result);
  bool instantiatedProofTerm(Kernel::Formula* goal, const std::map<unsigned, Kernel::TermList>& substitution, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned depth);
  bool premiseProofTerm(Kernel::Formula* premise, std::map<unsigned, Kernel::TermList>& substitution, const std::vector<unsigned>& variables, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned depth);
  void implicationChain(Kernel::Formula* formula, std::vector<Kernel::Formula*>& premises, Kernel::Formula*& conclusion) const;
  bool formulaMatchesAfterReplacement(Kernel::Formula* source, Kernel::Formula* target, Kernel::TermList needle, Kernel::TermList replacement, bool& replaced);
  bool termMatchesAfterReplacement(Kernel::TermList source, Kernel::TermList target, Kernel::TermList needle, Kernel::TermList replacement, bool& replaced);
  bool formulaMatchesAfterPatternReplacement(Kernel::Formula* source, Kernel::Formula* target, Kernel::TermList pattern, Kernel::TermList replacement, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution);
  bool termMatchesAfterPatternReplacement(Kernel::TermList source, Kernel::TermList target, Kernel::TermList pattern, Kernel::TermList replacement, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution);
  bool rewriteFormulaOnce(Kernel::Formula* source, Kernel::TermList pattern, Kernel::TermList replacement, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution, Kernel::Formula*& result);
  bool substituteTerm(Kernel::TermList term, const std::map<unsigned, Kernel::TermList>& substitution, Kernel::TermList& result);
  bool rewriteTermOnce(Kernel::TermList term, Kernel::TermList pattern, Kernel::TermList replacement, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution, Kernel::TermList& result);
  bool appendEqualityRewriteStep(const Hypothesis& hypothesis, const std::vector<unsigned>& variables, Kernel::TermList lhs, Kernel::TermList rhs, bool forward, const std::map<unsigned, Kernel::TermList>& substitution, unsigned& nextLabel, std::vector<std::string>& lines);
  bool recordEqualitySort(Kernel::TermList sort);
  std::string equalityDefinition() const;
  bool matchFormula(Kernel::Formula* pattern, Kernel::Formula* target, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution);
  bool matchTerm(Kernel::TermList pattern, Kernel::TermList target, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution);
  bool matchFormula(Kernel::Formula* pattern, Kernel::Formula* target, const std::map<unsigned, Kernel::TermList>& targetSubstitution, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution);
  bool matchTerm(Kernel::TermList pattern, Kernel::TermList target, const std::map<unsigned, Kernel::TermList>& targetSubstitution, const std::vector<unsigned>& variables, std::map<unsigned, Kernel::TermList>& substitution);
  bool equalityLiteral(Kernel::Formula* formula, Kernel::TermList& lhs, Kernel::TermList& rhs);
  bool equalityProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result);
  bool quantifiedPropHypothesis(Kernel::Formula* formula, std::string& binderName, Kernel::Formula*& body);
  std::string propEqualityDefinition() const;
  std::string functionName(unsigned functor);
  std::string predicateName(unsigned predicate);
  std::string functionDeclaration(unsigned functor, const std::string& name);
  std::string predicateDeclaration(unsigned predicate, const std::string& name);
  std::string variableName(unsigned var) const;
  std::string parenthesize(const std::string& value) const;
  std::string quote(const std::string& value) const;
  std::string parents(Kernel::Unit* u) const;
  std::string unitKind(Kernel::Unit* u) const;
  std::string replayKind(const Kernel::InferenceRule& rule) const;
  void recordStepSymbols(Kernel::Unit* u);
  void printMegalodonSymbolDeclarations();
  void printStepVariableSorts(Kernel::Unit* u);
  void printReplaySubstitutions(Kernel::Unit* u, const InferenceRecorder::InferenceInformation* info);
  void printReplayExtra(Kernel::Unit* u, const InferenceRecorder::InferenceInformation* info);
  std::string substitutedClauseText(Kernel::Clause* clause, const Kernel::Substitution& substitution) const;

  InferenceReplayer _replayer;
  std::map<unsigned, std::string> _functions;
  std::map<unsigned, std::string> _predicates;
  std::set<std::string> _usedSymbolNames;
  bool _usesEquality = false;
  std::string _equalitySort;
  bool _usesConjunction = false;
  bool _usesFalse = false;
  bool _usesDisjunction = false;
  bool _usesSetExists = false;
  bool _usesTrue = false;
  bool _usesPropEquality = false;
  bool _renderingReplayExtra = false;
  unsigned _proofSearchCalls = 0;
  unsigned _renderDepth = 0;
};

} // namespace Shell

#endif // __MEGALODON_CHECKER__
