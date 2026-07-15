#ifndef __MEGALODON_CHECKER__
#define __MEGALODON_CHECKER__

#include "Kernel/InferenceStore.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/InferenceReplay.hpp"

#include <cstddef>
#include <ostream>
#include <map>
#include <set>
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
  bool certificateTermJson(Kernel::TermList term, std::string& result);
  bool certificateAtomJson(Kernel::Literal* literal, std::string& result);
  bool certificateLiteralJson(Kernel::Literal* literal, std::string& result);
  bool certificateSplitLiteralJson(unsigned split, std::string& result);
  bool appendCertificateSplitLiteralsJson(Kernel::Clause* clause, std::vector<std::string>& literals);
  bool appendCertificateClauseLiteralsJson(Kernel::Clause* clause, std::vector<std::string>& literals);
  bool appendCertificateSubstitutedClauseLiteralsPreservingEqualityJson(Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals);
  bool certificateClauseJson(Kernel::Clause* clause, std::string& result);
  bool certificateSubstitutedEqualityLiteralJson(Kernel::Literal* literal, const Kernel::Substitution& substitution, bool swapEquality, std::string& result);
  bool certificateSubstitutedLiteralPreservingEqualityJson(Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& result);
  bool certificateSubstitutedClausePreservingEqualityJson(Kernel::Clause* clause, const Kernel::Substitution& substitution, std::string& result);
  bool certificateDefinitionInputStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateResolveStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateEqualityResolutionStepJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateTruthConflictResolutionStepJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateTrivialInequalityRemovalStepsJson(Kernel::Unit* unit, std::string& result);
  bool certificateFactorStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateEqualityFactoringStepJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateParamodulateStepJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateParamodulateThenSymmetryStepsJson(Kernel::Unit* unit, std::string& result);
  bool certificateDemodulationStepsJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateUnitResultingResolutionStepsJson(Kernel::Unit* unit, std::string& result);
  bool certificateSubstitutedResolutionStepsJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateSatSubsumptionResolutionStepsJson(Kernel::Unit* unit, std::string& result);
  bool certificateExtensionalityResolutionStepsJson(Kernel::Unit* unit, std::string& result);
  bool certificateCondensationStepsJson(Kernel::Unit* unit, std::string& result);
  bool certificateAvatarRefutationStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateDefinitionRewriteChainStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateBoolSimplificationStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateInequalitySplittingStepJson(Kernel::Unit* unit, std::string& result);
  bool certificateSuperpositionStepsJson(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
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
  std::string sortSymbolSuffix(const std::string& sort) const;
  std::string equalityNameForSort(const std::string& sort) const;
  std::string equalityDefinition(const std::string& sort) const;
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
  std::string sexprQuote(const std::string& value) const;
  bool certificateTypeSexpr(Kernel::TermList sort, std::string& result);
  bool certificateTermSexpr(Kernel::TermList term, std::string& result);
  bool certificateAtomSexpr(Kernel::Literal* literal, std::string& result);
  bool certificateLiteralSexpr(Kernel::Literal* literal, std::string& result);
  bool certificateSplitLiteralSexpr(unsigned split, std::string& result);
  bool appendCertificateSplitLiteralsSexpr(Kernel::Clause* clause, std::vector<std::string>& literals);
  bool appendCertificateClauseLiteralsSexpr(Kernel::Clause* clause, std::vector<std::string>& literals);
  bool certificateClauseSexpr(Kernel::Clause* clause, std::string& result);
  bool certificateSubstitutionSexpr(const Kernel::Substitution& substitution, std::string& result);
  bool certificateSubstitutionSexprForClause(
    const Kernel::Substitution& substitution,
    Kernel::Clause* parent,
    std::string& result);
  bool certificateRewriteTermAtMegalodonPosition(Kernel::TermList term, Kernel::TermList needle, Kernel::TermList replacement, std::vector<unsigned>& position, Kernel::TermList& rewritten);
  bool certificateRewriteLiteralAtMegalodonPosition(Kernel::Literal* literal, Kernel::TermList needle, Kernel::TermList replacement, std::vector<unsigned>& position, Kernel::Literal*& rewritten);
  bool certificateRewriteLiteralAtMegalodonPosition(Kernel::Literal* literal, Kernel::TermList needle, Kernel::TermList replacement, std::vector<unsigned>& position, std::string& rendered);
  std::string certificatePositionSexpr(const std::vector<unsigned>& position) const;
  bool certificateSource(Kernel::Unit* unit, std::string& result);
  bool certificateFormulaTermSexpr(Kernel::Formula* formula, std::string& result);
  bool certificatePredicateDefinitionSymbol(Kernel::Formula* formula, std::string& result);
  bool certificateFormulaNativeLiteralSexpr(Kernel::Formula* formula, bool& positive, std::string& atom);
  bool certificateFormulaNativeLiteralSexpr(Kernel::Formula* formula, std::string& result);
  bool certificateInputStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFormulaInputStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFormulaTermInputStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFormulaCopyStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFormulaTermCopyStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateRectifyFormulaStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFoolBoolStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFoolFormulaStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateEnnfFormulaStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateSkolemFormulaStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateCnfLiteralStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateCnfFormulaClauseStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificatePredicateDefinitionStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificatePredicateDefinitionFoldStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateDefinitionInputStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateInequalitySplittingNameIntroductionStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateInequalitySplittingStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateExtensionalityResolutionStepsSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateAvatarComponentStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateAvatarSplitStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateAvatarContradictionStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateAvatarRefutationStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateCondensationStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateDefinitionRewriteStepsSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateDefinitionFoldingStepsSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFoolExhaustivenessStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFoolDistinctnessStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateBoolSimplificationStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateUnitResultingResolutionStepsSexpr(Kernel::Unit* unit, std::string& result, bool recordSyntheticMetadata = false);
  bool certificateNativeStepSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateResolveStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateSubstitutedResolutionStepsSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateSatSubsumptionResolutionStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateFactorStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateTrivialInequalityRemovalStepsSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateEqualityResolutionStepSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateEqualityFactoringStepSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateTruthConflictStepSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateForwardSubsumptionDemodulationStepsSexpr(Kernel::Unit* unit, std::string& result);
  bool certificateDemodulationStepsSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateParamodulateStepSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateSuperpositionStepsSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  bool certificateSuperpositionStepSexpr(Kernel::Unit* unit, const InferenceRecorder::InferenceInformation* replayInfo, std::string& result);
  std::string certificateJsonWithStepIds(Kernel::Unit* unit, const std::string& certificateJson);
  std::string certificateFallbackSourceJson(Kernel::Unit* unit);
  void printMegalodonCertificateJson() const;
  void printMegalodonCertificateNativeSexpr() const;
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
  std::map<unsigned, Kernel::Clause*> _avatarComponentBySatVar;
  std::set<std::string> _usedSymbolNames;
  bool _usesEquality = false;
  std::set<std::string> _equalitySorts;
  bool _usesConjunction = false;
  bool _usesFalse = false;
  bool _usesDisjunction = false;
  bool _usesSetExists = false;
  bool _usesTrue = false;
  bool _usesPropEquality = false;
  bool _renderingReplayExtra = false;
  unsigned _proofSearchCalls = 0;
  unsigned _renderDepth = 0;
  std::vector<std::string> _certificateSteps;
  std::vector<std::string> _certificateNativeMetadata;
  std::vector<std::string> _certificateNativeSteps;
  std::set<unsigned> _certificateNativeStepIds;
};

} // namespace Shell

#endif // __MEGALODON_CHECKER__
