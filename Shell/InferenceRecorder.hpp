#ifndef __INFERENCE_RECORDER__
#define __INFERENCE_RECORDER__

#include "Forwards.hpp"

#include "Indexing/Index.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/RobSubstitution.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Shell/EqResWithDeletion.hpp"
#include <memory>
#include <map>
#include <unordered_map>
#include <vector>
#include <set>

namespace Shell {
class InferenceRecorder {
public:
  class GenericInferenceInformation {
    public:
  };

  class InferenceInformation : public GenericInferenceInformation {
  public:
    Kernel::Clause *conclusion;
    std::vector<Kernel::Clause *> premises;
    std::vector<Kernel::Substitution> substitutionForBanksSub;
    Kernel::Substitution conclusionVariableRenaming;
    bool hasDemodulationRewrite = false;
    Kernel::TermList demodulationRuleLhs;
    Kernel::TermList demodulationRuleRhs;
    Kernel::TermList demodulationRedex;
    Kernel::TermList demodulationReplacement;
    bool hasSuperpositionSelection = false;
    Kernel::Clause* superpositionTargetParent = nullptr;
    Kernel::Literal* superpositionTargetLiteral = nullptr;
    unsigned superpositionTargetLiteralIndex = 0;
    Kernel::TermList superpositionTargetTerm;
    Kernel::Clause* superpositionEqualityParent = nullptr;
    Kernel::Literal* superpositionEqualityLiteral = nullptr;
    unsigned superpositionEqualityLiteralIndex = 0;
    Kernel::TermList superpositionEqualityLhs;
    Kernel::TermList superpositionEqualityRhs;
    bool superpositionEqualityIsResult = false;
    bool superpositionSimultaneous = false;
  };

  class RectifyInferenceExtra : public GenericInferenceInformation {
    public:
      struct Renaming {
        Kernel::Formula* sourceFormula = nullptr;
        Kernel::Formula* resultFormula = nullptr;
        Kernel::Substitution quantifiedVariableSubstitution;
        std::map<unsigned, unsigned> ambientVariableRenaming;
      };
      std::vector<Renaming> renamings;
      Kernel::Formula* sourceFormula = nullptr;
      Kernel::Formula* resultFormula = nullptr;
      std::map<unsigned, unsigned> freeVariableRenaming;
  };

  class EnnfInferenceExtra : public GenericInferenceInformation {
    public:
      struct TraceNode {
        Kernel::Formula* sourceFormula = nullptr;
        Kernel::Formula* resultFormula = nullptr;
        bool polarity = true;
        std::vector<std::size_t> children;
      };
      Kernel::Formula* sourceFormula = nullptr;
      Kernel::Formula* resultFormula = nullptr;
      std::vector<TraceNode> trace;
      std::vector<std::size_t> activeTrace;
  };

  class SkolemInferenceExtra : public GenericInferenceInformation {
    public:
      struct ScopedVariable {
        unsigned variable = 0;
        Kernel::TermList sort;
      };
      struct Witness {
        bool typeVariable = false;
        unsigned symbol = 0;
        unsigned replacedVariable = 0;
        Kernel::TermList replacedSort;
        Kernel::TermList witnessTerm;
        Kernel::Formula* stageSourceFormula = nullptr;
        Kernel::Formula* stageTargetFormula = nullptr;
        std::vector<ScopedVariable> dependencies;
      };
      struct Branch {
        Kernel::Formula* sourceFormula = nullptr;
        Kernel::Formula* targetFormula = nullptr;
        std::vector<std::size_t> path;
        std::vector<std::string> contextProgram;
        std::vector<ScopedVariable> ambient;
        std::vector<ScopedVariable> context;
        std::vector<Witness> witnesses;
      };
      Kernel::Formula* sourceFormula = nullptr;
      Kernel::Formula* resultFormula = nullptr;
      std::vector<Branch> branches;
  };

  // Returns the singleton instance (lazily initialized, thread-safe)
  static InferenceRecorder *instance();
  // Optional: destroy the singleton (if you need controlled teardown)
  // static void destroyInstance();

  void resolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::ResultSubstitutionSP &recordedSubst);

  void superposition(
    unsigned int id,
    Kernel::Clause* conclusion,
    const std::vector<Kernel::Clause*>& premises,
    const Indexing::ResultSubstitutionSP& recordedSubst,
    bool eqIsResult,
    Kernel::Clause* targetParent,
    Kernel::Literal* targetLiteral,
    Kernel::TermList targetTerm,
    Kernel::Clause* equalityParent,
    Kernel::Literal* equalityLiteral,
    Kernel::TermList equalityLhs,
    Kernel::TermList equalityRhs,
    bool simultaneous);

  void factoring(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);

  void equalityResolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);
  
  void equalityResolutionDeletion(unsigned int id, Clause *conclusion, Clause *premise, EqResWithDeletion *appl);
  
  void equalityFactoring(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const Indexing::RobSubstitution &recordedSubst);
  
  void forwardDemodulation(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const SubstApplicator *appl, const Indexing::DemodulatorData *data,
                           TermList rhsS, TypedTermList trm);

  void backwardDemodulation(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const SubstApplicator &appl);

  void rectify(
    Formula* f,
    Formula* newFormula,
    VSList* vs,
    Substitution renaming,
    std::set<unsigned> unusedVars,
    const std::map<unsigned, unsigned>& ambientVariableRenaming);

  void startRectifyRecording(){
    _lastInferenceId = 0;
    _currentRecording = std::make_unique<RectifyInferenceExtra>();
  }

  void endRectifyRecording(
      unsigned int id,
      Kernel::Formula* sourceFormula,
      Kernel::Formula* resultFormula,
      const std::map<unsigned, unsigned>& freeVariableRenaming){
    auto* info = static_cast<RectifyInferenceExtra*>(_currentRecording.get());
    info->sourceFormula = sourceFormula;
    info->resultFormula = resultFormula;
    info->freeVariableRenaming = freeVariableRenaming;
    _lastInferenceId = id;
    _inferences[id] = std::move(_currentRecording);
  }

  void discardRectifyRecording(){
    _currentRecording.reset();
    _lastInferenceId = 0;
  }

  void startEnnfRecording(Kernel::Formula* sourceFormula);
  std::size_t startEnnfTraceNode(Kernel::Formula* sourceFormula, bool polarity);
  void finishEnnfTraceNode(std::size_t index, Kernel::Formula* resultFormula);
  void endEnnfRecording(
    unsigned int id,
    Kernel::Formula* sourceFormula,
    Kernel::Formula* resultFormula);
  void discardEnnfRecording();

  void startSkolemRecording(Kernel::Formula* sourceFormula);
  void recordSkolemBranch(
    Kernel::Formula* sourceFormula,
    Kernel::Formula* targetFormula,
    const std::vector<std::size_t>& path,
    const std::vector<std::string>& contextProgram,
    const std::vector<SkolemInferenceExtra::ScopedVariable>& ambient,
    const std::vector<SkolemInferenceExtra::ScopedVariable>& context,
    const std::vector<SkolemInferenceExtra::Witness>& witnesses);
  void endSkolemRecording(
    unsigned int id,
    Kernel::Formula* sourceFormula,
    Kernel::Formula* resultFormula);
  void discardSkolemRecording();

  bool reassignLastInferenceInformation(unsigned int id){
    auto source = _inferences.find(_lastInferenceId);
    if (source == _inferences.end()) {
      return false;
    }
    if (_lastInferenceId != id) {
      _inferences[id] = std::move(source->second);
      _inferences.erase(source);
    }
    _lastInferenceId = id;
    return true;
  }

  //void unitResultingResolution(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Unit *> &premises, const std::vector<Indexing::ResultSubstitutionSP> &substitutions);

  void setCurrentGoal(Kernel::Clause *goal)
  {
    _currentGoal = goal;
    _lastInferenceId = 0;
  }

  const InferenceInformation *getLastRecordedInferenceInformation() const
  {
    auto it = _inferences.find(_lastInferenceId);
    if (it != _inferences.end())
      return static_cast<const InferenceInformation *>(it->second.get());
    return nullptr;
  }

  const GenericInferenceInformation *getGenericLastInferenceInformation() const
  {
    auto it = _inferences.find(_lastInferenceId);
    if (it != _inferences.end())
      return it->second.get();
    return nullptr;
  }

  const GenericInferenceInformation *getGenericInferenceInformation(unsigned int id) const
  {
    auto it = _inferences.find(id);
    if (it != _inferences.end())
      return it->second.get();
    return nullptr;
  }

  ~InferenceRecorder();

  // non-copyable, non-movable
  InferenceRecorder(const InferenceRecorder &) = delete;
  InferenceRecorder &operator=(const InferenceRecorder &) = delete;
  InferenceRecorder(InferenceRecorder &&) = delete;
  InferenceRecorder &operator=(InferenceRecorder &&) = delete;
  
private:
  InferenceRecorder();

  static InferenceRecorder *_inst;

  bool isSameAsProofStep(Kernel::Clause *c, Kernel::Clause *goal, const std::vector<Kernel::Clause *> &premises, std::unordered_map<unsigned int, unsigned int> &outVarMap);

  template <typename T>
  void populateSubstitutionsGen(std::vector<Kernel::Substitution> &substMap,
                                const std::unordered_map<unsigned int, unsigned int> &varMap,
                                const std::vector<Clause *> premises,
                                const T &recordedSubst,
                                std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    // In case the variables are mapped differently, we adjust the term mapping to the original goal
    Substitution variableSubst = Substitution();
    for (auto [var, mappedVar] : varMap) {
      variableSubst.bind(var, TermList::var(mappedVar));
    }
    substMap.resize(premises.size());
    
    for (size_t bank = 0; bank < premises.size(); bank++) {
      unsigned int highestVar = 0;
      //std::cout << premises[bank]->toString() << std::endl;
      auto iter = premises[bank]->getVariableIterator();
      while (iter.hasNext()) {
        unsigned int var = variableSubst.apply(iter.next()).var();
        if (var > highestVar) {
          highestVar = var;
        }
      }
      for (unsigned v = 0; v <= highestVar; v++) {
        TermList x = applyFunc(recordedSubst, TermList::var(v), bank);
        substMap[bank].bind(v,
                            SubstHelper::apply(x,
                                               variableSubst));
      }
      //std::cout << "Substitution for bank " << bank << ": " << substMap[bank] << std::endl;
    }
  }

  template <typename T>
  void populateSubstitutionsMergeOneBank(std::vector<Kernel::Substitution> &substMap,
                                     const std::unordered_map<unsigned int, unsigned int> &varMap,
                                     const std::vector<Clause *> premises,
                                     const T &recordedSubst,
                                     std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    // In case the variables are mapped differently, we adjust the term mapping to the original goal
    Substitution variableSubst = Substitution();
    for (auto [var, mappedVar] : varMap) {
      variableSubst.bind(var, TermList::var(mappedVar));
    }

    substMap.resize(1);
    long highestVar = -1;
    for (size_t bank = 0; bank < premises.size(); bank++) {
      auto iter = premises[bank]->getVariableIterator();
      while (iter.hasNext()) {
        unsigned int var = iter.next();
        if (var > highestVar) {
          highestVar = var;
        }
      }
    }
    for (unsigned v = 0; v <= highestVar; v++) {
      TermList x = applyFunc(recordedSubst, TermList::var(v), 0);
      substMap[0].bind(v,
                         SubstHelper::apply(x,
                                            variableSubst));
    }
  }

  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> premises,
                             const RobSubstitution &recordedSubst);

  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> premises,
                             const Indexing::ResultSubstitutionSP &recordedSubst);

  void populateSubstitutions(std::vector<Kernel::Substitution> &substMap,
                             const std::unordered_map<unsigned int, unsigned int> &varMap,
                             const std::vector<Kernel::Clause *> premises,
                             const SubstApplicator &recordedSubst);

  template <typename T>
  void recordGenericSubstitutionInference(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst, std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (isSameAsProofStep(conclusion, _currentGoal, premises, varMap)) {
      std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
      info->conclusion = conclusion;
      info->premises = premises;
      for (const auto& [variable, mappedVariable] : varMap) {
        info->conclusionVariableRenaming.bind(
          variable,
          Kernel::TermList::var(mappedVariable));
      }
      populateSubstitutionsGen<T>(info->substitutionForBanksSub, varMap, premises, recordedSubst, applyFunc);
      _inferences[id] = std::move(info);
      _lastInferenceId = id;
    }
    // Do nothing if not same as proof step
  };

  template <typename T>
  void recordGenericSubstitutionInference(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst)
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (isSameAsProofStep(conclusion, _currentGoal, premises, varMap)) {
      // std::cout << conclusion->toNiceString() << std::endl;
      // std::cout << _currentGoal->toNiceString() << std::endl;
      std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
      info->conclusion = conclusion;
      info->premises = premises;
      for (const auto& [variable, mappedVariable] : varMap) {
        info->conclusionVariableRenaming.bind(
          variable,
          Kernel::TermList::var(mappedVariable));
      }
      populateSubstitutions(info->substitutionForBanksSub, varMap, premises, recordedSubst);
      // for(auto& subst : info->substitutionForBanksSub){
      //	std::cout << subst << std::endl;
      // }
      _inferences[id] = std::move(info);
      _lastInferenceId = id;
    }
    // Do nothing if not same as proof step
  };

  template <typename T>
  void recordGenericSubstitutionToOneBank(unsigned int id, Kernel::Clause *conclusion, const std::vector<Kernel::Clause *> &premises, const T &recordedSubst, std::function<TermList(const T &, const TermList &, size_t)> applyFunc)
  {
    std::unordered_map<unsigned int, unsigned int> varMap;
    if (isSameAsProofStep(conclusion, _currentGoal, premises,varMap)) {
      std::unique_ptr<InferenceInformation> info = std::make_unique<InferenceInformation>();
      info->conclusion = conclusion;
      info->premises = premises;
      for (const auto& [variable, mappedVariable] : varMap) {
        info->conclusionVariableRenaming.bind(
          variable,
          Kernel::TermList::var(mappedVariable));
      }
      populateSubstitutionsMergeOneBank<T>(info->substitutionForBanksSub, varMap, premises, recordedSubst, applyFunc);
      _inferences[id] = std::move(info);
      _lastInferenceId = id;
    }
    // Do nothing if not same as proof step
  };

  

  Kernel::Clause *_currentGoal = nullptr;
  std::unordered_map<unsigned int, std::unique_ptr<GenericInferenceInformation>> _inferences;
  unsigned int _lastInferenceId = 0;
  std::unique_ptr<GenericInferenceInformation> _currentRecording = nullptr;
};
} // namespace Shell

#endif // __INFERENCE_RECORDER__
