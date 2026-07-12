#include "MegalodonChecker.hpp"

#include "Forwards.hpp"
#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/EqHelper.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Matcher.hpp"
#include "Kernel/MLVariant.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/TermIterators.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/SharedSet.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Options.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/TweeGoalTransformation.hpp"

#include <algorithm>
#include <cctype>
#include <functional>
#include <set>
#include <sstream>
#include <utility>
#include <vector>

namespace Shell {

MegalodonChecker::MegalodonChecker(std::ostream& out, Kernel::InferenceStore* is)
  : AbstractProofPrinter(out, is), _replayer(out)
{
  env.options->set("code_tree_subsumption", "off");
  _replayer.makeInferenceEngine(this->_is->ordering);
}

MegalodonChecker::~MegalodonChecker()
{
  env.options->set("code_tree_subsumption", "on");
}

bool MegalodonChecker::inferenceNeedsReplayInformation(const Kernel::InferenceRule& rule) const
{
  switch (rule) {
    case Kernel::InferenceRule::RESOLUTION:
    case Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
    case Kernel::InferenceRule::EQUALITY_RESOLUTION:
    case Kernel::InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    case Kernel::InferenceRule::EQUALITY_FACTORING:
    case Kernel::InferenceRule::SUPERPOSITION:
    case Kernel::InferenceRule::FORWARD_DEMODULATION:
    case Kernel::InferenceRule::BACKWARD_DEMODULATION:
      return true;
    default:
      return false;
  }
}

std::string MegalodonChecker::replayKind(const Kernel::InferenceRule& rule) const
{
  switch (rule) {
    case Kernel::InferenceRule::RESOLUTION:
      return "resolution";
    case Kernel::InferenceRule::FACTORING:
      return "factoring";
    case Kernel::InferenceRule::EQUALITY_RESOLUTION:
    case Kernel::InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
      return "equality_resolution";
    case Kernel::InferenceRule::EQUALITY_FACTORING:
      return "equality_factoring";
    case Kernel::InferenceRule::SUPERPOSITION:
      return "superposition";
    case Kernel::InferenceRule::FORWARD_DEMODULATION:
      return "forward_demodulation";
    case Kernel::InferenceRule::BACKWARD_DEMODULATION:
      return "backward_demodulation";
    case Kernel::InferenceRule::RECTIFY:
      return "rectify";
    case Kernel::InferenceRule::REMOVE_DUPLICATE_LITERALS:
    case Kernel::InferenceRule::REORIENT_EQUATIONS:
    case Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL:
    case Kernel::InferenceRule::REORDER_LITERALS:
    case Kernel::InferenceRule::EVALUATION:
      return "generic_clause";
    case Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION:
      return "subsumption_resolution";
    case Kernel::InferenceRule::DEFINITION_UNFOLDING:
    case Kernel::InferenceRule::DEFINITION_FOLDING_TWEE:
    case Kernel::InferenceRule::DEFINITION_FOLDING_PRED:
      return "definition_rewrite";
    case Kernel::InferenceRule::CLAUSIFY:
      return "cnf";
    case Kernel::InferenceRule::FOOL_ELIMINATION:
      return "fool";
    case Kernel::InferenceRule::NNF:
    case Kernel::InferenceRule::ENNF:
    case Kernel::InferenceRule::FLATTEN:
    case Kernel::InferenceRule::REDUCE_FALSE_TRUE:
    case Kernel::InferenceRule::THEORY_NORMALIZATION:
    case Kernel::InferenceRule::BOOL_SIMP:
      return "normal_form";
    case Kernel::InferenceRule::SKOLEMIZE:
      return "skolemize";
    case Kernel::InferenceRule::AVATAR_COMPONENT:
      return "avatar_component";
    case Kernel::InferenceRule::AVATAR_REFUTATION:
    case Kernel::InferenceRule::AVATAR_REFUTATION_SMT:
      return "avatar_refutation";
    case Kernel::InferenceRule::AVATAR_CONTRADICTION_CLAUSE:
      return "avatar_contradiction";
    case Kernel::InferenceRule::AVATAR_SPLIT_CLAUSE:
      return "avatar_split";
    case Kernel::InferenceRule::UNIT_RESULTING_RESOLUTION:
      return "unit_resulting_resolution";
    default:
      return "generic";
  }
}

std::string MegalodonChecker::quote(const std::string& value) const
{
  std::ostringstream out;
  out << '"';
  for (char ch : value) {
    switch (ch) {
      case '\\':
        out << "\\\\";
        break;
      case '"':
        out << "\\\"";
        break;
      case '\n':
        out << "\\n";
        break;
      case '\r':
        out << "\\r";
        break;
      case '\t':
        out << "\\t";
        break;
      default:
        out << ch;
        break;
    }
  }
  out << '"';
  return out.str();
}

std::string MegalodonChecker::substitutedClauseText(Kernel::Clause* clause, const Kernel::Substitution& substitution) const
{
  std::ostringstream out;
  out << "cnf(u" << clause->number() << "_subst,axiom,\n    ";
  if (clause->isEmpty()) {
    out << "$false";
  } else {
    bool first = true;
    for (Kernel::Literal* literal : *clause) {
      if (!first) {
        out << " | ";
      }
      first = false;
      out << Kernel::SubstHelper::apply(literal, substitution)->toString();
    }
  }
  out << ").\n";
  return out.str();
}

void MegalodonChecker::printReplaySubstitutions(Kernel::Unit* u, const InferenceRecorder::InferenceInformation* info)
{
  if (info == nullptr || info->premises.size() != info->substitutionForBanksSub.size()) {
    return;
  }

  out << "megalodon_step_substitutions(" << u->number() << ",[";
  for (std::size_t i = 0; i < info->premises.size(); ++i) {
    if (i != 0) {
      out << ',';
    }
    out << quote(substitutedClauseText(info->premises[i], info->substitutionForBanksSub[i]));
  }
  out << "]).\n";
}

void MegalodonChecker::printReplayExtra(Kernel::Unit* u, const InferenceRecorder::InferenceInformation* info)
{
  const auto* extra = env.proofExtra.find(u);

  auto termText = [](Kernel::TermList term) {
    std::ostringstream text;
    text << term;
    return text.str();
  };
  auto literalText = [](Kernel::Literal* literal) {
    return literal == nullptr ? std::string() : literal->toString();
  };
  auto withHolPrinting = [&](Options::HPrinting printing, const std::function<std::string()>& render) {
    Options::HPrinting previous = env.options->holPrinting();
    env.options->setHolPrinting(printing);
    std::string text = render();
    env.options->setHolPrinting(previous);
    return text;
  };
  auto termTextWithHolPrinting = [&](Kernel::TermList term, Options::HPrinting printing) {
    return withHolPrinting(printing, [&]() {
      std::ostringstream text;
      text << term;
      return text.str();
    });
  };
  auto literalTextWithHolPrinting = [&](Kernel::Literal* literal, Options::HPrinting printing) {
    if (literal == nullptr) {
      return std::string();
    }
    return withHolPrinting(printing, [&]() {
      return literal->toString();
    });
  };
  auto substitutedClauseTextWithHolPrinting = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, Options::HPrinting printing) {
    return withHolPrinting(printing, [&]() {
      std::ostringstream out;
      out << "cnf(u" << clause->number() << "_subst,axiom,\n    ";
      if (clause->isEmpty()) {
        out << "$false";
      } else {
        bool first = true;
        for (Kernel::Literal* literal : *clause) {
          if (!first) {
            out << " | ";
          }
          first = false;
          out << Kernel::SubstHelper::apply(literal, substitution)->toString();
        }
      }
      out << ").\n";
      return out.str();
    });
  };
  auto substitutionText = [](const Kernel::Substitution& substitution) {
    std::ostringstream text;
    text << substitution;
    return text.str();
  };
  auto addSubstitutedLiteralFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Literal* literal) {
    fields.push_back(prefix + "_substituted=" + literalText(literal));
    if (literal == nullptr) {
      return;
    }
    fields.push_back(prefix + "_substituted_db_indices=" + literalTextWithHolPrinting(literal, Options::HPrinting::DB_INDICES));
    std::string substitutedProposition;
    if (skeletonLiteralToMegalodon(literal, substitutedProposition)) {
      fields.push_back(prefix + "_substituted_proposition=" + substitutedProposition);
    } else if (literal->isEquality()) {
      Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
      std::string equalitySort;
      std::string lhs;
      std::string rhs;
      if (sortToMegalodon(equalityArgumentSort, equalitySort)
        && termToMegalodon(*literal->nthArgument(0), lhs)
        && termToMegalodon(*literal->nthArgument(1), rhs)) {
        if (equalitySort == "prop") {
          _usesPropEquality = true;
          substitutedProposition = "vampire_eq_prop " + parenthesize(lhs) + " " + parenthesize(rhs);
        } else {
          substitutedProposition = lhs + " = " + rhs;
        }
        if (literal->isNegative()) {
          _usesFalse = true;
          substitutedProposition = parenthesize(substitutedProposition) + " -> vampire_false";
        }
        fields.push_back(prefix + "_substituted_proposition=" + substitutedProposition);
      }
    }
  };
  std::vector<Kernel::Clause*> parentClauses;
  for (Kernel::Unit* parent : iterTraits(u->getParents())) {
    if (parent->isClause()) {
      parentClauses.push_back(parent->asClause());
    }
  }
  auto literalPositionInParent = [&](Kernel::Literal* literal, std::size_t parentIndex) -> int {
    if (literal == nullptr) {
      return -1;
    }
    if (parentIndex >= parentClauses.size()) {
      return -1;
    }
    Kernel::Clause* parent = parentClauses[parentIndex];
    for (unsigned literalIndex = 0; literalIndex < parent->length(); ++literalIndex) {
      if ((*parent)[literalIndex] == literal) {
        return static_cast<int>(literalIndex);
      }
    }
    return -1;
  };
  auto literalPosition = [&](Kernel::Literal* literal, int preferredParentIndex) -> std::pair<int, int> {
    if (preferredParentIndex >= 0) {
      int literalIndex = literalPositionInParent(literal, static_cast<std::size_t>(preferredParentIndex));
      if (literalIndex >= 0) {
        return {preferredParentIndex, literalIndex};
      }
    }
    if (literal == nullptr) {
      return {-1, -1};
    }
    for (std::size_t parentIndex = 0; parentIndex < parentClauses.size(); ++parentIndex) {
      int literalIndex = literalPositionInParent(literal, parentIndex);
      if (literalIndex >= 0) {
        return {static_cast<int>(parentIndex), literalIndex};
      }
    }
    return {-1, -1};
  };
  auto addLiteralPositionFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Literal* literal, int preferredParentIndex = -1) {
    auto [parentIndex, literalIndex] = literalPosition(literal, preferredParentIndex);
    if (parentIndex < 0 || literalIndex < 0) {
      return;
    }
    fields.push_back(prefix + "_parent_index=" + std::to_string(parentIndex));
    fields.push_back(prefix + "_literal_index=" + std::to_string(literalIndex));
    fields.push_back(prefix + "_parent_unit=" + std::to_string(parentClauses[parentIndex]->number()));
    if (
      info != nullptr
      && static_cast<std::size_t>(parentIndex) < info->substitutionForBanksSub.size()
      && static_cast<std::size_t>(parentIndex) < info->premises.size()
    ) {
      Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, info->substitutionForBanksSub[parentIndex]);
      addSubstitutedLiteralFields(fields, prefix, substituted);
    }
  };
  auto emit = [&](const std::string& kind, const std::vector<std::string>& fields) {
    out << "megalodon_step_extra(" << u->number() << ',' << quote(kind) << ",[";
    for (std::size_t i = 0; i < fields.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << quote(fields[i]);
    }
    out << "]).\n";
  };
  auto addParentSubstitutionFields = [&](std::vector<std::string>& fields) {
    if (info == nullptr || info->premises.size() != info->substitutionForBanksSub.size()) {
      return;
    }
    for (std::size_t i = 0; i < info->premises.size(); ++i) {
      fields.push_back("parent_" + std::to_string(i) + "_substitution=" + substitutionText(info->substitutionForBanksSub[i]));
      fields.push_back(
        "parent_" + std::to_string(i) + "_substituted_clause="
        + substitutedClauseText(info->premises[i], info->substitutionForBanksSub[i]));
      fields.push_back(
        "parent_" + std::to_string(i) + "_substituted_clause_db_indices="
        + substitutedClauseTextWithHolPrinting(info->premises[i], info->substitutionForBanksSub[i], Options::HPrinting::DB_INDICES));
    }
  };
  auto substitutedClauseToMegalodon = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::string& result) {
    std::vector<std::string> literals;
    literals.reserve(clause->length());
    for (Kernel::Literal* literal : clause->iterLits()) {
      Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
      std::string proposition;
      if (!skeletonLiteralToMegalodon(substituted, proposition)) {
        return false;
      }
      literals.push_back(proposition);
    }
    return skeletonDisjunctionToMegalodon(literals, result);
  };
  auto renderFormulaForExtra = [&](Kernel::Formula* formula, std::string& text) {
    bool usesEquality = _usesEquality;
    std::string equalitySort = _equalitySort;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySort.clear();
    _renderingReplayExtra = true;
    bool ok = formulaToMegalodon(formula, text);
    _usesEquality = usesEquality;
    _equalitySort = equalitySort;
    _usesConjunction = usesConjunction;
    _usesFalse = usesFalse;
    _usesDisjunction = usesDisjunction;
    _usesSetExists = usesSetExists;
    _usesTrue = usesTrue;
    _usesPropEquality = usesPropEquality;
    _renderingReplayExtra = renderingReplayExtra;
    return ok;
  };
  auto renderFormulaForExtraWithSubstitution = [&](Kernel::Formula* formula, Kernel::Substitution substitution, std::string& text) {
    bool usesEquality = _usesEquality;
    std::string equalitySort = _equalitySort;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySort.clear();
    _renderingReplayExtra = true;
    std::map<unsigned, Kernel::TermList> substitutionMap;
    for (auto [variable, term] : iterTraits(substitution.items())) {
      substitutionMap[variable] = term;
    }
    bool ok = formulaToMegalodon(formula, substitutionMap, text);
    _usesEquality = usesEquality;
    _equalitySort = equalitySort;
    _usesConjunction = usesConjunction;
    _usesFalse = usesFalse;
    _usesDisjunction = usesDisjunction;
    _usesSetExists = usesSetExists;
    _usesTrue = usesTrue;
    _usesPropEquality = usesPropEquality;
    _renderingReplayExtra = renderingReplayExtra;
    return ok;
  };
  auto renderTermForExtra = [&](Kernel::TermList term, std::string& text) {
    bool usesEquality = _usesEquality;
    std::string equalitySort = _equalitySort;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySort.clear();
    _renderingReplayExtra = true;
    bool ok = termToMegalodon(term, text);
    _usesEquality = usesEquality;
    _equalitySort = equalitySort;
    _usesConjunction = usesConjunction;
    _usesFalse = usesFalse;
    _usesDisjunction = usesDisjunction;
    _usesSetExists = usesSetExists;
    _usesTrue = usesTrue;
    _usesPropEquality = usesPropEquality;
    _renderingReplayExtra = renderingReplayExtra;
    return ok;
  };
  auto addLambdaSubtermFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Clause* clause, const Kernel::Substitution* substitution) {
    struct RenderedLambda {
      std::string text;
      std::string sort;
      std::string binderSort;
      std::string binderDb;
      std::string body;
      std::string bodySort;
      std::string dbIndices;
      std::string bodyDbIndices;
      bool bodyHasDb = false;
    };
    std::vector<RenderedLambda> lambdas;
    std::set<std::string> seen;
    auto addLambda = [&](Kernel::TermList term) {
      if (lambdas.size() >= 32) {
        return;
      }
      std::string text;
      if (renderTermForExtra(term, text) && seen.insert(text).second) {
        RenderedLambda rendered;
        rendered.text = text;
        rendered.dbIndices = termTextWithHolPrinting(term, Options::HPrinting::DB_INDICES);
        std::string sortText;
        Kernel::TermList sort;
        if (Kernel::SortHelper::tryGetResultSort(term, sort)) {
          sortToMegalodon(sort, sortText);
        }
        rendered.sort = sortText;
        if (term.isLambdaTerm()) {
          std::string binderSortText;
          if (sortToMegalodon(*term.term()->nthArgument(0), binderSortText)) {
            rendered.binderSort = binderSortText;
          }
          rendered.binderDb = "db0";
          Kernel::TermList body = term.lambdaBody();
          std::string bodyText;
          if (renderTermForExtra(body, bodyText)) {
            rendered.body = bodyText;
            rendered.bodyHasDb = bodyText.find("db") != std::string::npos;
          }
          rendered.bodyDbIndices = termTextWithHolPrinting(body, Options::HPrinting::DB_INDICES);
          Kernel::TermList bodySort;
          if (Kernel::SortHelper::tryGetResultSort(body, bodySort)) {
            std::string bodySortText;
            if (sortToMegalodon(bodySort, bodySortText)) {
              rendered.bodySort = bodySortText;
            }
          }
        }
        lambdas.push_back(rendered);
      }
    };
    std::function<void(Kernel::TermList)> visitTerm = [&](Kernel::TermList term) {
      if (term.isVar()) {
        return;
      }
      if (term.isLambdaTerm()) {
        addLambda(term);
        visitTerm(term.lambdaBody());
        return;
      }
      if (term.isApplication()) {
        visitTerm(term.lhs());
        visitTerm(term.rhs());
        return;
      }
      if (!term.isTerm() || term.term()->isSpecial()) {
        return;
      }
      Kernel::Term* t = term.term();
      for (unsigned i = 0; i < t->numTermArguments(); ++i) {
        visitTerm(t->termArg(i));
      }
    };
    for (Kernel::Literal* literal : clause->iterLits()) {
      Kernel::Literal* current = substitution == nullptr ? literal : Kernel::SubstHelper::apply(literal, *substitution);
      for (unsigned i = 0; i < current->arity(); ++i) {
        visitTerm(*current->nthArgument(i));
      }
    }
    if (lambdas.empty()) {
      return;
    }
    fields.push_back(prefix + "_lambda_count=" + std::to_string(lambdas.size()));
    for (std::size_t i = 0; i < lambdas.size(); ++i) {
      fields.push_back(prefix + "_lambda_" + std::to_string(i) + "=" + lambdas[i].text);
      if (!lambdas[i].dbIndices.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_db_indices=" + lambdas[i].dbIndices);
      }
      if (!lambdas[i].sort.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_sort=" + lambdas[i].sort);
      }
      if (!lambdas[i].binderSort.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_binder_sort=" + lambdas[i].binderSort);
      }
      if (!lambdas[i].binderDb.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_binder_db=" + lambdas[i].binderDb);
      }
      if (!lambdas[i].body.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_body=" + lambdas[i].body);
      }
      if (!lambdas[i].bodyDbIndices.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_body_db_indices=" + lambdas[i].bodyDbIndices);
      }
      if (lambdas[i].bodyHasDb) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_body_has_db=true");
      }
      if (!lambdas[i].bodySort.empty()) {
        fields.push_back(prefix + "_lambda_" + std::to_string(i) + "_body_sort=" + lambdas[i].bodySort);
      }
    }
  };
  auto renderClauseForExtra = [&](Kernel::Clause* clause, std::string& text) {
    bool usesEquality = _usesEquality;
    std::string equalitySort = _equalitySort;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySort.clear();
    _renderingReplayExtra = true;
    bool ok = skeletonClauseToMegalodon(clause, text);
    _usesEquality = usesEquality;
    _equalitySort = equalitySort;
    _usesConjunction = usesConjunction;
    _usesFalse = usesFalse;
    _usesDisjunction = usesDisjunction;
    _usesSetExists = usesSetExists;
    _usesTrue = usesTrue;
    _usesPropEquality = usesPropEquality;
    _renderingReplayExtra = renderingReplayExtra;
    return ok;
  };
  auto renderUnitForExtra = [&](Kernel::Unit* unit, std::string& text) {
    if (unit->isClause()) {
      return renderClauseForExtra(unit->asClause(), text);
    }
    return renderFormulaForExtra(unit->getFormula(), text);
  };
  auto addClauseVariableSortFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Clause* clause) {
    Lib::DHMap<unsigned, Kernel::TermList> varSorts;
    Kernel::SortHelper::collectVariableSorts(clause, varSorts);
    std::vector<std::pair<unsigned, std::string>> rendered;
    Lib::DHMap<unsigned, Kernel::TermList>::Iterator it(varSorts);
    while (it.hasNext()) {
      unsigned var;
      Kernel::TermList sort;
      it.next(var, sort);
      std::string sortText;
      if (sortToMegalodon(sort, sortText)) {
        rendered.push_back({var, variableName(var) + ":" + sortText});
      }
    }
    std::sort(rendered.begin(), rendered.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    fields.push_back(prefix + "_variable_sort_count=" + std::to_string(rendered.size()));
    for (std::size_t i = 0; i < rendered.size(); ++i) {
      fields.push_back(prefix + "_variable_sort_" + std::to_string(i) + "=" + rendered[i].second);
    }
  };
  auto addClauseDbIndexSortFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Clause* clause) {
    std::map<unsigned, std::string> rendered;
    std::function<void(Kernel::TermList)> visitTerm = [&](Kernel::TermList term) {
      auto dbIndex = term.deBruijnIndex();
      if (dbIndex.isSome()) {
        Kernel::TermList sort;
        std::string sortText;
        if (Kernel::SortHelper::tryGetResultSort(term, sort) && sortToMegalodon(sort, sortText)) {
          rendered[dbIndex.unwrap()] = "db" + std::to_string(dbIndex.unwrap()) + ":" + sortText;
        }
      }
      if (term.isVar()) {
        return;
      }
      if (term.isApplication()) {
        visitTerm(term.lhs());
        visitTerm(term.rhs());
        return;
      }
      if (term.isLambdaTerm()) {
        visitTerm(term.lambdaBody());
        return;
      }
      if (!term.isTerm() || term.term()->isSpecial()) {
        return;
      }
      Kernel::Term* t = term.term();
      for (unsigned i = 0; i < t->numTermArguments(); ++i) {
        visitTerm(t->termArg(i));
      }
    };
    for (Kernel::Literal* literal : clause->iterLits()) {
      for (unsigned i = 0; i < literal->arity(); ++i) {
        visitTerm(*literal->nthArgument(i));
      }
    }
    fields.push_back(prefix + "_db_sort_count=" + std::to_string(rendered.size()));
    unsigned index = 0;
    for (const auto& entry : rendered) {
      fields.push_back(prefix + "_db_sort_" + std::to_string(index) + "=" + entry.second);
      ++index;
    }
  };

  if (u->inference().rule() == Kernel::InferenceRule::AVATAR_DEFINITION) {
    const auto* splitExtraRaw = env.proofExtra.find(u);
    if (splitExtraRaw != nullptr) {
      const auto* splitExtra = static_cast<const SplitDefinitionExtra*>(splitExtraRaw);
      if (splitExtra->component != nullptr && splitExtra->component->isComponent() && !splitExtra->component->noSplits()) {
        unsigned componentLevel = splitExtra->component->splits()->sval();
        SATLiteral componentLiteral = Splitter::getLiteralFromName(componentLevel);
        _avatarComponentBySatVar[componentLiteral.var()] = splitExtra->component;
        std::vector<std::string> fields;
        fields.push_back("component_split_level=" + std::to_string(componentLevel));
        fields.push_back("component_split_var=" + std::to_string(componentLiteral.var()));
        fields.push_back(std::string("component_split_positive=") + (componentLiteral.positive() ? "1" : "0"));
        std::string componentText;
        if (renderClauseForExtra(splitExtra->component, componentText)) {
          fields.push_back("component_clause=" + componentText);
        }
        addClauseVariableSortFields(fields, "component_clause", splitExtra->component);
        addClauseDbIndexSortFields(fields, "component_clause", splitExtra->component);
        emit("avatar_definition", fields);
      }
    }
  }

  if (u->isClause() && u->asClause()->splits() && !u->asClause()->splits()->isEmpty()) {
    std::vector<std::string> fields;
    unsigned dependencyIndex = 0;
    for (unsigned split : iterTraits(u->asClause()->splits()->iter())) {
      SATLiteral splitLiteral = Splitter::getLiteralFromName(split);
      std::string prefix = "dependency_" + std::to_string(dependencyIndex);
      fields.push_back(prefix + "_split_level=" + std::to_string(split));
      fields.push_back(prefix + "_split_var=" + std::to_string(splitLiteral.var()));
      fields.push_back(prefix + "_split_positive=" + (splitLiteral.positive() ? "1" : "0"));
      auto component = _avatarComponentBySatVar.find(splitLiteral.var());
      if (component != _avatarComponentBySatVar.end() && component->second != nullptr) {
        std::string componentText;
        if (renderClauseForExtra(component->second, componentText)) {
          fields.push_back(prefix + "_component_clause=" + componentText);
        }
        addClauseVariableSortFields(fields, prefix + "_component_clause", component->second);
        addClauseDbIndexSortFields(fields, prefix + "_component_clause", component->second);
        addLambdaSubtermFields(fields, prefix + "_component_clause", component->second, nullptr);
        std::vector<std::string> scopedDbSorts;
        for (const std::string& field : fields) {
          std::string dbPrefix = prefix + "_component_clause_db_sort_";
          if (field.rfind(dbPrefix, 0) != 0) {
            continue;
          }
          if (field.size() <= dbPrefix.size() || !std::isdigit(static_cast<unsigned char>(field[dbPrefix.size()]))) {
            continue;
          }
          std::size_t equals = field.find('=');
          if (equals != std::string::npos) {
            scopedDbSorts.push_back(field.substr(equals + 1));
          }
        }
        if (!scopedDbSorts.empty()) {
          fields.push_back(prefix + "_scoped_split_certificate=component_contains_de_bruijn");
          fields.push_back(prefix + "_scoped_split_certificate_db_sort_count=" + std::to_string(scopedDbSorts.size()));
          for (std::size_t sortIndex = 0; sortIndex < scopedDbSorts.size(); ++sortIndex) {
            fields.push_back(
              prefix + "_scoped_split_certificate_db_sort_" + std::to_string(sortIndex) + "=" + scopedDbSorts[sortIndex]);
          }
        }
      }
      ++dependencyIndex;
    }
    fields.push_back("dependency_count=" + std::to_string(dependencyIndex));
    emit("split_dependency", fields);
  }

  if (u->inference().rule() == Kernel::InferenceRule::AVATAR_SPLIT_CLAUSE) {
    UnitIterator parents = u->getParents();
    if (parents.hasNext()) {
      Kernel::Unit* mainParentUnit = parents.next();
      if (mainParentUnit->isClause()) {
        Kernel::Clause* mainParent = mainParentUnit->asClause();
        std::vector<std::string> fields;
        fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
        std::string sourceText;
        if (renderClauseForExtra(mainParent, sourceText)) {
          fields.push_back("source=" + sourceText);
        }
        std::string targetText;
        if (renderUnitForExtra(u, targetText)) {
          fields.push_back("target=" + targetText);
        }

        std::set<unsigned> previousSplitVars;
        if (!mainParent->noSplits()) {
          unsigned previousIndex = 0;
          for (unsigned split : iterTraits(mainParent->splits()->iter())) {
            SATLiteral splitLiteral = Splitter::getLiteralFromName(split);
            previousSplitVars.insert(splitLiteral.var());
            fields.push_back("previous_split_" + std::to_string(previousIndex) + "_level=" + std::to_string(split));
            fields.push_back("previous_split_" + std::to_string(previousIndex) + "_var=" + std::to_string(splitLiteral.var()));
            fields.push_back("previous_split_" + std::to_string(previousIndex) + "_positive=" + (splitLiteral.positive() ? "1" : "0"));
            ++previousIndex;
          }
          fields.push_back("previous_split_count=" + std::to_string(previousIndex));
        } else {
          fields.push_back("previous_split_count=0");
        }

        const auto* satExtra = env.proofExtra.find(u);
        if (satExtra != nullptr) {
          const auto* avatarClause = static_cast<const Indexing::SATClauseExtra*>(satExtra);
          unsigned satIndex = 0;
          for (SATLiteral literal : avatarClause->clause->iter()) {
            fields.push_back("sat_literal_" + std::to_string(satIndex) + "_var=" + std::to_string(literal.var()));
            fields.push_back("sat_literal_" + std::to_string(satIndex) + "_positive=" + (literal.positive() ? "1" : "0"));
            ++satIndex;
          }
          fields.push_back("sat_literal_count=" + std::to_string(satIndex));
        }

        std::map<unsigned, Kernel::Clause*> components;
        std::map<unsigned, std::pair<unsigned, Kernel::Clause*>> splitToParentMap;
        unsigned parentIndex = 1;
        for (Kernel::Unit* splitParent : iterTraits(u->getParents())) {
          if (parentIndex == 1) {
            ++parentIndex;
            continue;
          }
          const auto* splitExtraRaw = env.proofExtra.find(splitParent);
          if (splitExtraRaw == nullptr) {
            ++parentIndex;
            continue;
          }
          const auto* splitExtra = static_cast<const SplitDefinitionExtra*>(splitExtraRaw);
          if (splitExtra->component == nullptr || !splitExtra->component->isComponent() || splitExtra->component->noSplits()) {
            ++parentIndex;
            continue;
          }
          unsigned componentLevel = splitExtra->component->splits()->sval();
          SATLiteral componentLiteral = Splitter::getLiteralFromName(componentLevel);
          components.insert({componentLevel, splitExtra->component});
          if (previousSplitVars.find(componentLiteral.var()) == previousSplitVars.end()) {
            splitToParentMap.insert({componentLiteral.var(), {parentIndex - 1, splitExtra->component}});
          }
          std::string prefix = "component_parent_" + std::to_string(parentIndex - 1);
          fields.push_back(prefix + "_unit=" + std::to_string(splitParent->number()));
          fields.push_back(prefix + "_split_level=" + std::to_string(componentLevel));
          fields.push_back(prefix + "_split_var=" + std::to_string(componentLiteral.var()));
          fields.push_back(prefix + "_split_positive=" + (componentLiteral.positive() ? "1" : "0"));
          std::string componentText;
          if (renderClauseForExtra(splitExtra->component, componentText)) {
            fields.push_back(prefix + "_clause=" + componentText);
          }
          ++parentIndex;
        }
        fields.push_back("component_parent_count=" + std::to_string(parentIndex > 1 ? parentIndex - 2 : 0));

        Stack<LiteralStack> disjointLiterals;
        if (!Splitter::getComponents(mainParent, disjointLiterals)) {
          disjointLiterals.reset();
          LiteralStack component;
          for (Kernel::Literal* literal : mainParent->iterLits()) {
            component.push(literal);
          }
          disjointLiterals.push(std::move(component));
        }
        unsigned classIndex = 0;
        Substitution fullSubst;
        std::map<unsigned, unsigned> varToSplitMap;
        decltype(disjointLiterals)::Iterator classes(disjointLiterals);
        while (classes.hasNext()) {
          LiteralStack klass = classes.next();
          std::string classPrefix = "literal_class_" + std::to_string(classIndex);
          fields.push_back(classPrefix + "_literal_count=" + std::to_string(klass.size()));
          for (unsigned literalIndex = 0; literalIndex < klass.size(); ++literalIndex) {
            std::string literalText;
            if (skeletonLiteralToMegalodon(klass[literalIndex], literalText)) {
              fields.push_back(classPrefix + "_literal_" + std::to_string(literalIndex) + "=" + literalText);
            }
          }
          Substitution subst;
          for (auto [splitLevel, component] : components) {
            if (klass.size() != component->length()) {
              continue;
            }
            subst.reset();
            if (klass.size() == 1 && klass[0]->ground() && Kernel::Literal::positiveLiteral(klass[0]) == Kernel::Literal::positiveLiteral((*component)[0])) {
              Lib::DHMap<unsigned, Kernel::TermList> variableSorts;
              Kernel::SortHelper::collectVariableSorts(klass[0], variableSorts);
              auto variableDomain = variableSorts.domain();
              while (variableDomain.hasNext()) {
                unsigned var = variableDomain.next();
                varToSplitMap.insert({var, Splitter::getLiteralFromName(splitLevel).var()});
              }
              fields.push_back(classPrefix + "_matched_split_level=" + std::to_string(splitLevel));
              break;
            }
            if (Kernel::MLVariant::isVariant(klass.begin(), component, /*complementary=*/false, &subst)) {
              for (auto [var, term] : iterTraits(subst.items())) {
                if (term.isVar()) {
                  fullSubst.bind(term.var(), Kernel::TermList::var(var));
                  varToSplitMap.insert({term.var(), Splitter::getLiteralFromName(splitLevel).var()});
                }
              }
              fields.push_back(classPrefix + "_matched_split_level=" + std::to_string(splitLevel));
              break;
            }
          }
          ++classIndex;
        }
        fields.push_back("literal_class_count=" + std::to_string(classIndex));

        Lib::DHMap<unsigned, Kernel::TermList> mainParentSorts;
        Kernel::SortHelper::collectVariableSorts(mainParent, mainParentSorts);
        std::set<unsigned> sortedParentVars;
        for (unsigned var : iterTraits(mainParentSorts.domain())) {
          sortedParentVars.insert(var);
        }
        unsigned bindingIndex = 0;
        for (unsigned var : sortedParentVars) {
          Kernel::TermList substituted = fullSubst.apply(var);
          auto splitVar = varToSplitMap.find(var);
          if (!substituted.isVar() && splitVar == varToSplitMap.end()) {
            continue;
          }
          std::string prefix = "parent_var_binding_" + std::to_string(bindingIndex);
          fields.push_back(prefix + "_parent_var=" + variableName(var));
          if (substituted.isVar()) {
            fields.push_back(prefix + "_component_var=" + variableName(substituted.var()));
          }
          if (splitVar != varToSplitMap.end()) {
            fields.push_back(prefix + "_split_var=" + std::to_string(splitVar->second));
          }
          ++bindingIndex;
        }
        fields.push_back("parent_var_binding_count=" + std::to_string(bindingIndex));
        emit("avatar_split", fields);
      }
    }
  }

  auto isNormalFormRule = [](Kernel::InferenceRule rule) {
    switch (rule) {
      case Kernel::InferenceRule::NNF:
      case Kernel::InferenceRule::ENNF:
      case Kernel::InferenceRule::FLATTEN:
      case Kernel::InferenceRule::REDUCE_FALSE_TRUE:
      case Kernel::InferenceRule::THEORY_NORMALIZATION:
      case Kernel::InferenceRule::BOOL_SIMP:
        return true;
      default:
        return false;
    }
  };

  if (isNormalFormRule(u->inference().rule()) && !u->isClause()) {
    UnitIterator parentIterator = u->getParents();
    if (parentIterator.hasNext()) {
      Kernel::Unit* parent = parentIterator.next();
      if (!parent->isClause()) {
        Kernel::Formula* source = parent->getFormula();
        Kernel::Formula* target = u->getFormula();
        std::vector<std::string> fields;
        fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
        std::string sourceText;
        std::string targetText;
        if (renderFormulaForExtra(source, sourceText)) {
          fields.push_back("source=" + sourceText);
        } else {
          fields.push_back("source_conversion_failed=1");
          fields.push_back("source_connective=" + std::to_string(static_cast<int>(source->connective())));
          fields.push_back("source_raw=" + source->toString());
        }
        if (renderFormulaForExtra(target, targetText)) {
          fields.push_back("target=" + targetText);
        } else {
          fields.push_back("target_conversion_failed=1");
          fields.push_back("target_connective=" + std::to_string(static_cast<int>(target->connective())));
          fields.push_back("target_raw=" + target->toString());
        }

        unsigned pairCount = 0;
        std::size_t totalPairText = 0;
        const unsigned pairLimit = 32;
        const std::size_t textLimit = 120000;
        std::function<bool(const std::vector<Kernel::Formula*>&, std::size_t, std::size_t, Kernel::Connective, std::string&)> renderFormulaSliceForExtra;
        renderFormulaSliceForExtra =
          [&](const std::vector<Kernel::Formula*>& formulas, std::size_t begin, std::size_t end, Kernel::Connective connective, std::string& result) {
            if (begin >= end || end > formulas.size()) {
              return false;
            }
            if (begin + 1 == end) {
              return renderFormulaForExtra(formulas[begin], result);
            }
            std::string lhs;
            std::string rhs;
            if (connective == Kernel::AND) {
              if (!renderFormulaForExtra(formulas[begin], lhs)
                || !renderFormulaSliceForExtra(formulas, begin + 1, end, connective, rhs)) {
                return false;
              }
              result = "vampire_and " + parenthesize(lhs) + " " + parenthesize(rhs);
              return true;
            }
            if (connective == Kernel::OR) {
              if (!renderFormulaSliceForExtra(formulas, begin, end - 1, connective, lhs)
                || !renderFormulaForExtra(formulas[end - 1], rhs)) {
                return false;
              }
              result = "vampire_or " + parenthesize(lhs) + " " + parenthesize(rhs);
              return true;
            }
            return false;
          };

        auto formulaArgs = [](Kernel::Formula* formula) {
          std::vector<Kernel::Formula*> result;
          Kernel::FormulaList::Iterator args(formula->args());
          while (args.hasNext()) {
            result.push_back(args.next());
          }
          return result;
        };

        auto emitPair = [&](const std::string& leftText, const std::string& rightText, const std::string& path) {
          if (leftText == rightText || pairCount >= pairLimit || totalPairText >= textLimit) {
            return false;
          }
          totalPairText += leftText.size() + rightText.size();
          if (totalPairText > textLimit) {
            return false;
          }
          unsigned index = pairCount++;
          fields.push_back("pair_" + std::to_string(index) + "_source=" + leftText);
          fields.push_back("pair_" + std::to_string(index) + "_target=" + rightText);
          fields.push_back("pair_" + std::to_string(index) + "_path=" + path);
          return true;
        };

        std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned, std::string)> collectPairs;
        std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned, std::string)> collectEnnfPairs;
        std::function<void(const std::vector<Kernel::Formula*>&, std::size_t, std::size_t, const std::vector<Kernel::Formula*>&, std::size_t, std::size_t, Kernel::Connective, unsigned, std::string)> collectSlicePairs;
        auto negatedFormula = [](Kernel::Formula* formula) -> Kernel::Formula* {
          return new Kernel::BinaryFormula(Kernel::IMP, formula, Kernel::Formula::falseFormula());
        };
        auto negatedBody = [](Kernel::Formula* formula) -> Kernel::Formula* {
          if (formula->connective() == Kernel::NOT) {
            return formula->uarg();
          }
          if (formula->connective() == Kernel::IMP && formula->right()->connective() == Kernel::FALSE) {
            return formula->left();
          }
          return nullptr;
        };
        collectPairs =
          [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth, std::string path) {
            if (left == nullptr || right == nullptr || depth > 16 || pairCount >= pairLimit || totalPairText >= textLimit) {
              return;
            }
            std::string leftText;
            std::string rightText;
            if (!renderFormulaForExtra(left, leftText) || !renderFormulaForExtra(right, rightText)) {
              return;
            }
            emitPair(leftText, rightText, path);
            if (left->connective() != right->connective()) {
              if (u->inference().rule() == Kernel::InferenceRule::ENNF) {
                collectEnnfPairs(left, right, depth + 1, path);
              }
              return;
            }
            switch (left->connective()) {
              case Kernel::AND:
              case Kernel::OR: {
                std::vector<Kernel::Formula*> leftArgs = formulaArgs(left);
                std::vector<Kernel::Formula*> rightArgs = formulaArgs(right);
                if (leftArgs.size() != rightArgs.size() || leftArgs.size() < 2) {
                  return;
                }
                collectSlicePairs(leftArgs, 0, leftArgs.size(), rightArgs, 0, rightArgs.size(), left->connective(), depth + 1, path);
                return;
              }
              case Kernel::IMP:
              case Kernel::IFF:
              case Kernel::XOR:
                collectPairs(left->left(), right->left(), depth + 1, path + ".left");
                collectPairs(left->right(), right->right(), depth + 1, path + ".right");
                return;
              case Kernel::NOT:
                collectPairs(left->uarg(), right->uarg(), depth + 1, path + ".not");
                return;
              case Kernel::FORALL:
              case Kernel::EXISTS:
                collectPairs(left->qarg(), right->qarg(), depth + 1, path + ".body");
                return;
              default:
                return;
            }
          };
        collectEnnfPairs =
          [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth, std::string path) {
            if (left == nullptr || right == nullptr || depth > 16 || pairCount >= pairLimit || totalPairText >= textLimit) {
              return;
            }
            std::vector<Kernel::Formula*> rightArgs;
            if (right->connective() == Kernel::AND || right->connective() == Kernel::OR) {
              rightArgs = formulaArgs(right);
            }
            if (left->connective() == Kernel::IMP && right->connective() == Kernel::OR && rightArgs.size() == 2) {
              collectPairs(negatedFormula(left->left()), rightArgs[0], depth + 1, path + ".ennf_imp_left");
              collectPairs(left->right(), rightArgs[1], depth + 1, path + ".ennf_imp_right");
              return;
            }
            Kernel::Formula* negated = negatedBody(left);
            if (negated == nullptr) {
              return;
            }
            if (negated->connective() == Kernel::IMP && right->connective() == Kernel::AND && rightArgs.size() == 2) {
              collectPairs(negated->left(), rightArgs[0], depth + 1, path + ".ennf_neg_imp_left");
              collectPairs(negatedFormula(negated->right()), rightArgs[1], depth + 1, path + ".ennf_neg_imp_right");
              return;
            }
            if ((negated->connective() == Kernel::AND || negated->connective() == Kernel::OR)
              && right->connective() == (negated->connective() == Kernel::AND ? Kernel::OR : Kernel::AND)) {
              std::vector<Kernel::Formula*> leftArgs = formulaArgs(negated);
              if (leftArgs.size() != rightArgs.size() || leftArgs.size() < 2) {
                return;
              }
              for (std::size_t index = 0; index < leftArgs.size() && index < 2; ++index) {
                collectPairs(
                  negatedFormula(leftArgs[index]),
                  rightArgs[index],
                  depth + 1,
                  path + ".ennf_neg_junction[" + std::to_string(index) + "]");
              }
            }
          };
        collectSlicePairs =
          [&](const std::vector<Kernel::Formula*>& leftArgs, std::size_t leftBegin, std::size_t leftEnd,
              const std::vector<Kernel::Formula*>& rightArgs, std::size_t rightBegin, std::size_t rightEnd,
              Kernel::Connective connective, unsigned depth, std::string path) {
            if (depth > 16 || pairCount >= pairLimit || totalPairText >= textLimit) {
              return;
            }
            std::size_t leftSize = leftEnd - leftBegin;
            std::size_t rightSize = rightEnd - rightBegin;
            if (leftSize != rightSize || leftSize < 2) {
              return;
            }
            if (connective == Kernel::AND) {
              collectPairs(leftArgs[leftBegin], rightArgs[rightBegin], depth + 1, path + ".and[0]");
              if (leftSize == 2) {
                collectPairs(leftArgs[leftBegin + 1], rightArgs[rightBegin + 1], depth + 1, path + ".and[1]");
              } else {
                std::string leftText;
                std::string rightText;
                if (renderFormulaSliceForExtra(leftArgs, leftBegin + 1, leftEnd, connective, leftText)
                  && renderFormulaSliceForExtra(rightArgs, rightBegin + 1, rightEnd, connective, rightText)) {
                  emitPair(leftText, rightText, path + ".and[1]");
                }
                collectSlicePairs(leftArgs, leftBegin + 1, leftEnd, rightArgs, rightBegin + 1, rightEnd, connective, depth + 1, path + ".and[1]");
              }
              return;
            }
            if (connective == Kernel::OR) {
              if (leftSize == 2) {
                collectPairs(leftArgs[leftBegin], rightArgs[rightBegin], depth + 1, path + ".or[0]");
                collectPairs(leftArgs[leftBegin + 1], rightArgs[rightBegin + 1], depth + 1, path + ".or[1]");
                return;
              }
              std::string leftText;
              std::string rightText;
              if (renderFormulaSliceForExtra(leftArgs, leftBegin, leftEnd - 1, connective, leftText)
                && renderFormulaSliceForExtra(rightArgs, rightBegin, rightEnd - 1, connective, rightText)) {
                emitPair(leftText, rightText, path + ".or[0]");
              }
              collectSlicePairs(leftArgs, leftBegin, leftEnd - 1, rightArgs, rightBegin, rightEnd - 1, connective, depth + 1, path + ".or[0]");
              collectPairs(leftArgs[leftEnd - 1], rightArgs[rightEnd - 1], depth + 1, path + ".or[1]");
            }
          };
        collectPairs(source, target, 0, "root");
        emit("normal_form", fields);
      }
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::RECTIFY && !u->isClause()) {
    const auto* genericInfo = InferenceRecorder::instance()->getGenericLastInferenceInformation();
    const auto* rectifyInfo = static_cast<const InferenceRecorder::RectifyInferenceExtra*>(genericInfo);
    if (rectifyInfo != nullptr) {
      std::vector<std::string> fields;
      fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
      UnitIterator parentIterator = u->getParents();
      if (parentIterator.hasNext()) {
        Kernel::Unit* parent = parentIterator.next();
        if (!parent->isClause()) {
          std::string sourceText;
          if (renderFormulaForExtra(parent->getFormula(), sourceText)) {
            fields.push_back("source=" + sourceText);
          }
        }
      }
      std::string targetText;
      if (renderFormulaForExtra(u->getFormula(), targetText)) {
        fields.push_back("target=" + targetText);
      }
      fields.push_back("renaming_count=" + std::to_string(rectifyInfo->renamings.size()));
      unsigned index = 0;
      const unsigned renamingLimit = 64;
      for (auto [newFormula, formulaAndSubst] : rectifyInfo->renamings) {
        if (index >= renamingLimit) {
          fields.push_back("renaming_truncated=1");
          break;
        }
        auto [formula, substitution] = formulaAndSubst;
        std::string originalText;
        if (renderFormulaForExtra(formula, originalText)) {
          fields.push_back("renaming_" + std::to_string(index) + "_source=" + originalText);
        }
        std::string substitutedText;
        if (renderFormulaForExtraWithSubstitution(formula, substitution, substitutedText)) {
          fields.push_back("renaming_" + std::to_string(index) + "_source_substituted=" + substitutedText);
        }
        std::string newText;
        if (renderFormulaForExtra(newFormula, newText)) {
          fields.push_back("renaming_" + std::to_string(index) + "_target=" + newText);
        }
        ++index;
      }
      emit("rectify", fields);
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::FOOL_ELIMINATION && !u->isClause()) {
    UnitIterator parentIterator = u->getParents();
    if (parentIterator.hasNext()) {
      Kernel::Unit* parent = parentIterator.next();
      if (!parent->isClause()) {
        Kernel::Formula* source = parent->getFormula();
        Kernel::Formula* target = u->getFormula();
        std::vector<std::string> fields;
        fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
        std::string sourceText;
        std::string targetText;
        if (renderFormulaForExtra(source, sourceText)) {
          fields.push_back("source=" + sourceText);
        } else {
          fields.push_back("source_conversion_failed=1");
          fields.push_back("source_connective=" + std::to_string(static_cast<int>(source->connective())));
          fields.push_back("source_raw=" + source->toString());
        }
        if (renderFormulaForExtra(target, targetText)) {
          fields.push_back("target=" + targetText);
        } else {
          fields.push_back("target_conversion_failed=1");
          fields.push_back("target_connective=" + std::to_string(static_cast<int>(target->connective())));
          fields.push_back("target_raw=" + target->toString());
        }

        unsigned pairCount = 0;
        std::size_t totalPairText = 0;
        const unsigned pairLimit = 48;
        const std::size_t textLimit = 180000;
        std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned)> collectPairs =
          [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth) {
            if (left == nullptr || right == nullptr || depth > 24 || pairCount >= pairLimit || totalPairText >= textLimit) {
              return;
            }
            if (left->toString() == right->toString()) {
              return;
            }
            std::string leftText;
            std::string rightText;
            if (renderFormulaForExtra(left, leftText) && renderFormulaForExtra(right, rightText)) {
              totalPairText += leftText.size() + rightText.size();
              if (totalPairText <= textLimit) {
                unsigned index = pairCount++;
                fields.push_back("pair_" + std::to_string(index) + "_source=" + leftText);
                fields.push_back("pair_" + std::to_string(index) + "_target=" + rightText);
              }
            }
            if (left->connective() != right->connective()) {
              return;
            }
            switch (left->connective()) {
              case Kernel::AND:
              case Kernel::OR: {
                Kernel::FormulaList::Iterator leftIt(left->args());
                Kernel::FormulaList::Iterator rightIt(right->args());
                while (leftIt.hasNext() && rightIt.hasNext()) {
                  collectPairs(leftIt.next(), rightIt.next(), depth + 1);
                }
                return;
              }
              case Kernel::IMP:
              case Kernel::IFF:
              case Kernel::XOR:
                collectPairs(left->left(), right->left(), depth + 1);
                collectPairs(left->right(), right->right(), depth + 1);
                return;
              case Kernel::NOT:
                collectPairs(left->uarg(), right->uarg(), depth + 1);
                return;
              case Kernel::FORALL:
              case Kernel::EXISTS:
                collectPairs(left->qarg(), right->qarg(), depth + 1);
                return;
              default:
                return;
            }
          };
        collectPairs(source, target, 0);
        emit("fool", fields);
      }
    }
  }

  auto isDefinitionRewriteRule = [](Kernel::InferenceRule rule) {
    switch (rule) {
      case Kernel::InferenceRule::DEFINITION_UNFOLDING:
      case Kernel::InferenceRule::DEFINITION_FOLDING_TWEE:
      case Kernel::InferenceRule::DEFINITION_FOLDING_PRED:
        return true;
      default:
        return false;
    }
  };

  if (isDefinitionRewriteRule(u->inference().rule())) {
    std::vector<std::string> fields;
    fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
    std::string targetText;
    if (renderUnitForExtra(u, targetText)) {
      fields.push_back("target=" + targetText);
    }
    unsigned parentIndex = 0;
    for (Kernel::Unit* parent : iterTraits(u->getParents())) {
      std::string parentText;
      if (renderUnitForExtra(parent, parentText)) {
        fields.push_back("parent_" + std::to_string(parentIndex) + "=" + parentText);
        if (parentIndex == 0) {
          fields.push_back("source=" + parentText);
        } else if (parentIndex == 1) {
          fields.push_back("definition=" + parentText);
        }
      }
      ++parentIndex;
    }
    if (u->inference().rule() == Kernel::InferenceRule::DEFINITION_FOLDING_TWEE && extra != nullptr) {
      const auto* foldingExtra = static_cast<const TweeDefinitionFoldingExtra*>(extra);
      fields.push_back("fold_step_count=" + std::to_string(foldingExtra->steps.size()));
      for (std::size_t stepIndex = 0; stepIndex < foldingExtra->steps.size(); ++stepIndex) {
        const std::string prefix = "fold_step_" + std::to_string(stepIndex);
        std::string lhs;
        if (renderTermForExtra(foldingExtra->steps[stepIndex].first, lhs)) {
          fields.push_back(prefix + "_lhs=" + lhs);
        }
        std::string rhs;
        if (renderTermForExtra(foldingExtra->steps[stepIndex].second, rhs)) {
          fields.push_back(prefix + "_rhs=" + rhs);
        }
      }
    }
    emit("definition_rewrite", fields);
  }

  if (u->inference().rule() == Kernel::InferenceRule::CLAUSIFY && u->isClause()) {
    UnitIterator parentIterator = u->getParents();
    if (parentIterator.hasNext()) {
      Kernel::Unit* parent = parentIterator.next();
      std::vector<std::string> fields;
      fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
      std::string sourceText;
      if (renderUnitForExtra(parent, sourceText)) {
        fields.push_back("source=" + sourceText);
      }
      std::string targetText;
      if (renderUnitForExtra(u, targetText)) {
        fields.push_back("target=" + targetText);
      }
      if (!u->asClause()->isEmpty()) {
        fields.push_back("target_literal_count=" + std::to_string(u->asClause()->length()));
        for (unsigned literalIndex = 0; literalIndex < u->asClause()->length(); ++literalIndex) {
          std::string literalText;
          if (skeletonLiteralToMegalodon((*u->asClause())[literalIndex], literalText)) {
            fields.push_back("target_literal_" + std::to_string(literalIndex) + "=" + literalText);
          }
        }
      } else {
        fields.push_back("target_literal_count=0");
      }
      const auto* parentExtra = env.proofExtra.find(parent);
      if (parentExtra != nullptr) {
        const auto* cnfExtra = static_cast<const Inferences::CNFTransformationInferenceExtra*>(parentExtra);
        fields.push_back("parent_clause_count=" + std::to_string(cnfExtra->number));
      }
      emit("cnf", fields);
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::SKOLEMIZE && !u->isClause()) {
    std::vector<std::string> fields;
    fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
    std::string targetText;
    if (renderUnitForExtra(u, targetText)) {
      fields.push_back("target=" + targetText);
    }
    unsigned parentIndex = 0;
    for (Kernel::Unit* parent : iterTraits(u->getParents())) {
      std::string parentText;
      if (renderUnitForExtra(parent, parentText)) {
        fields.push_back("parent_" + std::to_string(parentIndex) + "=" + parentText);
        if (parentIndex == 0) {
          fields.push_back("source=" + parentText);
        }
      }
      ++parentIndex;
    }
    if (_is->hasIntroducedSymbols(u)) {
      auto& symbols = _is->getIntroducedSymbols(u);
      fields.push_back("introduced_count=" + std::to_string(symbols.size()));
      unsigned symbolIndex = 0;
      for (auto symbol : iterTraits(Kernel::InferenceStore::SymbolStack::ConstIterator(symbols))) {
        const std::string prefix = "introduced_" + std::to_string(symbolIndex);
        fields.push_back(prefix + "_kind=" + std::to_string(static_cast<int>(symbol.first)));
        fields.push_back(prefix + "_raw_symbol=" + std::to_string(symbol.second));
        long replacedVar = _is->variableReplacedByIntroducedSymbol(symbol.second);
        if (replacedVar >= 0) {
          fields.push_back(prefix + "_replaced_var=" + variableName(static_cast<unsigned>(replacedVar)));
        }
        if (symbol.first == SymbolType::FUNC) {
          std::string name = functionName(symbol.second);
          fields.push_back(prefix + "_symbol=" + name);
          std::string declaration = functionDeclaration(symbol.second, name);
          if (!declaration.empty()) {
            fields.push_back(prefix + "_declaration=" + declaration);
          }
        } else if (symbol.first == SymbolType::PRED) {
          std::string name = predicateName(symbol.second);
          fields.push_back(prefix + "_symbol=" + name);
          std::string declaration = predicateDeclaration(symbol.second, name);
          if (!declaration.empty()) {
            fields.push_back(prefix + "_declaration=" + declaration);
          }
        } else {
          fields.push_back(prefix + "_symbol=" + recoverMegalodonSymbolName(env.signature->typeConName(symbol.second), "T"));
        }
        ++symbolIndex;
      }
    }
    emit("skolemize", fields);
  }

  if (u->inference().rule() == Kernel::InferenceRule::PREDICATE_DEFINITION && _is->hasIntroducedSymbols(u)) {
    auto& symbols = _is->getIntroducedSymbols(u);
    if (symbols.size() == 1 && symbols.top().first == SymbolType::PRED) {
      unsigned symbol = symbols.top().second;
      Kernel::Formula* formula = _is->formulaReplacedByIntroducedSymbol(symbol);
      std::string formulaText;
      if (formula != nullptr && formulaToMegalodon(formula, formulaText)) {
        std::string name = predicateName(symbol);
        std::string declaration = predicateDeclaration(symbol, name);
        std::string sort;
        std::size_t colon = declaration.find(':');
        std::size_t dot = declaration.rfind('.');
        if (colon != std::string::npos && dot != std::string::npos && colon < dot) {
          sort = declaration.substr(colon + 1, dot - colon - 1);
        }
        std::vector<std::string> fields;
        fields.push_back("introduced_symbol=" + name);
        if (!sort.empty()) {
          fields.push_back("sort=" + sort);
        }
        Lib::DHMap<unsigned, Kernel::TermList> bodyVarSorts;
        Kernel::SortHelper::collectVariableSorts(formula, bodyVarSorts);
        std::vector<std::pair<unsigned, std::string>> renderedBodyVarSorts;
        Lib::DHMap<unsigned, Kernel::TermList>::Iterator varSortIterator(bodyVarSorts);
        while (varSortIterator.hasNext()) {
          unsigned var;
          Kernel::TermList varSort;
          varSortIterator.next(var, varSort);
          std::string varSortText;
          if (sortToMegalodon(varSort, varSortText)) {
            renderedBodyVarSorts.push_back({var, variableName(var) + ":" + varSortText});
          }
        }
        std::sort(renderedBodyVarSorts.begin(), renderedBodyVarSorts.end(), [](const auto& left, const auto& right) {
          return left.first < right.first;
        });
        for (std::size_t index = 0; index < renderedBodyVarSorts.size(); ++index) {
          fields.push_back("body_variable_sort_" + std::to_string(index) + "=" + renderedBodyVarSorts[index].second);
        }
        fields.push_back("formula=" + formulaText);
        emit("predicate_definition", fields);
      }
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::FUNCTION_DEFINITION && u->isClause()) {
    std::vector<std::string> fields;
    if (_is->hasIntroducedSymbols(u)) {
      auto& symbols = _is->getIntroducedSymbols(u);
      if (symbols.size() == 1 && symbols.top().first == SymbolType::FUNC) {
        unsigned symbol = symbols.top().second;
        std::string name = functionName(symbol);
        std::string declaration = functionDeclaration(symbol, name);
        std::string sort;
        std::size_t colon = declaration.find(':');
        std::size_t dot = declaration.rfind('.');
        if (colon != std::string::npos && dot != std::string::npos && colon < dot) {
          sort = declaration.substr(colon + 1, dot - colon - 1);
        }
        fields.push_back("introduced_symbol=" + name);
        if (!sort.empty()) {
          fields.push_back("sort=" + sort);
        }
      }
    }
    if (u->asClause()->length() == 1) {
      Kernel::Literal* literal = (*u->asClause())[0];
      if (literal->isEquality() && literal->isPositive()) {
        std::string equalitySort;
        if (sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort)) {
          fields.push_back("equality_sort=" + equalitySort);
        }
        std::string lhs;
        std::string rhs;
        if (termToMegalodon(*literal->nthArgument(0), lhs)) {
          fields.push_back("lhs=" + lhs);
        }
        if (termToMegalodon(*literal->nthArgument(1), rhs)) {
          fields.push_back("rhs=" + rhs);
        }
        std::string proposition;
        if (skeletonLiteralToMegalodon(literal, proposition)) {
          fields.push_back("proposition=" + proposition);
        } else if (!lhs.empty() && !rhs.empty()) {
          fields.push_back("proposition=" + lhs + " = " + rhs);
        }
      }
    }
    if (!fields.empty()) {
      emit("function_definition", fields);
    }
  }

  if (u->isClause() && u->asClause()->length() == 1) {
    Kernel::Literal* literal = (*u->asClause())[0];
    if (literal->isEquality() && literal->isPositive()) {
      std::string equalitySort;
      std::string lhs;
      std::string rhs;
      if (sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort)
        && equalitySort.find("->") != std::string::npos
        && termToMegalodon(*literal->nthArgument(0), lhs)
        && termToMegalodon(*literal->nthArgument(1), rhs)) {
        std::vector<std::string> fields;
        fields.push_back("equality_sort=" + equalitySort);
        fields.push_back("lhs=" + lhs);
        fields.push_back("rhs=" + rhs);
        fields.push_back("proposition=" + lhs + " = " + rhs);
        emit("clause_equality", fields);
      }
    }
  }

  if (u->isClause()) {
    std::vector<std::string> fields;
    addLambdaSubtermFields(fields, "step", u->asClause(), nullptr);
    if (!fields.empty()) {
      emit("lambda_sorts", fields);
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::UNIT_RESULTING_RESOLUTION && u->isClause()) {
    std::vector<std::string> fields;
    fields.push_back("conclusion_clause=" + substitutedClauseText(u->asClause(), Kernel::Substitution()));
    std::string proposition;
    if (skeletonClauseToMegalodon(u->asClause(), proposition)) {
      fields.push_back("conclusion_proposition=" + proposition);
    }
    if (extra != nullptr) {
      const auto* urr = static_cast<const Inferences::UnitResultingResolutionExtra*>(extra);
      fields.push_back("trace_main_parent_unit=" + std::to_string(urr->mainParent->number()));
      fields.push_back("trace_step_count=" + std::to_string(urr->steps.size()));
      for (std::size_t traceIndex = 0; traceIndex < urr->steps.size(); ++traceIndex) {
        const auto& trace = urr->steps[traceIndex];
        std::string prefix = "trace_step_" + std::to_string(traceIndex);
        fields.push_back(prefix + "_unit_parent=" + std::to_string(trace.unitParent->number()));
        fields.push_back(prefix + "_selected=" + literalText(trace.selected));
        if (skeletonLiteralToMegalodon(trace.selected, proposition)) {
          fields.push_back(prefix + "_selected_proposition=" + proposition);
        }
        fields.push_back(prefix + "_selected_substituted=" + literalText(trace.selectedSubstituted));
        if (skeletonLiteralToMegalodon(trace.selectedSubstituted, proposition)) {
          fields.push_back(prefix + "_selected_substituted_proposition=" + proposition);
        }
        fields.push_back(prefix + "_unit_substituted=" + literalText(trace.unitSubstituted));
        if (skeletonLiteralToMegalodon(trace.unitSubstituted, proposition)) {
          fields.push_back(prefix + "_unit_substituted_proposition=" + proposition);
        }
      }
      fields.push_back("trace_remaining_count=" + std::to_string(urr->remaining.size()));
      for (std::size_t remainingIndex = 0; remainingIndex < urr->remaining.size(); ++remainingIndex) {
        std::string prefix = "trace_remaining_" + std::to_string(remainingIndex);
        fields.push_back(prefix + "=" + literalText(urr->remaining[remainingIndex]));
        if (skeletonLiteralToMegalodon(urr->remaining[remainingIndex], proposition)) {
          fields.push_back(prefix + "_proposition=" + proposition);
        }
      }
    }
    addParentSubstitutionFields(fields);
    for (std::size_t i = 0; i < parentClauses.size(); ++i) {
      fields.push_back("parent_" + std::to_string(i) + "_unit=" + std::to_string(parentClauses[i]->number()));
      fields.push_back("parent_" + std::to_string(i) + "_clause=" + substitutedClauseText(parentClauses[i], Kernel::Substitution()));
      if (skeletonClauseToMegalodon(parentClauses[i], proposition)) {
        fields.push_back("parent_" + std::to_string(i) + "_proposition=" + proposition);
      }
      if (
        info != nullptr
        && i < info->premises.size()
        && i < info->substitutionForBanksSub.size()
        && substitutedClauseToMegalodon(info->premises[i], info->substitutionForBanksSub[i], proposition)
      ) {
        fields.push_back("parent_" + std::to_string(i) + "_substituted_proposition=" + proposition);
      }
    }
    emit("unit_resulting_resolution", fields);
  }

  if (extra == nullptr) {
    return;
  }

  switch (u->inference().rule()) {
    case Kernel::InferenceRule::SUPERPOSITION:
    case Kernel::InferenceRule::EQUALITY_FACTORING: {
      const auto* rewrite = static_cast<const Inferences::TwoLiteralRewriteInferenceExtra*>(extra);
      std::vector<std::string> fields;
      fields.push_back(std::string("selected=") + literalText(rewrite->selected.selectedLiteral.selectedLiteral));
      fields.push_back(std::string("other=") + literalText(rewrite->selected.otherLiteral));
      addLiteralPositionFields(fields, "selected", rewrite->selected.selectedLiteral.selectedLiteral, 0);
      addLiteralPositionFields(fields, "other", rewrite->selected.otherLiteral, 1);
      fields.push_back(std::string("lhs=") + termText(rewrite->rewrite.lhs));
      fields.push_back(std::string("target=") + termText(rewrite->rewrite.rewritten));
      std::string renderedRewriteTerm;
      if (renderTermForExtra(rewrite->rewrite.lhs, renderedRewriteTerm)) {
        fields.push_back("lhs_term=" + renderedRewriteTerm);
      }
      if (renderTermForExtra(rewrite->rewrite.rewritten, renderedRewriteTerm)) {
        fields.push_back("target_term=" + renderedRewriteTerm);
      }
      Kernel::TermList rewriteSort;
      std::string rewriteSortText;
      if (Kernel::SortHelper::tryGetResultSort(rewrite->rewrite.lhs, rewriteSort)
        && sortToMegalodon(rewriteSort, rewriteSortText)) {
        fields.push_back("lhs_sort=" + rewriteSortText);
      }
      if (Kernel::SortHelper::tryGetResultSort(rewrite->rewrite.rewritten, rewriteSort)
        && sortToMegalodon(rewriteSort, rewriteSortText)) {
        fields.push_back("target_sort=" + rewriteSortText);
      }
      if (rewrite->selected.synthesisExtra.condition != nullptr) {
        fields.push_back(std::string("condition=") + literalText(rewrite->selected.synthesisExtra.condition));
      }
      if (rewrite->selected.synthesisExtra.thenLit != nullptr) {
        fields.push_back(std::string("then=") + literalText(rewrite->selected.synthesisExtra.thenLit));
      }
      if (rewrite->selected.synthesisExtra.elseLit != nullptr) {
        fields.push_back(std::string("else=") + literalText(rewrite->selected.synthesisExtra.elseLit));
      }
      if (info != nullptr && info->premises.size() >= 2 && info->substitutionForBanksSub.size() >= 2) {
        addLambdaSubtermFields(fields, "selected_parent", info->premises[0], &info->substitutionForBanksSub[0]);
        addLambdaSubtermFields(fields, "other_parent", info->premises[1], &info->substitutionForBanksSub[1]);
      }
      if (u->isClause()) {
        addLambdaSubtermFields(fields, "conclusion", u->asClause(), nullptr);
      }
      addParentSubstitutionFields(fields);
      emit("two_literal_rewrite", fields);
      return;
    }
    case Kernel::InferenceRule::RESOLUTION:
    case Kernel::InferenceRule::FACTORING: {
      const auto* selected = static_cast<const Inferences::TwoLiteralInferenceExtra*>(extra);
      std::vector<std::string> fields;
      fields.push_back(std::string("selected=") + literalText(selected->selectedLiteral.selectedLiteral));
      fields.push_back(std::string("other=") + literalText(selected->otherLiteral));
      addLiteralPositionFields(fields, "selected", selected->selectedLiteral.selectedLiteral, 0);
      addLiteralPositionFields(fields, "other", selected->otherLiteral, 1);
      if (selected->synthesisExtra.condition != nullptr) {
        fields.push_back(std::string("condition=") + literalText(selected->synthesisExtra.condition));
      }
      if (selected->synthesisExtra.thenLit != nullptr) {
        fields.push_back(std::string("then=") + literalText(selected->synthesisExtra.thenLit));
      }
      if (selected->synthesisExtra.elseLit != nullptr) {
        fields.push_back(std::string("else=") + literalText(selected->synthesisExtra.elseLit));
      }
      addParentSubstitutionFields(fields);
      emit("two_literal", fields);
      return;
    }
    case Kernel::InferenceRule::FORWARD_DEMODULATION:
    case Kernel::InferenceRule::BACKWARD_DEMODULATION: {
      const auto* rewrite = static_cast<const Inferences::RewriteInferenceExtra*>(extra);
      std::vector<std::string> fields;
      fields.push_back(std::string("lhs=") + termText(rewrite->lhs));
      fields.push_back(std::string("target=") + termText(rewrite->rewritten));
      std::string renderedRewriteTerm;
      if (renderTermForExtra(rewrite->lhs, renderedRewriteTerm)) {
        fields.push_back("rule_lhs=" + renderedRewriteTerm);
      }
      if (renderTermForExtra(rewrite->rewritten, renderedRewriteTerm)) {
        fields.push_back("redex=" + renderedRewriteTerm);
      }
      if (rewrite->hasRhs && renderTermForExtra(rewrite->rhs, renderedRewriteTerm)) {
        fields.push_back("rule_rhs=" + renderedRewriteTerm);
      }
      if (rewrite->hasReplacement && renderTermForExtra(rewrite->replacement, renderedRewriteTerm)) {
        fields.push_back("replacement=" + renderedRewriteTerm);
      }
      if (info == nullptr || !info->hasDemodulationRewrite) {
        for (Kernel::Unit* parent : iterTraits(u->getParents())) {
          if (!parent->isClause() || parent->asClause()->length() != 1) {
            continue;
          }
          Kernel::Literal* literal = (*parent->asClause())[0];
          if (!literal->isEquality() || !literal->isPositive()) {
            continue;
          }
          Kernel::TermList left = *literal->nthArgument(0);
          Kernel::TermList right = *literal->nthArgument(1);
          Kernel::TermList orientedRhs;
          bool oriented = false;
          if (left == rewrite->lhs || left.toString() == rewrite->lhs.toString()) {
            orientedRhs = right;
            oriented = true;
          } else if (right == rewrite->lhs || right.toString() == rewrite->lhs.toString()) {
            orientedRhs = left;
            oriented = true;
          }
          if (oriented && renderTermForExtra(orientedRhs, renderedRewriteTerm)) {
            fields.push_back("rule_rhs=" + renderedRewriteTerm);
            break;
          }
        }
      }
      if (info != nullptr && info->hasDemodulationRewrite) {
        std::string text;
        if (renderTermForExtra(info->demodulationRuleLhs, text)) {
          fields.push_back("rule_lhs=" + text);
        }
        if (renderTermForExtra(info->demodulationRuleRhs, text)) {
          fields.push_back("rule_rhs=" + text);
        }
        if (renderTermForExtra(info->demodulationRedex, text)) {
          fields.push_back("redex=" + text);
        }
        if (renderTermForExtra(info->demodulationReplacement, text)) {
          fields.push_back("replacement=" + text);
        }
        if (!info->premises.empty() && !info->substitutionForBanksSub.empty()) {
          addLambdaSubtermFields(fields, "main_parent", info->premises[0], &info->substitutionForBanksSub[0]);
        }
        if (u->isClause()) {
          addLambdaSubtermFields(fields, "conclusion", u->asClause(), nullptr);
        }
      }
      if (info == nullptr || !info->hasDemodulationRewrite) {
        bool emittedMainParent = false;
        for (Kernel::Unit* parent : iterTraits(u->getParents())) {
          if (!parent->isClause()) {
            continue;
          }
          std::string prefix = emittedMainParent ? "rewrite_parent" : "main_parent";
          addLambdaSubtermFields(fields, prefix, parent->asClause(), nullptr);
          emittedMainParent = true;
        }
      }
      if ((info == nullptr || !info->hasDemodulationRewrite) && u->isClause()) {
        addLambdaSubtermFields(fields, "conclusion", u->asClause(), nullptr);
      }
      addParentSubstitutionFields(fields);
      emit("rewrite", fields);
      return;
    }
    case Kernel::InferenceRule::EQUALITY_RESOLUTION:
    case Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION:
    case Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION: {
      const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
      std::vector<std::string> fields;
      fields.push_back(std::string("selected=") + literalText(selected->selectedLiteral));
      addLiteralPositionFields(fields, "selected", selected->selectedLiteral, 0);
      addParentSubstitutionFields(fields);
      if (parentClauses.size() == 2) {
        auto [selectedParentIndex, selectedLiteralIndex] = literalPosition(selected->selectedLiteral, 0);
        if (selectedParentIndex >= 0 && selectedLiteralIndex >= 0) {
          std::size_t mainParentIndex = static_cast<std::size_t>(selectedParentIndex);
          std::size_t sideParentIndex = mainParentIndex == 0 ? 1 : 0;
          SATSubsumption::SATSubsumptionAndResolution satSR;
          if (satSR.checkSubsumptionResolutionWithLiteral(
                parentClauses[sideParentIndex],
                parentClauses[mainParentIndex],
                static_cast<unsigned>(selectedLiteralIndex))) {
            Kernel::Substitution substitution = satSR.getBindingsForSubsumptionResolutionWithLiteral();
            fields.push_back("selected_substitution_source=sat_subsumption");
            fields.push_back("selected_substitution=" + substitutionText(substitution));
            Kernel::Literal* substituted = Kernel::SubstHelper::apply(selected->selectedLiteral, substitution);
            addSubstitutedLiteralFields(fields, "selected", substituted);
          }
        }
      }
      emit("literal", fields);
      return;
    }
    default:
      break;
  }

  std::vector<std::string> raw;
  raw.push_back(extra->toString());
  emit("raw", raw);
}

std::string MegalodonChecker::parents(Kernel::Unit* u) const
{
  std::ostringstream out;
  out << '[';
  bool first = true;
  for (auto parent : iterTraits(u->getParents())) {
    if (!first) {
      out << ',';
    }
    first = false;
    out << parent->number();
  }
  out << ']';
  return out.str();
}

std::string MegalodonChecker::unitKind(Kernel::Unit* u) const
{
  return u->isClause() ? "clause" : "formula";
}

std::string MegalodonChecker::variableName(unsigned var) const
{
  return "X" + std::to_string(var);
}

std::string MegalodonChecker::parenthesize(const std::string& value) const
{
  return "(" + value + ")";
}

namespace {

bool isHexDigit(char ch)
{
  return (ch >= '0' && ch <= '9') || (ch >= 'a' && ch <= 'f') || (ch >= 'A' && ch <= 'F');
}

int hexValue(char ch)
{
  if (ch >= '0' && ch <= '9') {
    return ch - '0';
  }
  if (ch >= 'a' && ch <= 'f') {
    return 10 + ch - 'a';
  }
  if (ch >= 'A' && ch <= 'F') {
    return 10 + ch - 'A';
  }
  return 0;
}

bool isMegalodonNameStart(char ch)
{
  return ch == '_' || (ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z');
}

bool isMegalodonNameChar(char ch)
{
  return isMegalodonNameStart(ch) || ch == '\'' || (ch >= '0' && ch <= '9');
}

bool isReservedMegalodonName(const std::string& name)
{
  static const std::set<std::string> reserved = {
    "Axiom", "Definition", "Infix", "Qed", "Theorem", "Variable",
    "admit", "claim", "else", "exists", "forall", "fun", "if", "in",
    "let", "prop", "set", "then", "vampire_and", "vampire_eq",
    "vampire_false", "vampire_or"
  };
  return reserved.find(name) != reserved.end();
}

std::string unquoteTptpName(const std::string& name)
{
  if (name.size() < 2 || name.front() != '\'' || name.back() != '\'') {
    return name;
  }
  std::ostringstream out;
  for (std::size_t i = 1; i + 1 < name.size(); ++i) {
    if (name[i] == '\\' && i + 2 < name.size()) {
      ++i;
    }
    out << name[i];
  }
  return out.str();
}

}

std::string MegalodonChecker::decodeMegalodonTptpName(const std::string& tptpName) const
{
  std::string encoded = unquoteTptpName(tptpName);
  if (encoded == "emptyname") {
    return encoded;
  }
  if (encoded.rfind("c_", 0) == 0 && encoded.size() > 2) {
    char firstPayload = encoded[2];
    if (firstPayload == '_' || (firstPayload >= 'A' && firstPayload <= 'Z') || (firstPayload >= '0' && firstPayload <= '9')) {
      encoded = encoded.substr(2);
    }
  }

  std::ostringstream out;
  for (std::size_t i = 0; i < encoded.size(); ++i) {
    if (encoded[i] == '_' && i + 2 < encoded.size() && isHexDigit(encoded[i + 1]) && isHexDigit(encoded[i + 2])) {
      out << static_cast<char>(hexValue(encoded[i + 1]) * 16 + hexValue(encoded[i + 2]));
      i += 2;
    } else {
      out << encoded[i];
    }
  }
  return out.str();
}

std::string MegalodonChecker::sanitizeMegalodonName(const std::string& name, const std::string& fallbackPrefix) const
{
  if (name.empty()) {
    return fallbackPrefix;
  }
  std::ostringstream out;
  if (!isMegalodonNameStart(name[0])) {
    out << fallbackPrefix << '_';
  }
  for (char ch : name) {
    if (isMegalodonNameChar(ch)) {
      out << ch;
    } else {
      out << '_';
    }
  }
  std::string sanitized = out.str();
  if (sanitized.empty() || isReservedMegalodonName(sanitized)) {
    sanitized = fallbackPrefix + "_" + sanitized;
  }
  if (sanitized.size() > 1 && sanitized[0] == 'X' && std::all_of(sanitized.begin() + 1, sanitized.end(), [](char ch) { return std::isdigit(static_cast<unsigned char>(ch)); })) {
    sanitized = fallbackPrefix + "_" + sanitized;
  }
  return sanitized;
}

std::string MegalodonChecker::recoverMegalodonSymbolName(const std::string& tptpName, const std::string& fallbackPrefix)
{
  std::string decoded = decodeMegalodonTptpName(tptpName);
  std::string candidate = sanitizeMegalodonName(decoded, fallbackPrefix);
  if (_usedSymbolNames.insert(candidate).second) {
    return candidate;
  }

  for (unsigned i = 1;; ++i) {
    std::string renamed = candidate + "_" + std::to_string(i);
    if (_usedSymbolNames.insert(renamed).second) {
      return renamed;
    }
  }
}

std::string MegalodonChecker::functionName(unsigned functor)
{
  auto found = _functions.find(functor);
  if (found != _functions.end()) {
    return found->second;
  }
  std::string name = recoverMegalodonSymbolName(env.signature->functionName(functor), "f");
  _functions.emplace(functor, name);
  return name;
}

std::string MegalodonChecker::predicateName(unsigned predicate)
{
  auto found = _predicates.find(predicate);
  if (found != _predicates.end()) {
    return found->second;
  }
  std::string name = recoverMegalodonSymbolName(env.signature->predicateName(predicate), "p");
  _predicates.emplace(predicate, name);
  return name;
}

bool MegalodonChecker::sortToMegalodon(Kernel::TermList sort, std::string& result)
{
  if (sort.isTerm() && sort.term()->isSort()) {
    Kernel::AtomicSort* atomic = static_cast<Kernel::AtomicSort*>(sort.term());
    if (atomic->isBoolSort()) {
      result = "prop";
      return true;
    }
    if (sort == Kernel::AtomicSort::defaultSort()) {
      result = "set";
      return true;
    }
  }
  std::string printed = sort.toString();
  if (printed == "$o") {
    result = "prop";
    return true;
  }
  if (printed == "$i") {
    result = "set";
    return true;
  }
  if (sort.isArrowSort()) {
    std::string domain;
    std::string range;
    if (!sortToMegalodon(sort.domain(), domain) || !sortToMegalodon(sort.result(), range)) {
      return false;
    }
    if (sort.domain().isArrowSort()) {
      domain = parenthesize(domain);
    }
    result = domain + "->" + range;
    return true;
  }
  return false;
}

std::string MegalodonChecker::functionDeclaration(unsigned functor, const std::string& name)
{
  Kernel::OperatorType* type = env.signature->getFunction(functor)->fnType();
  std::vector<std::string> parts;
  for (unsigned i = type->numTypeArguments(); i < type->arity(); ++i) {
    std::string argSort;
    if (!sortToMegalodon(type->arg(i), argSort)) {
      return "";
    }
    if (type->arg(i).isArrowSort()) {
      argSort = parenthesize(argSort);
    }
    parts.push_back(argSort);
  }
  std::string resultSort;
  if (!sortToMegalodon(type->result(), resultSort)) {
    return "";
  }
  parts.push_back(resultSort);

  std::ostringstream out;
  out << "Variable " << name << ":";
  for (unsigned i = 0; i < parts.size(); ++i) {
    if (i != 0) {
      out << "->";
    }
    out << parts[i];
  }
  out << ".";
  return out.str();
}

std::string MegalodonChecker::predicateDeclaration(unsigned predicate, const std::string& name)
{
  Kernel::OperatorType* type = env.signature->getPredicate(predicate)->predType();
  std::ostringstream out;
  out << "Variable " << name << ":";
  bool needsArrow = false;
  for (unsigned i = type->numTypeArguments(); i < type->arity(); ++i) {
    std::string argSort;
    if (!sortToMegalodon(type->arg(i), argSort)) {
      return "";
    }
    if (type->arg(i).isArrowSort()) {
      argSort = parenthesize(argSort);
    }
    if (needsArrow) {
      out << "->";
    }
    out << argSort;
    needsArrow = true;
  }
  if (needsArrow) {
    out << "->";
  }
  out << "prop.";
  return out.str();
}

bool MegalodonChecker::recordEqualitySort(Kernel::TermList sort)
{
  std::string sortText;
  if (!sortToMegalodon(sort, sortText)) {
    return false;
  }
  if (!_equalitySort.empty() && _equalitySort != sortText) {
    return false;
  }
  _usesEquality = true;
  _equalitySort = sortText;
  return true;
}

std::string MegalodonChecker::equalityDefinition() const
{
  std::string sortText = _equalitySort.empty() ? "set" : _equalitySort;
  std::string argumentSort = sortText.find("->") == std::string::npos ? sortText : parenthesize(sortText);
  return "Definition vampire_eq_set : " + argumentSort + "->" + argumentSort
    + "->prop := fun x y:" + sortText
    + " => forall Q:" + argumentSort + "->prop, Q x -> Q y.";
}

std::string MegalodonChecker::propEqualityDefinition() const
{
  return "Definition vampire_eq_prop : prop->prop->prop := fun x y:prop => forall Q:prop->prop, Q x -> Q y.";
}

bool MegalodonChecker::termToMegalodon(Kernel::TermList term, std::string& result)
{
  std::map<unsigned, Kernel::TermList> substitution;
  return termToMegalodon(term, substitution, result);
}

bool MegalodonChecker::termToMegalodon(Kernel::TermList term, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result)
{
  if (_renderDepth > 512) {
    return false;
  }
  struct RenderDepthGuard {
    unsigned& depth;
    RenderDepthGuard(unsigned& depth) : depth(depth) { ++depth; }
    ~RenderDepthGuard() { --depth; }
  } renderDepthGuard(_renderDepth);

  if (HOL::isTrue(term)) {
    _usesTrue = true;
    result = "vampire_true";
    return true;
  }
  if (HOL::isFalse(term)) {
    _usesFalse = true;
    result = "vampire_false";
    return true;
  }
  if (term.isVar()) {
    std::set<unsigned> seen;
    Kernel::TermList current = term;
    while (current.isVar()) {
      auto inserted = seen.insert(current.var());
      if (!inserted.second) {
        result = variableName(current.var());
        return true;
      }
      auto found = substitution.find(current.var());
      if (found == substitution.end() || found->second == current) {
        result = variableName(current.var());
        return true;
      }
      current = found->second;
    }
    return termToMegalodon(current, substitution, result);
  }
  if (term.isApplication()) {
    std::vector<Kernel::TermList> args;
    Kernel::TermList head = term;
    while (head.isApplication()) {
      args.push_back(head.rhs());
      head = head.lhs();
    }

    std::string headText;
    if (!termToMegalodon(head, substitution, headText)) {
      return false;
    }
    std::ostringstream out;
    out << headText;
    for (auto it = args.rbegin(); it != args.rend(); ++it) {
      std::string arg;
      if (!termToMegalodon(*it, substitution, arg)) {
        return false;
      }
      if (it->isApplication()
        || (it->isTerm() && (it->term()->isSpecial() || it->term()->numTermArguments() > 0))) {
        arg = parenthesize(arg);
      }
      out << ' ' << arg;
    }
    result = out.str();
    return true;
  }
  if (term.isTerm() && term.term()->isSpecial()) {
    Kernel::Term* special = term.term();
    switch (special->specialFunctor()) {
      case Kernel::SpecialFunctor::FORMULA:
        return formulaToMegalodon(special->getSpecialData()->getFormula(), substitution, result);
      case Kernel::SpecialFunctor::LAMBDA: {
        const Kernel::Term::SpecialTermData* data = special->getSpecialData();
        std::string body;
        Kernel::TermList lambdaBody = data->getLambdaExp();
        if (lambdaBody.isTerm() && lambdaBody.term()->isFormula()) {
          if (!formulaToMegalodon(lambdaBody.term()->getSpecialData()->getFormula(), substitution, body)) {
            return false;
          }
        } else if (!termToMegalodon(lambdaBody, substitution, body)) {
          return false;
        }

        std::vector<std::pair<unsigned, Kernel::TermList>> vars;
        Kernel::VSList::Iterator vit(data->getLambdaVars());
        while (vit.hasNext()) {
          vars.push_back(vit.next());
        }
        for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
          std::string sort;
          if (!sortToMegalodon(it->second, sort)) {
            return false;
          }
          body = "fun " + variableName(it->first) + ":" + sort + " => " + body;
        }
        result = parenthesize(body);
        return true;
      }
      default:
        return false;
    }
  }
  if (!term.isTerm()) {
    return false;
  }

  Kernel::Term* t = term.term();
  std::string name = functionName(t->functor());
  if (t->numTermArguments() == 0) {
    result = name;
    return true;
  }

  std::ostringstream out;
  out << name;
  for (unsigned i = 0; i < t->numTermArguments(); ++i) {
    std::string arg;
    if (!termToMegalodon(t->termArg(i), substitution, arg)) {
      return false;
    }
    if (t->termArg(i).isApplication()
      || (t->termArg(i).isTerm() && (t->termArg(i).term()->isSpecial() || t->termArg(i).term()->numTermArguments() > 0))) {
      arg = parenthesize(arg);
    }
    out << ' ' << arg;
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::termToMegalodonReplacing(Kernel::TermList term, Kernel::TermList needle, const std::string& replacement, std::string& result)
{
  if (term == needle) {
    result = replacement;
    return true;
  }
  if (term.isVar()) {
    result = variableName(term.var());
    return true;
  }
  if (term.isApplication()) {
    std::vector<Kernel::TermList> args;
    Kernel::TermList head = term;
    while (head.isApplication()) {
      args.push_back(head.rhs());
      head = head.lhs();
    }

    std::string headText;
    if (!termToMegalodonReplacing(head, needle, replacement, headText)) {
      return false;
    }
    std::ostringstream out;
    out << headText;
    for (auto it = args.rbegin(); it != args.rend(); ++it) {
      std::string arg;
      if (!termToMegalodonReplacing(*it, needle, replacement, arg)) {
        return false;
      }
      if (it->isApplication() || (it->isTerm() && it->term()->isSpecial())) {
        arg = parenthesize(arg);
      }
      out << ' ' << arg;
    }
    result = out.str();
    return true;
  }
  if (!term.isTerm() || term.term()->isSpecial()) {
    return false;
  }

  Kernel::Term* t = term.term();
  std::string name = functionName(t->functor());
  if (t->numTermArguments() == 0) {
    result = name;
    return true;
  }

  std::ostringstream out;
  out << name;
  for (unsigned i = 0; i < t->numTermArguments(); ++i) {
    std::string arg;
    if (!termToMegalodonReplacing(t->termArg(i), needle, replacement, arg)) {
      return false;
    }
    if (t->termArg(i).isApplication()
      || (t->termArg(i).isTerm() && (t->termArg(i).term()->isSpecial() || t->termArg(i).term()->numTermArguments() > 0))) {
      arg = parenthesize(arg);
    }
    out << ' ' << arg;
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::formulaToMegalodonReplacing(Kernel::Formula* formula, Kernel::TermList needle, const std::string& replacement, std::string& result)
{
  switch (formula->connective()) {
    case Kernel::LITERAL: {
      Kernel::Literal* literal = formula->literal();
      if (literal->isNegative()) {
        Kernel::Literal* positive = Kernel::Literal::complementaryLiteral(literal);
        if (!literalToMegalodon(positive, result)) {
          return false;
        }
        _usesFalse = true;
        result = parenthesize(result) + " -> vampire_false";
        return true;
      }
      if (literal->isEquality()) {
        std::string equalitySort;
        if (!sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort) || equalitySort != "set") {
          return false;
        }
        _usesEquality = true;
        std::string lhs;
        std::string rhs;
        if (!termToMegalodonReplacing(*literal->nthArgument(0), needle, replacement, lhs)
          || !termToMegalodonReplacing(*literal->nthArgument(1), needle, replacement, rhs)) {
          return false;
        }
        result = lhs + " = " + rhs;
        return true;
      }
      std::string name = predicateName(literal->functor());
      if (literal->arity() == 0) {
        result = name;
        return true;
      }
      std::ostringstream out;
      out << name;
      for (unsigned i = 0; i < literal->arity(); ++i) {
        std::string arg;
        if (!termToMegalodonReplacing(*literal->nthArgument(i), needle, replacement, arg)) {
          return false;
        }
        out << ' ' << arg;
      }
      result = out.str();
      return true;
    }
    case Kernel::BOOL_TERM:
      return termToMegalodonReplacing(formula->getBooleanTerm(), needle, replacement, result);
    default:
      return false;
  }
}

bool MegalodonChecker::literalToMegalodon(Kernel::Literal* literal, std::string& result)
{
  std::map<unsigned, Kernel::TermList> substitution;
  if (literal->isNegative()) {
    return false;
  }
  if (literal->isEquality()) {
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
    std::string equalitySort;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!termToMegalodon(*literal->nthArgument(0), substitution, lhs) || !termToMegalodon(*literal->nthArgument(1), substitution, rhs)) {
      return false;
    }
    if (equalitySort == "prop") {
      _usesPropEquality = true;
      result = "vampire_eq_prop " + parenthesize(lhs) + " " + parenthesize(rhs);
      return true;
    }
    if (!recordEqualitySort(equalityArgumentSort)) {
      return false;
    }
    result = lhs + " = " + rhs;
    return true;
  }

  std::string name = predicateName(literal->functor());
  if (literal->arity() == 0) {
    result = name;
    return true;
  }

  std::ostringstream out;
  out << name;
  for (unsigned i = 0; i < literal->arity(); ++i) {
    std::string arg;
    if (!termToMegalodon(*literal->nthArgument(i), substitution, arg)) {
      return false;
    }
    out << ' ' << arg;
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::skeletonLiteralToMegalodon(Kernel::Literal* literal, std::string& result)
{
  Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
  if (!literalToMegalodon(positive, result)) {
    return false;
  }
  if (literal->isNegative()) {
    _usesFalse = true;
    result = parenthesize(result) + " -> vampire_false";
  }
  return true;
}

bool MegalodonChecker::signedNameToMegalodon(const std::string& rawName, std::string& result)
{
  std::string name = rawName;
  bool negative = false;
  if (!name.empty() && name[0] == '~') {
    negative = true;
    name = name.substr(1);
  } else if (name.rfind("¬", 0) == 0) {
    negative = true;
    name = name.substr(2);
  }

  result = sanitizeMegalodonName(name, "split");
  if (negative) {
    _usesFalse = true;
    result = parenthesize(result) + " -> vampire_false";
  }
  return true;
}

bool MegalodonChecker::skeletonSplitLiteralToMegalodon(unsigned split, std::string& result)
{
  return signedNameToMegalodon(Saturation::Splitter::getFormulaStringFromName(split, true), result);
}

bool MegalodonChecker::skeletonDisjunctionToMegalodon(const std::vector<std::string>& literals, std::string& result)
{
  if (literals.empty()) {
    _usesFalse = true;
    result = "vampire_false";
    return true;
  }
  if (literals.size() == 1) {
    result = literals[0];
    return true;
  }
  _usesDisjunction = true;
  result = "vampire_or " + parenthesize(literals[0]) + " " + parenthesize(literals[1]);
  for (std::size_t i = 2; i < literals.size(); ++i) {
    result = "vampire_or " + parenthesize(result) + " " + parenthesize(literals[i]);
  }
  return true;
}

bool MegalodonChecker::skeletonClauseToMegalodon(Kernel::Clause* clause, std::string& result)
{
  std::vector<std::string> literals;
  literals.reserve(clause->length());
  for (Kernel::Literal* literal : clause->iterLits()) {
    std::string proposition;
    if (!skeletonLiteralToMegalodon(literal, proposition)) {
      return false;
    }
    literals.push_back(proposition);
  }
  if (clause->splits() && !clause->splits()->isEmpty()) {
    auto split = clause->splits()->iter();
    while (split.hasNext()) {
      std::string proposition;
      if (!skeletonSplitLiteralToMegalodon(split.next(), proposition)) {
        return false;
      }
      literals.push_back(proposition);
    }
  }
  if (!skeletonDisjunctionToMegalodon(literals, result)) {
    return false;
  }

  Lib::DHMap<unsigned, Kernel::TermList> varSorts;
  Kernel::SortHelper::collectVariableSorts(clause, varSorts);
  std::set<unsigned> vars;
  for (Kernel::Literal* literal : clause->iterLits()) {
    Kernel::TermVarIterator vit(literal);
    while (vit.hasNext()) {
      vars.insert(vit.next());
    }
  }
  for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
    Kernel::TermList sort;
    if (!varSorts.find(*it, sort)) {
      return false;
    }
    std::string sortText;
    if (!sortToMegalodon(sort, sortText)) {
      return false;
    }
    result = "forall " + variableName(*it) + ":" + sortText + ", " + result;
  }
  return true;
}

bool MegalodonChecker::certificateTermJson(Kernel::TermList term, std::string& result)
{
  if (term.isVar()) {
    result = "{\"var\":" + quote(variableName(term.var())) + "}";
    return true;
  }
  if (term.isApplication()) {
    std::string lhs;
    std::string rhs;
    if (!certificateTermJson(term.lhs(), lhs) || !certificateTermJson(term.rhs(), rhs)) {
      return false;
    }
    result = "{\"apply\":[" + lhs + "," + rhs + "]}";
    return true;
  }
  if (!term.isTerm() || term.term()->isSpecial()) {
    return false;
  }

  Kernel::Term* t = term.term();
  std::string name = functionName(t->functor());
  if (t->numTermArguments() == 0) {
    result = "{\"const\":" + quote(name) + "}";
    return true;
  }

  std::ostringstream out;
  out << "{\"app\":" << quote(name) << ",\"args\":[";
  for (unsigned i = 0; i < t->numTermArguments(); ++i) {
    if (i != 0) {
      out << ',';
    }
    std::string arg;
    if (!certificateTermJson(t->termArg(i), arg)) {
      return false;
    }
    out << arg;
  }
  out << "]}";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateAtomJson(Kernel::Literal* literal, std::string& result)
{
  Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
  if (positive->isEquality()) {
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(positive);
    std::string equalitySort;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!certificateTermJson(*positive->nthArgument(0), lhs) || !certificateTermJson(*positive->nthArgument(1), rhs)) {
      return false;
    }
    if (equalitySort == "set") {
      result = "{\"eq\":[" + lhs + "," + rhs + "]}";
    } else {
      result = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    return true;
  }

  std::ostringstream out;
  out << "{\"pred\":" << quote(predicateName(positive->functor())) << ",\"args\":[";
  for (unsigned i = 0; i < positive->arity(); ++i) {
    if (i != 0) {
      out << ',';
    }
    std::string arg;
    if (!certificateTermJson(*positive->nthArgument(i), arg)) {
      return false;
    }
    out << arg;
  }
  out << "]}";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateLiteralJson(Kernel::Literal* literal, std::string& result)
{
  std::string atom;
  if (!certificateAtomJson(literal, atom)) {
    return false;
  }
  std::ostringstream out;
  out << "{\"polarity\":" << (literal->isPositive() ? "true" : "false") << ",\"atom\":" << atom << "}";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateClauseJson(Kernel::Clause* clause, std::string& result)
{
  if (clause->splits() && !clause->splits()->isEmpty()) {
    return false;
  }

  std::ostringstream out;
  out << '[';
  bool first = true;
  for (Kernel::Literal* literal : clause->iterLits()) {
    std::string rendered;
    if (!certificateLiteralJson(literal, rendered)) {
      return false;
    }
    if (!first) {
      out << ',';
    }
    first = false;
    out << rendered;
  }
  out << ']';
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateSubstitutedEqualityLiteralJson(
  Kernel::Literal* literal,
  const Kernel::Substitution& substitution,
  bool swapEquality,
  std::string& result)
{
  if (!literal->isEquality()) {
    return false;
  }
  Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
  std::string equalitySort;
  std::string lhs;
  std::string rhs;
  unsigned lhsIndex = swapEquality ? 1 : 0;
  unsigned rhsIndex = swapEquality ? 0 : 1;
  if (!sortToMegalodon(equalityArgumentSort, equalitySort)
    || !certificateTermJson(Kernel::SubstHelper::apply(*literal->nthArgument(lhsIndex), substitution), lhs)
    || !certificateTermJson(Kernel::SubstHelper::apply(*literal->nthArgument(rhsIndex), substitution), rhs)) {
    return false;
  }
  std::string atom;
  if (equalitySort == "set") {
    atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
  } else {
    atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
  }
  result = "{\"polarity\":";
  result += literal->isPositive() ? "true" : "false";
  result += ",\"atom\":" + atom + "}";
  return true;
}

bool MegalodonChecker::certificateSubstitutedLiteralPreservingEqualityJson(
  Kernel::Literal* literal,
  const Kernel::Substitution& substitution,
  std::string& result)
{
  if (literal->isEquality()) {
    return certificateSubstitutedEqualityLiteralJson(literal, substitution, false, result);
  }

  Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
  return certificateLiteralJson(substituted, result);
}

bool MegalodonChecker::certificateSubstitutedClausePreservingEqualityJson(
  Kernel::Clause* clause,
  const Kernel::Substitution& substitution,
  std::string& result)
{
  std::ostringstream out;
  out << '[';
  for (unsigned i = 0; i < clause->length(); ++i) {
    if (i != 0) {
      out << ',';
    }
    std::string literalJson;
    if (!certificateSubstitutedLiteralPreservingEqualityJson((*clause)[i], substitution, literalJson)) {
      return false;
    }
    out << literalJson;
  }
  out << ']';
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateDefinitionInputStepJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::FUNCTION_DEFINITION) {
    return false;
  }
  if (!_is->hasIntroducedSymbols(unit)) {
    return false;
  }
  auto& symbols = _is->getIntroducedSymbols(unit);
  if (symbols.size() != 1 || symbols.top().first != SymbolType::FUNC) {
    return false;
  }
  Kernel::Clause* clause = unit->asClause();
  if (clause->length() != 1) {
    return false;
  }
  Kernel::Literal* literal = (*clause)[0];
  if (!literal->isEquality() || !literal->isPositive()) {
    return false;
  }

  const std::string symbolName = functionName(symbols.top().second);
  const std::string symbolJson = "{\"const\":" + quote(symbolName) + "}";

  std::string lhs;
  std::string rhs;
  if (!certificateTermJson(*literal->nthArgument(0), lhs)
    || !certificateTermJson(*literal->nthArgument(1), rhs)) {
    return false;
  }

  std::string value;
  if (lhs == symbolJson) {
    value = rhs;
  } else if (rhs == symbolJson) {
    value = lhs;
  } else {
    return false;
  }

  std::string equalitySort;
  if (!sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort)) {
    return false;
  }

  std::ostringstream out;
  out << "{\"rule\":\"definition_input\","
      << "\"symbol\":" << quote(symbolName) << ','
      << "\"sort\":" << quote(equalitySort) << ','
      << "\"value\":" << value << ','
      << "\"source\":{\"kind\":\"vampire_function_definition\","
      << "\"name\":" << quote("u" + std::to_string(unit->number())) << "}}";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateResolveStepJson(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::RESOLUTION
      && rule != Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION
    )) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return false;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2) {
    return false;
  }

  auto containsLiteral = [](Kernel::Clause* clause, Kernel::Literal* literal) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        return true;
      }
    }
    return false;
  };
  auto appendClauseExcept = [&](std::vector<std::string>& literals, Kernel::Clause* clause, Kernel::Literal* excluded) {
    bool excludedOne = false;
    for (Kernel::Literal* literal : clause->iterLits()) {
      if (!excludedOne && literal == excluded) {
        excludedOne = true;
        continue;
      }
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    return excludedOne;
  };
  auto renderedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    return true;
  };
  auto complementary = [&](Kernel::Literal* left, Kernel::Literal* right) {
    if (left == nullptr || right == nullptr || left->isPositive() == right->isPositive()) {
      return false;
    }
    std::string leftAtom;
    std::string rightAtom;
    return certificateAtomJson(left, leftAtom)
      && certificateAtomJson(right, rightAtom)
      && leftAtom == rightAtom;
  };
  auto stepForOrientation = [&](Kernel::Literal* leftPivot, Kernel::Literal* rightPivot, std::string& stepJson) {
    if (!containsLiteral(parents[0], leftPivot) || !containsLiteral(parents[1], rightPivot)) {
      return false;
    }
    if (!complementary(leftPivot, rightPivot)) {
      return false;
    }

    std::vector<std::string> expected;
    if (!appendClauseExcept(expected, parents[0], leftPivot)
      || !appendClauseExcept(expected, parents[1], rightPivot)) {
      return false;
    }
    std::vector<std::string> actual;
    if (!renderedClause(unit->asClause(), actual)) {
      return false;
    }
    std::sort(expected.begin(), expected.end());
    std::sort(actual.begin(), actual.end());
    if (expected != actual) {
      return false;
    }

    std::string pivot;
    if (!certificateLiteralJson(leftPivot, pivot)) {
      return false;
    }
    stepJson = "{\"rule\":\"resolve\","
      "\"parents\":["
      + quote("u" + std::to_string(parents[0]->number())) + ","
      + quote("u" + std::to_string(parents[1]->number())) + "],"
      "\"pivot\":" + pivot + "}";
    return true;
  };

  if (rule == Kernel::InferenceRule::RESOLUTION) {
    const auto* selected = static_cast<const Inferences::TwoLiteralInferenceExtra*>(extra);
    if (stepForOrientation(selected->selectedLiteral.selectedLiteral, selected->otherLiteral, result)) {
      return true;
    }
    return stepForOrientation(selected->otherLiteral, selected->selectedLiteral.selectedLiteral, result);
  }

  const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
  Kernel::Literal* selectedLiteral = selected->selectedLiteral;
  if (selectedLiteral == nullptr) {
    return false;
  }
  for (unsigned parentIndex = 0; parentIndex < 2; ++parentIndex) {
    if (!containsLiteral(parents[parentIndex], selectedLiteral)) {
      continue;
    }
    unsigned otherParentIndex = parentIndex == 0 ? 1 : 0;
    for (Kernel::Literal* candidate : parents[otherParentIndex]->iterLits()) {
      if (!complementary(selectedLiteral, candidate)) {
        continue;
      }
      if (parentIndex == 0) {
        if (stepForOrientation(selectedLiteral, candidate, result)) {
          return true;
        }
      } else if (stepForOrientation(candidate, selectedLiteral, result)) {
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateEqualityResolutionStepJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::EQUALITY_RESOLUTION
      && rule != Kernel::InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION
      && rule != Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL
    )) {
    return false;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 1) {
    return false;
  }
  Kernel::Clause* parent = parents[0];
  Kernel::Substitution emptySubstitution;
  const Kernel::Substitution* selectedSubstitution = &emptySubstitution;
  if (replayInfo != nullptr
    && replayInfo->premises.size() == 1
    && replayInfo->substitutionForBanksSub.size() == 1) {
    selectedSubstitution = &replayInfo->substitutionForBanksSub[0];
  }

  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };
  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };

  auto isNegativeReflexiveEquality = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isNegative()) {
      return false;
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, *selectedSubstitution);
    std::string lhs;
    std::string rhs;
    return certificateTermJson(*substituted->nthArgument(0), lhs)
      && certificateTermJson(*substituted->nthArgument(1), rhs)
      && lhs == rhs;
  };
  auto substitutedConclusionWithout = [&](Kernel::Literal* selectedLiteral, std::vector<std::string>& expected, std::vector<std::pair<std::string, std::string>>& symmetryCandidates) {
    bool foundSelected = false;
    for (Kernel::Literal* literal : parent->iterLits()) {
      if (!foundSelected && literal == selectedLiteral) {
        foundSelected = true;
        continue;
      }
      std::string rendered;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, *selectedSubstitution, rendered)) {
        return false;
      }
      expected.push_back(rendered);
      if (literal->isEquality()) {
        std::string swapped;
        if (!certificateSubstitutedEqualityLiteralJson(literal, *selectedSubstitution, true, swapped)) {
          return false;
        }
        if (rendered != swapped) {
          symmetryCandidates.push_back({rendered, swapped});
        }
      }
    }
    if (!foundSelected) {
      return false;
    }
    std::sort(expected.begin(), expected.end());
    expected.erase(std::unique(expected.begin(), expected.end()), expected.end());
    return true;
  };
  auto normalizedActualClause = [&](std::vector<std::string>& actual) {
    for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      actual.push_back(rendered);
    }
    std::sort(actual.begin(), actual.end());
    actual.erase(std::unique(actual.begin(), actual.end()), actual.end());
    return true;
  };
  auto canNormalizeBySymmetry = [&](const std::vector<std::string>& source, const std::vector<std::string>& actual, const std::vector<std::pair<std::string, std::string>>& symmetryCandidates, std::vector<std::pair<std::string, std::string>>& flips) {
    std::vector<std::string> current = source;
    flips.clear();
    for (std::size_t guard = 0; current != actual && guard < symmetryCandidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : symmetryCandidates) {
        if (std::find(actual.begin(), actual.end(), candidate.second) == actual.end()) {
          continue;
        }
        auto currentIt = std::find(current.begin(), current.end(), candidate.first);
        if (currentIt == current.end()) {
          continue;
        }
        *currentIt = candidate.second;
        std::sort(current.begin(), current.end());
        current.erase(std::unique(current.begin(), current.end()), current.end());
        flips.push_back(candidate);
        changed = true;
        break;
      }
      if (!changed) {
        break;
      }
    }
    return current == actual;
  };
  auto emitStep = [&](Kernel::Literal* selectedLiteral) {
    if (!isNegativeReflexiveEquality(selectedLiteral)) {
      return false;
    }
    std::vector<std::string> expected;
    std::vector<std::pair<std::string, std::string>> symmetryCandidates;
    std::vector<std::string> actual;
    if (!substitutedConclusionWithout(selectedLiteral, expected, symmetryCandidates)
      || !normalizedActualClause(actual)) {
      return false;
    }

    std::string literal;
    if (!certificateLiteralJson(selectedLiteral, literal)) {
      return false;
    }
    std::string substitution;
    if (!certificateSubstitutionJson(*selectedSubstitution, substitution)) {
      return false;
    }

    std::string stepBase = "u" + std::to_string(unit->number());
    std::string equalityResolutionStep =
      "{\"rule\":\"equality_resolution\","
      "\"parents\":["
      + quote("u" + std::to_string(parent->number())) + "],"
      "\"literal\":" + literal + ","
      "\"substitution\":" + substitution + "}";
    if (expected == actual) {
      result = equalityResolutionStep;
      return true;
    }

    std::vector<std::pair<std::string, std::string>> flips;
    if (!canNormalizeBySymmetry(expected, actual, symmetryCandidates, flips)) {
      return false;
    }

    std::vector<std::string> steps;
    std::string currentStepId = stepBase + "_eqres";
    steps.push_back(
      "{\"id\":" + quote(currentStepId) + ","
      "\"rule\":\"equality_resolution\","
      "\"parents\":[" + quote("u" + std::to_string(parent->number())) + "],"
      "\"literal\":" + literal + ","
      "\"substitution\":" + substitution + ","
      "\"clause\":" + jsonArray(expected) + "}");
    std::vector<std::string> currentClause = expected;
    for (std::size_t index = 0; index < flips.size(); ++index) {
      const auto& flip = flips[index];
      auto literalIt = std::find(currentClause.begin(), currentClause.end(), flip.first);
      if (literalIt == currentClause.end()) {
        return false;
      }
      *literalIt = flip.second;
      std::sort(currentClause.begin(), currentClause.end());
      currentClause.erase(std::unique(currentClause.begin(), currentClause.end()), currentClause.end());
      std::string normalizeStepId = index + 1 == flips.size()
        ? stepBase
        : stepBase + "_normalize" + std::to_string(index);
      steps.push_back(
        "{\"id\":" + quote(normalizeStepId) + ","
        "\"rule\":\"equality_symmetry\","
        "\"parents\":[" + quote(currentStepId) + "],"
        "\"literal\":" + flip.first + ","
        "\"clause\":" + jsonArray(currentClause) + "}");
      currentStepId = normalizeStepId;
    }
    result = jsonArray(steps);
    return true;
  };

  if (rule == Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL) {
    for (Kernel::Literal* literal : parent->iterLits()) {
      if (emitStep(literal)) {
        return true;
      }
    }
    return false;
  }

  const auto* extra = env.proofExtra.find(unit);
  if (extra != nullptr) {
    const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
    if (emitStep(selected->selectedLiteral)) {
      return true;
    }
  }
  for (Kernel::Literal* literal : parent->iterLits()) {
    if (emitStep(literal)) {
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::certificateFactorStepJson(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FACTORING
      && rule != Kernel::InferenceRule::REMOVE_DUPLICATE_LITERALS
    )) {
    return false;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 1) {
    return false;
  }
  Kernel::Clause* parent = parents[0];

  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };

  std::vector<std::string> expected;
  std::vector<std::string> actual;
  if (!normalizedClause(parent, expected)
    || !normalizedClause(unit->asClause(), actual)
    || expected != actual) {
    return false;
  }
  if (parent->length() <= unit->asClause()->length()) {
    return false;
  }

  result = "{\"rule\":\"factor\","
    "\"parents\":["
    + quote("u" + std::to_string(parent->number())) + "]}";
  return true;
}

bool MegalodonChecker::certificateEqualityFactoringStepJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::EQUALITY_FACTORING
    || replayInfo == nullptr
    || replayInfo->premises.size() != 1
    || replayInfo->substitutionForBanksSub.size() != 1) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return false;
  }
  const auto* rewrite = static_cast<const Inferences::TwoLiteralRewriteInferenceExtra*>(extra);

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 1 || parents[0] != replayInfo->premises[0]) {
    return false;
  }
  Kernel::Clause* parent = parents[0];
  const Kernel::Substitution& substitution = replayInfo->substitutionForBanksSub[0];
  Kernel::Literal* selected = rewrite->selected.selectedLiteral.selectedLiteral;
  Kernel::Literal* other = rewrite->selected.otherLiteral;
  Kernel::TermList selectedLhs = rewrite->rewrite.lhs;
  Kernel::TermList otherRhs = rewrite->rewrite.rewritten;

  auto containsLiteral = [](Kernel::Clause* clause, Kernel::Literal* literal) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        return true;
      }
    }
    return false;
  };
  if (selected == nullptr
    || other == nullptr
    || !selected->isEquality()
    || !other->isEquality()
    || !selected->isPositive()
    || !other->isPositive()
    || !containsLiteral(parent, selected)
    || !containsLiteral(parent, other)) {
    return false;
  }

  bool selectedLhsIsLeft = selectedLhs == *selected->nthArgument(0);
  bool selectedLhsIsRight = selectedLhs == *selected->nthArgument(1);
  bool otherRhsIsLeft = otherRhs == *other->nthArgument(0);
  bool otherRhsIsRight = otherRhs == *other->nthArgument(1);
  if ((!selectedLhsIsLeft && !selectedLhsIsRight)
    || (!otherRhsIsLeft && !otherRhsIsRight)) {
    return false;
  }
  Kernel::TermList selectedRhs = selectedLhsIsLeft
    ? *selected->nthArgument(1)
    : *selected->nthArgument(0);
  Kernel::TermList otherLhs = otherRhsIsLeft
    ? *other->nthArgument(1)
    : *other->nthArgument(0);

  Kernel::TermList selectedLhsSubstituted = Kernel::SubstHelper::apply(selectedLhs, substitution);
  Kernel::TermList otherLhsSubstituted = Kernel::SubstHelper::apply(otherLhs, substitution);
  if (selectedLhsSubstituted != otherLhsSubstituted) {
    return false;
  }

  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };
  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto normalizeLiterals = [](std::vector<std::string>& literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
  };
  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string literalJson;
      if (!certificateLiteralJson(literal, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    normalizeLiterals(literals);
    return true;
  };

  std::vector<std::string> expected;
  std::vector<std::pair<std::string, std::string>> symmetryCandidates;
  bool skippedSelected = false;
  for (unsigned i = 0; i < parent->length(); ++i) {
    Kernel::Literal* literal = (*parent)[i];
    if (!skippedSelected && literal == selected) {
      skippedSelected = true;
      continue;
    }
    std::string literalJson;
    if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
      return false;
    }
    expected.push_back(literalJson);
    if (literal->isEquality()) {
      std::string swappedJson;
      if (!certificateSubstitutedEqualityLiteralJson(literal, substitution, true, swappedJson)) {
        return false;
      }
      if (literalJson != swappedJson) {
        symmetryCandidates.push_back({literalJson, swappedJson});
      }
    }
  }
  if (!skippedSelected) {
    return false;
  }

  Kernel::TermList equalityArgumentSort = Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(selected), substitution);
  Kernel::TermList selectedRhsSubstituted = Kernel::SubstHelper::apply(selectedRhs, substitution);
  Kernel::TermList otherRhsSubstituted = Kernel::SubstHelper::apply(otherRhs, substitution);
  Kernel::Literal* introduced = Kernel::Literal::createEquality(false, selectedRhsSubstituted, otherRhsSubstituted, equalityArgumentSort);
  std::string introducedJson;
  if (!certificateLiteralJson(introduced, introducedJson)) {
    return false;
  }
  expected.push_back(introducedJson);
  Kernel::Literal* swappedIntroduced = Kernel::Literal::createEquality(false, otherRhsSubstituted, selectedRhsSubstituted, equalityArgumentSort);
  std::string swappedIntroducedJson;
  if (!certificateLiteralJson(swappedIntroduced, swappedIntroducedJson)) {
    return false;
  }
  if (introducedJson != swappedIntroducedJson) {
    symmetryCandidates.push_back({introducedJson, swappedIntroducedJson});
  }
  normalizeLiterals(expected);

  std::vector<std::string> actual;
  if (!normalizedClause(unit->asClause(), actual)) {
    return false;
  }
  auto canNormalizeBySymmetry = [&](std::vector<std::pair<std::string, std::string>>& flips) {
    std::vector<std::string> current = expected;
    flips.clear();
    for (std::size_t guard = 0; current != actual && guard < symmetryCandidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : symmetryCandidates) {
        if (std::find(actual.begin(), actual.end(), candidate.second) == actual.end()) {
          continue;
        }
        auto currentIt = std::find(current.begin(), current.end(), candidate.first);
        if (currentIt == current.end()) {
          continue;
        }
        *currentIt = candidate.second;
        normalizeLiterals(current);
        flips.push_back(candidate);
        changed = true;
        break;
      }
      if (!changed) {
        break;
      }
    }
    return current == actual;
  };
  std::vector<std::pair<std::string, std::string>> finalSymmetryFlips;
  if (expected != actual && !canNormalizeBySymmetry(finalSymmetryFlips)) {
    return false;
  }

  std::string selectedJson;
  std::string otherJson;
  std::string selectedLhsJson;
  std::string otherRhsJson;
  std::string substitutionJson;
  if (!certificateLiteralJson(selected, selectedJson)
    || !certificateLiteralJson(other, otherJson)
    || !certificateTermJson(selectedLhs, selectedLhsJson)
    || !certificateTermJson(otherRhs, otherRhsJson)
    || !certificateSubstitutionJson(substitution, substitutionJson)) {
    return false;
  }

  std::string stepBase = "u" + std::to_string(unit->number());
  std::string equalityFactoringStep =
    "{\"rule\":\"equality_factoring\","
    "\"parents\":[" + quote("u" + std::to_string(parent->number())) + "],"
    "\"selected\":" + selectedJson + ","
    "\"other\":" + otherJson + ","
    "\"selected_lhs\":" + selectedLhsJson + ","
    "\"other_rhs\":" + otherRhsJson + ","
    "\"substitution\":" + substitutionJson + "}";
  if (finalSymmetryFlips.empty()) {
    result = equalityFactoringStep;
    return true;
  }

  std::vector<std::string> steps;
  std::string currentStepId = stepBase + "_eqfact";
  steps.push_back(
    "{\"id\":" + quote(currentStepId) + ","
    "\"rule\":\"equality_factoring\","
    "\"parents\":[" + quote("u" + std::to_string(parent->number())) + "],"
    "\"selected\":" + selectedJson + ","
    "\"other\":" + otherJson + ","
    "\"selected_lhs\":" + selectedLhsJson + ","
    "\"other_rhs\":" + otherRhsJson + ","
    "\"substitution\":" + substitutionJson + ","
    "\"clause\":" + jsonArray(expected) + "}");
  std::vector<std::string> currentClause = expected;
  for (std::size_t index = 0; index < finalSymmetryFlips.size(); ++index) {
    const auto& flip = finalSymmetryFlips[index];
    auto literalIt = std::find(currentClause.begin(), currentClause.end(), flip.first);
    if (literalIt == currentClause.end()) {
      return false;
    }
    *literalIt = flip.second;
    normalizeLiterals(currentClause);
    std::string normalizeStepId = index + 1 == finalSymmetryFlips.size()
      ? stepBase
      : stepBase + "_normalize" + std::to_string(index);
    steps.push_back(
      "{\"id\":" + quote(normalizeStepId) + ","
      "\"rule\":\"equality_symmetry\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"literal\":" + flip.first + ","
      "\"clause\":" + jsonArray(currentClause) + "}");
    currentStepId = normalizeStepId;
  }
  result = jsonArray(steps);
  return true;
}

bool MegalodonChecker::certificateParamodulateStepJson(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FORWARD_DEMODULATION
      && rule != Kernel::InferenceRule::BACKWARD_DEMODULATION
      && rule != Kernel::InferenceRule::DEFINITION_FOLDING_TWEE
      && rule != Kernel::InferenceRule::DEFINITION_FOLDING_PRED
    )) {
    return false;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2) {
    return false;
  }

  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  auto appendClauseExcept = [&](std::vector<std::string>& literals, Kernel::Clause* clause, Kernel::Literal* excluded) {
    bool excludedOne = false;
    for (Kernel::Literal* literal : clause->iterLits()) {
      if (!excludedOne && literal == excluded) {
        excludedOne = true;
        continue;
      }
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    return excludedOne;
  };
  auto renderAtomWithTopLevelReplacement = [&](Kernel::Literal* literal, unsigned position, Kernel::TermList replacement, std::string& atom) {
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (positive->isEquality()) {
      if (position > 1) {
        return false;
      }
      Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(positive);
      std::string equalitySort;
      if (!sortToMegalodon(equalityArgumentSort, equalitySort)) {
        return false;
      }
      std::string lhs;
      std::string rhs;
      if (!certificateTermJson(position == 0 ? replacement : *positive->nthArgument(0), lhs)
        || !certificateTermJson(position == 1 ? replacement : *positive->nthArgument(1), rhs)) {
        return false;
      }
      if (equalitySort == "set") {
        atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
      } else {
        atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
      }
      return true;
    }

    if (position >= positive->arity()) {
      return false;
    }
    std::ostringstream out;
    out << "{\"pred\":" << quote(predicateName(positive->functor())) << ",\"args\":[";
    for (unsigned i = 0; i < positive->arity(); ++i) {
      if (i != 0) {
        out << ',';
      }
      std::string arg;
      if (!certificateTermJson(i == position ? replacement : *positive->nthArgument(i), arg)) {
        return false;
      }
      out << arg;
    }
    out << "]}";
    atom = out.str();
    return true;
  };
  auto renderLiteralWithTopLevelReplacement = [&](Kernel::Literal* literal, unsigned position, Kernel::TermList replacement, std::string& rendered) {
    std::string atom;
    if (!renderAtomWithTopLevelReplacement(literal, position, replacement, atom)) {
      return false;
    }
    rendered = "{\"polarity\":";
    rendered += literal->isPositive() ? "true" : "false";
    rendered += ",\"atom\":" + atom + "}";
    return true;
  };

  std::vector<std::string> actual;
  if (!normalizedClause(unit->asClause(), actual)) {
    return false;
  }

  for (std::size_t equalityParentIndex = 0; equalityParentIndex < parents.size(); ++equalityParentIndex) {
    Kernel::Clause* equalityParent = parents[equalityParentIndex];
    std::size_t targetParentIndex = equalityParentIndex == 0 ? 1 : 0;
    Kernel::Clause* targetParent = parents[targetParentIndex];
    for (Kernel::Literal* equality : equalityParent->iterLits()) {
      if (!equality->isEquality() || !equality->isPositive()) {
        continue;
      }
      Kernel::TermList from = *equality->nthArgument(0);
      Kernel::TermList to = *equality->nthArgument(1);
      std::string fromJson;
      std::string toJson;
      std::string equalityJson;
      if (!certificateTermJson(from, fromJson)
        || !certificateTermJson(to, toJson)
        || !certificateLiteralJson(equality, equalityJson)) {
        continue;
      }
      for (Kernel::Literal* target : targetParent->iterLits()) {
        Kernel::Literal* positiveTarget = target->isPositive() ? target : Kernel::Literal::complementaryLiteral(target);
        unsigned topLevelTerms = positiveTarget->isEquality() ? 2 : positiveTarget->arity();
        for (unsigned position = 0; position < topLevelTerms; ++position) {
          std::string targetTermJson;
          if (!certificateTermJson(*positiveTarget->nthArgument(position), targetTermJson)
            || targetTermJson != fromJson) {
            continue;
          }
          std::vector<std::string> expected;
          if (!appendClauseExcept(expected, equalityParent, equality)
            || !appendClauseExcept(expected, targetParent, target)) {
            continue;
          }
          std::string rewrittenTarget;
          if (!renderLiteralWithTopLevelReplacement(target, position, to, rewrittenTarget)) {
            continue;
          }
          expected.push_back(rewrittenTarget);
          std::sort(expected.begin(), expected.end());
          expected.erase(std::unique(expected.begin(), expected.end()), expected.end());
          if (expected != actual) {
            continue;
          }

          std::string targetJson;
          if (!certificateLiteralJson(target, targetJson)) {
            continue;
          }
          result = "{\"rule\":\"paramodulate\","
            "\"parents\":["
            + quote("u" + std::to_string(equalityParent->number())) + ","
            + quote("u" + std::to_string(targetParent->number())) + "],"
            "\"equality\":" + equalityJson + ","
            "\"from\":" + fromJson + ","
            "\"to\":" + toJson + ","
            "\"target\":" + targetJson + ","
            "\"position\":[" + std::to_string(position) + "],"
            "\"substitution\":{}}";
          return true;
        }
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateParamodulateThenSymmetryStepsJson(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FORWARD_DEMODULATION
      && rule != Kernel::InferenceRule::BACKWARD_DEMODULATION
      && rule != Kernel::InferenceRule::DEFINITION_FOLDING_TWEE
      && rule != Kernel::InferenceRule::DEFINITION_FOLDING_PRED
    )) {
    return false;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2) {
    return false;
  }

  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  auto appendClauseExcept = [&](std::vector<std::string>& literals, Kernel::Clause* clause, Kernel::Literal* excluded) {
    bool excludedOne = false;
    for (Kernel::Literal* literal : clause->iterLits()) {
      if (!excludedOne && literal == excluded) {
        excludedOne = true;
        continue;
      }
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    return excludedOne;
  };
  auto renderEqualityAtom = [&](Kernel::Literal* literal, Kernel::TermList lhsTerm, Kernel::TermList rhsTerm, std::string& atom) {
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (!positive->isEquality()) {
      return false;
    }
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(positive);
    std::string equalitySort;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!certificateTermJson(lhsTerm, lhs) || !certificateTermJson(rhsTerm, rhs)) {
      return false;
    }
    if (equalitySort == "set") {
      atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
    } else {
      atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    return true;
  };
  auto renderEqualityLiteral = [&](Kernel::Literal* literal, Kernel::TermList lhsTerm, Kernel::TermList rhsTerm, std::string& rendered) {
    std::string atom;
    if (!renderEqualityAtom(literal, lhsTerm, rhsTerm, atom)) {
      return false;
    }
    rendered = "{\"polarity\":";
    rendered += literal->isPositive() ? "true" : "false";
    rendered += ",\"atom\":" + atom + "}";
    return true;
  };

  std::vector<std::string> actual;
  if (!normalizedClause(unit->asClause(), actual)) {
    return false;
  }

  for (std::size_t equalityParentIndex = 0; equalityParentIndex < parents.size(); ++equalityParentIndex) {
    Kernel::Clause* equalityParent = parents[equalityParentIndex];
    std::size_t targetParentIndex = equalityParentIndex == 0 ? 1 : 0;
    Kernel::Clause* targetParent = parents[targetParentIndex];
    for (Kernel::Literal* equality : equalityParent->iterLits()) {
      if (!equality->isEquality() || !equality->isPositive()) {
        continue;
      }
      Kernel::TermList from = *equality->nthArgument(0);
      Kernel::TermList to = *equality->nthArgument(1);
      std::string fromJson;
      std::string toJson;
      std::string equalityJson;
      if (!certificateTermJson(from, fromJson)
        || !certificateTermJson(to, toJson)
        || !certificateLiteralJson(equality, equalityJson)) {
        continue;
      }
      for (Kernel::Literal* target : targetParent->iterLits()) {
        Kernel::Literal* positiveTarget = target->isPositive() ? target : Kernel::Literal::complementaryLiteral(target);
        if (!positiveTarget->isEquality()) {
          continue;
        }
        for (unsigned position = 0; position < 2; ++position) {
          std::string targetTermJson;
          if (!certificateTermJson(*positiveTarget->nthArgument(position), targetTermJson)
            || targetTermJson != fromJson) {
            continue;
          }

          Kernel::TermList rewrittenLhs = position == 0 ? to : *positiveTarget->nthArgument(0);
          Kernel::TermList rewrittenRhs = position == 1 ? to : *positiveTarget->nthArgument(1);
          std::string rewrittenTarget;
          std::string swappedTarget;
          if (!renderEqualityLiteral(target, rewrittenLhs, rewrittenRhs, rewrittenTarget)
            || !renderEqualityLiteral(target, rewrittenRhs, rewrittenLhs, swappedTarget)) {
            continue;
          }

          std::vector<std::string> paramClause;
          if (!appendClauseExcept(paramClause, equalityParent, equality)
            || !appendClauseExcept(paramClause, targetParent, target)) {
            continue;
          }
          paramClause.push_back(rewrittenTarget);
          std::sort(paramClause.begin(), paramClause.end());
          paramClause.erase(std::unique(paramClause.begin(), paramClause.end()), paramClause.end());

          std::vector<std::string> symmetricClause = paramClause;
          auto rewrittenIt = std::find(symmetricClause.begin(), symmetricClause.end(), rewrittenTarget);
          if (rewrittenIt == symmetricClause.end()) {
            continue;
          }
          symmetricClause.erase(rewrittenIt);
          symmetricClause.push_back(swappedTarget);
          std::sort(symmetricClause.begin(), symmetricClause.end());
          symmetricClause.erase(std::unique(symmetricClause.begin(), symmetricClause.end()), symmetricClause.end());
          if (symmetricClause != actual) {
            continue;
          }

          std::string targetJson;
          if (!certificateLiteralJson(target, targetJson)) {
            continue;
          }
          std::string stepId = "u" + std::to_string(unit->number());
          std::string paramStepId = stepId + "_paramodulate";
          result = "["
            "{\"id\":" + quote(paramStepId) + ","
            "\"rule\":\"paramodulate\","
            "\"parents\":["
            + quote("u" + std::to_string(equalityParent->number())) + ","
            + quote("u" + std::to_string(targetParent->number())) + "],"
            "\"equality\":" + equalityJson + ","
            "\"from\":" + fromJson + ","
            "\"to\":" + toJson + ","
            "\"target\":" + targetJson + ","
            "\"position\":[" + std::to_string(position) + "],"
            "\"substitution\":{},"
            "\"clause\":" + jsonArray(paramClause) + "},"
            "{\"id\":" + quote(stepId) + ","
            "\"rule\":\"equality_symmetry\","
            "\"parents\":[" + quote(paramStepId) + "],"
            "\"literal\":" + rewrittenTarget + "}"
            "]";
          return true;
        }
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateDemodulationStepsJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FORWARD_DEMODULATION
      && rule != Kernel::InferenceRule::BACKWARD_DEMODULATION
    )
    || replayInfo == nullptr
    || !replayInfo->hasDemodulationRewrite
    || replayInfo->premises.size() != 2
    || replayInfo->substitutionForBanksSub.size() != 2) {
    return false;
  }

  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto normalize = [](std::vector<std::string>& literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
  };
  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string literalJson;
      if (!certificateLiteralJson(literal, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    normalize(literals);
    return true;
  };
  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };
  auto appendSubstitutedClauseExcept = [&](std::vector<std::string>& literals, Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::Literal* excluded) {
    bool skipped = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      Kernel::Literal* literal = (*clause)[i];
      if (!skipped && literal == excluded) {
        skipped = true;
        continue;
      }
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    return skipped;
  };
  auto positiveEqualityLiteralJson = [&](Kernel::Literal* equalityLiteral, Kernel::TermList lhsTerm, Kernel::TermList rhsTerm, std::string& rendered) {
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(equalityLiteral);
    std::string equalitySort;
    std::string lhs;
    std::string rhs;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)
      || !certificateTermJson(lhsTerm, lhs)
      || !certificateTermJson(rhsTerm, rhs)) {
      return false;
    }
    std::string atom;
    if (equalitySort == "set") {
      atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
    } else {
      atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    rendered = "{\"polarity\":true,\"atom\":" + atom + "}";
    return true;
  };
  auto substitutedClauseReplacingOneLiteralJson = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::Literal* excluded, const std::string& replacement, std::string& rendered) {
    std::vector<std::string> literals;
    bool skipped = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      Kernel::Literal* literal = (*clause)[i];
      if (!skipped && literal == excluded) {
        skipped = true;
        literals.push_back(replacement);
        continue;
      }
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    if (!skipped) {
      return false;
    }
    rendered = jsonArray(literals);
    return true;
  };
  auto collectTermPositions = [&](auto&& self, Kernel::TermList term, Kernel::TermList needle, std::vector<unsigned>& current, std::vector<std::vector<unsigned>>& positions) -> void {
    if (term == needle) {
      positions.push_back(current);
      return;
    }
    if (term.isApplication()) {
      current.push_back(0);
      self(self, term.lhs(), needle, current, positions);
      current.back() = 1;
      self(self, term.rhs(), needle, current, positions);
      current.pop_back();
      return;
    }
    if (!term.isTerm() || term.term()->isSpecial()) {
      return;
    }
    Kernel::Term* t = term.term();
    for (unsigned i = 0; i < t->numTermArguments(); ++i) {
      current.push_back(i);
      self(self, t->termArg(i), needle, current, positions);
      current.pop_back();
    }
  };
  auto collectSubstitutedLiteralAtomPositions = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, Kernel::TermList needle, std::vector<std::vector<unsigned>>& positions) {
    if (literal->isEquality()) {
      for (unsigned i = 0; i < 2; ++i) {
        std::vector<unsigned> position;
        position.push_back(i);
        collectTermPositions(collectTermPositions, Kernel::SubstHelper::apply(*literal->nthArgument(i), substitution), needle, position, positions);
      }
    } else {
      Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
      Kernel::Literal* positive = substituted->isPositive() ? substituted : Kernel::Literal::complementaryLiteral(substituted);
      for (unsigned i = 0; i < positive->arity(); ++i) {
        std::vector<unsigned> position;
        position.push_back(i);
        collectTermPositions(collectTermPositions, *positive->nthArgument(i), needle, position, positions);
      }
    }
    return !positions.empty();
  };
  auto positionJson = [](const std::vector<unsigned>& position) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < position.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << position[i];
    }
    out << ']';
    return out.str();
  };
  auto rewriteScopeJson = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, const std::vector<unsigned>& position, std::string& rendered) {
    if (position.empty()) {
      return false;
    }
    Kernel::Literal* indexed = literal->isEquality()
      ? literal
      : (literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal));
    unsigned arity = indexed->isEquality() ? 2 : indexed->arity();
    if (position[0] >= arity) {
      return false;
    }

    Kernel::TermList current = Kernel::SubstHelper::apply(*indexed->nthArgument(position[0]), substitution);
    unsigned lambdaDepth = 0;
    for (std::size_t depth = 1; depth < position.size(); ++depth) {
      unsigned index = position[depth];
      if (current.isLambdaTerm() && index == 0) {
        ++lambdaDepth;
      }
      if (current.isApplication()) {
        if (index > 1) {
          return false;
        }
        current = index == 0 ? current.lhs() : current.rhs();
        continue;
      }
      if (!current.isTerm() || current.term()->isSpecial()) {
        return false;
      }
      if (index >= current.term()->numTermArguments()) {
        return false;
      }
      current = current.term()->termArg(index);
    }

    auto dbIndex = current.deBruijnIndex();
    if (dbIndex.isNone() || dbIndex.unwrap() >= lambdaDepth) {
      return false;
    }
    rendered = "\"rewrite_scope\":{\"kind\":\"bound_lambda_var\","
      "\"lambda_depth\":" + std::to_string(lambdaDepth) + ","
      "\"db_index\":" + std::to_string(dbIndex.unwrap()) + "},";
    return true;
  };
  auto positionsJson = [&](const std::vector<std::vector<unsigned>>& positions) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < positions.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << positionJson(positions[i]);
    }
    out << ']';
    return out.str();
  };
  auto replacedSubstitutedLiteralJson = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, Kernel::TermList what, Kernel::TermList by, std::string& rendered) {
    if (literal->isEquality()) {
      Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
      std::string equalitySort;
      std::string lhs;
      std::string rhs;
      Kernel::TermList lhsTerm = Kernel::EqHelper::replace(Kernel::SubstHelper::apply(*literal->nthArgument(0), substitution), what, by);
      Kernel::TermList rhsTerm = Kernel::EqHelper::replace(Kernel::SubstHelper::apply(*literal->nthArgument(1), substitution), what, by);
      if (!sortToMegalodon(equalityArgumentSort, equalitySort)
        || !certificateTermJson(lhsTerm, lhs)
        || !certificateTermJson(rhsTerm, rhs)) {
        return false;
      }
      std::string atom;
      if (equalitySort == "set") {
        atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
      } else {
        atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
      }
      rendered = "{\"polarity\":";
      rendered += literal->isPositive() ? "true" : "false";
      rendered += ",\"atom\":" + atom + "}";
      return true;
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
    Kernel::Literal* replaced = Kernel::EqHelper::replace(substituted, what, by);
    return certificateLiteralJson(replaced, rendered);
  };

  std::vector<std::string> actual;
  if (!normalizedClause(unit->asClause(), actual)) {
    return false;
  }

  Kernel::TermList redex = replayInfo->demodulationRedex;
  Kernel::TermList replacement = replayInfo->demodulationReplacement;
  for (std::size_t equalityParentIndex = 0; equalityParentIndex < 2; ++equalityParentIndex) {
    std::size_t targetParentIndex = equalityParentIndex == 0 ? 1 : 0;
    Kernel::Clause* equalityParent = replayInfo->premises[equalityParentIndex];
    Kernel::Clause* targetParent = replayInfo->premises[targetParentIndex];
    for (Kernel::Literal* equalityLiteral : equalityParent->iterLits()) {
      if (!equalityLiteral->isEquality() || !equalityLiteral->isPositive()) {
        continue;
      }
      Kernel::TermList equalityLeft = Kernel::SubstHelper::apply(*equalityLiteral->nthArgument(0), replayInfo->substitutionForBanksSub[equalityParentIndex]);
      Kernel::TermList equalityRight = Kernel::SubstHelper::apply(*equalityLiteral->nthArgument(1), replayInfo->substitutionForBanksSub[equalityParentIndex]);
      bool needsSymmetry = false;
      if (equalityLeft == redex && equalityRight == replacement) {
        needsSymmetry = false;
      } else if (equalityLeft == replacement && equalityRight == redex) {
        needsSymmetry = true;
      } else {
        continue;
      }

      for (Kernel::Literal* targetLiteral : targetParent->iterLits()) {
        std::vector<std::vector<unsigned>> positions;
        collectSubstitutedLiteralAtomPositions(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], redex, positions);
        if (positions.empty()) {
          continue;
        }

        std::vector<std::string> paramClause;
        if (!appendSubstitutedClauseExcept(paramClause, targetParent, replayInfo->substitutionForBanksSub[targetParentIndex], targetLiteral)
          || !appendSubstitutedClauseExcept(paramClause, equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral)) {
          continue;
        }
        std::string rewrittenTargetJson;
        if (!replacedSubstitutedLiteralJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], redex, replacement, rewrittenTargetJson)) {
          continue;
        }
        paramClause.push_back(rewrittenTargetJson);
        normalize(paramClause);
        if (paramClause != actual) {
          continue;
        }

        std::string stepBase = "u" + std::to_string(unit->number());
        std::vector<std::string> steps;
        std::vector<std::string> parentIds(2);
        for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
          std::string substitutionJson;
          std::string clauseJson;
          if (!certificateSubstitutionJson(replayInfo->substitutionForBanksSub[parentIndex], substitutionJson)
            || !certificateSubstitutedClausePreservingEqualityJson(replayInfo->premises[parentIndex], replayInfo->substitutionForBanksSub[parentIndex], clauseJson)) {
            return false;
          }
          parentIds[parentIndex] = "u" + std::to_string(replayInfo->premises[parentIndex]->number());
          if (substitutionJson != "{}") {
            std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
            steps.push_back(
              "{\"id\":" + quote(substituteId) + ","
              "\"rule\":\"substitute\","
              "\"parents\":[" + quote(parentIds[parentIndex]) + "],"
              "\"substitution\":" + substitutionJson + ","
              "\"clause\":" + clauseJson + "}");
            parentIds[parentIndex] = substituteId;
          }
        }

        std::string equalityParentLiteralJson;
        std::string equalityJson;
        std::string fromJson;
        std::string toJson;
        std::string targetJson;
        std::string conclusionJson;
        if (!certificateSubstitutedLiteralPreservingEqualityJson(equalityLiteral, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityParentLiteralJson)
          || !positiveEqualityLiteralJson(equalityLiteral, redex, replacement, equalityJson)
          || !certificateTermJson(redex, fromJson)
          || !certificateTermJson(replacement, toJson)
          || !certificateSubstitutedLiteralPreservingEqualityJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], targetJson)
          || !certificateClauseJson(unit->asClause(), conclusionJson)) {
          return false;
        }

        std::string equalityParentId = parentIds[equalityParentIndex];
        if (needsSymmetry || equalityParentLiteralJson != equalityJson) {
          std::string symmetryClauseJson;
          if (!substitutedClauseReplacingOneLiteralJson(equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral, equalityJson, symmetryClauseJson)) {
            return false;
          }
          std::string symmetryStepId = stepBase + "_symmetry";
          steps.push_back(
            "{\"id\":" + quote(symmetryStepId) + ","
            "\"rule\":\"equality_symmetry\","
            "\"parents\":[" + quote(equalityParentId) + "],"
            "\"literal\":" + equalityParentLiteralJson + ","
            "\"clause\":" + symmetryClauseJson + "}");
          equalityParentId = symmetryStepId;
        }

        std::string ruleName = positions.size() == 1 ? "paramodulate" : "paramodulate_all";
        std::string positionField = positions.size() == 1
          ? "\"position\":" + positionJson(positions.front()) + ","
          : "\"positions\":" + positionsJson(positions) + ",";
        std::string rewriteScopeField;
        if (positions.size() == 1) {
          rewriteScopeJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], positions.front(), rewriteScopeField);
        }
        steps.push_back(
          "{\"id\":" + quote(stepBase) + ","
          "\"rule\":\"" + ruleName + "\","
          "\"parents\":["
          + quote(equalityParentId) + ","
          + quote(parentIds[targetParentIndex]) + "],"
          "\"equality\":" + equalityJson + ","
          "\"from\":" + fromJson + ","
          "\"to\":" + toJson + ","
          "\"target\":" + targetJson + ","
          "\"rewritten_target\":" + rewrittenTargetJson + ","
          + positionField
          + rewriteScopeField
          + "\"substitution\":{},"
          "\"clause\":" + conclusionJson + "}");
        result = jsonArray(steps);
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateUnitResultingResolutionStepsJson(Kernel::Unit* unit, std::string& result)
{
  auto fail = [&](const char*) {
    return false;
  };
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::UNIT_RESULTING_RESOLUTION) {
    return fail("not urr clause");
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return fail("missing proof extra");
  }
  const auto* urr = static_cast<const Inferences::UnitResultingResolutionExtra*>(extra);
  if (urr->steps.empty() || urr->mainParent == nullptr) {
    return fail("empty urr trace");
  }

  Kernel::Clause* mainParent = urr->mainParent;
  auto matchLiteralWithoutReset = [&](Kernel::Literal* base, Kernel::Literal* instance, Kernel::Substitution& substitution) {
    if (base == nullptr
      || instance == nullptr
      || !Kernel::Literal::headersMatch(base, instance, false)
      || base->arity() != instance->arity()) {
      return false;
    }
    auto matchWithOrientation = [&](bool reverseInstance) {
      Kernel::Substitution attempt;
      for (auto [var, term] : iterTraits(substitution.items())) {
        attempt.bindUnbound(var, term);
      }
      auto dereference = [&](Kernel::TermList term, Kernel::Substitution& subst) {
        Kernel::TermList current = term;
        Kernel::TermList binding;
        while (current.isVar() && subst.findBinding(current.var(), binding) && binding != current) {
          current = binding;
        }
        return current;
      };
      auto matchTerm = [&](auto&& self, Kernel::TermList baseTerm, Kernel::TermList instanceTerm, Kernel::Substitution& subst) -> bool {
        if (baseTerm.isVar()) {
          Kernel::TermList existing;
          if (!subst.findBinding(baseTerm.var(), existing)) {
            if (instanceTerm.isVar()) {
              return true;
            }
            subst.bindUnbound(baseTerm.var(), instanceTerm);
            return true;
          }
          existing = dereference(existing, subst);
          if (existing == instanceTerm) {
            return true;
          }
          if (existing.isVar()) {
            subst.rebind(baseTerm.var(), instanceTerm);
            return true;
          }
          return false;
        }
        if (!instanceTerm.isTerm() || baseTerm.term()->functor() != instanceTerm.term()->functor()) {
          return false;
        }
        if (baseTerm.term()->arity() != instanceTerm.term()->arity()) {
          return false;
        }
        for (unsigned i = 0; i < baseTerm.term()->arity(); ++i) {
          if (!self(self, *baseTerm.term()->nthArgument(i), *instanceTerm.term()->nthArgument(i), subst)) {
            return false;
          }
        }
        return true;
      };
      for (unsigned i = 0; i < base->arity(); ++i) {
        unsigned instanceIndex = reverseInstance ? base->arity() - 1 - i : i;
        if (!matchTerm(matchTerm, *base->nthArgument(i), *instance->nthArgument(instanceIndex), attempt)) {
          return false;
        }
      }
      for (auto [var, term] : iterTraits(attempt.items())) {
        substitution.rebind(var, term);
      }
      return true;
    };
    if (base->isEquality() && base->arity() == 2) {
      if (matchWithOrientation(true)) {
        return true;
      }
    }
    return matchWithOrientation(false);
  };
  std::vector<std::string> actualClause;
  for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
    std::string literalJson;
    if (!certificateLiteralJson(literal, literalJson)) {
      return fail("actual literal json failed");
    }
    actualClause.push_back(literalJson);
  }
  std::sort(actualClause.begin(), actualClause.end());
  actualClause.erase(std::unique(actualClause.begin(), actualClause.end()), actualClause.end());

  auto cloneSubstitution = [](const Kernel::Substitution& source) {
    Kernel::Substitution copy;
    Kernel::Substitution sourceCopy = source;
    for (auto [var, term] : iterTraits(sourceCopy.items())) {
      copy.bindUnbound(var, term);
    }
    return copy;
  };

  std::vector<Kernel::Literal*> selectedMainLiterals;
  Kernel::Substitution mainSubstitution;
  std::vector<Kernel::Literal*> candidateSelectedMainLiterals;

  auto residualMatchesActual = [&](const std::vector<Kernel::Literal*>& selected, const Kernel::Substitution& substitution) {
    std::vector<std::string> residualClause;
    std::vector<std::pair<std::string, std::string>> residualSymmetryCandidates;
    std::vector<std::string> selectedLiterals;
    for (Kernel::Literal* literal : selected) {
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      selectedLiterals.push_back(literalJson);
    }
    for (Kernel::Literal* literal : mainParent->iterLits()) {
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      auto selectedIt = std::find(selectedLiterals.begin(), selectedLiterals.end(), literalJson);
      if (selectedIt != selectedLiterals.end()) {
        selectedLiterals.erase(selectedIt);
        continue;
      }
      residualClause.push_back(literalJson);
      if (literal->isEquality()) {
        std::string swappedJson;
        if (!certificateSubstitutedEqualityLiteralJson(literal, substitution, true, swappedJson)) {
          return false;
        }
        if (literalJson != swappedJson) {
          residualSymmetryCandidates.push_back({literalJson, swappedJson});
        }
      }
    }
    if (!selectedLiterals.empty()) {
      return false;
    }
    std::sort(residualClause.begin(), residualClause.end());
    residualClause.erase(std::unique(residualClause.begin(), residualClause.end()), residualClause.end());
    if (residualClause == actualClause) {
      return true;
    }
    for (std::size_t guard = 0; residualClause != actualClause && guard < residualSymmetryCandidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : residualSymmetryCandidates) {
        if (std::find(actualClause.begin(), actualClause.end(), candidate.second) == actualClause.end()) {
          continue;
        }
        auto residualIt = std::find(residualClause.begin(), residualClause.end(), candidate.first);
        if (residualIt == residualClause.end()) {
          continue;
        }
        *residualIt = candidate.second;
        std::sort(residualClause.begin(), residualClause.end());
        residualClause.erase(std::unique(residualClause.begin(), residualClause.end()), residualClause.end());
        changed = true;
        break;
      }
      if (!changed) {
        break;
      }
    }
    return residualClause == actualClause;
  };
  auto residualMatchesActualModuloRename = [&](const std::vector<Kernel::Literal*>& selected, const Kernel::Substitution& substitution) {
    std::vector<Kernel::Literal*> selectedInstances;
    for (Kernel::Literal* literal : selected) {
      selectedInstances.push_back(Kernel::SubstHelper::apply(literal, substitution));
    }
    std::vector<Kernel::Literal*> residualLiterals;
    for (Kernel::Literal* literal : mainParent->iterLits()) {
      Kernel::Literal* literalInstance = Kernel::SubstHelper::apply(literal, substitution);
      bool isSelected = false;
      for (Kernel::Literal* selectedInstance : selectedInstances) {
        if (literalInstance == selectedInstance) {
          isSelected = true;
          break;
        }
        std::string literalJson;
        std::string selectedJson;
        if (certificateLiteralJson(literalInstance, literalJson)
          && certificateLiteralJson(selectedInstance, selectedJson)
          && literalJson == selectedJson) {
          isSelected = true;
          break;
        }
      }
      if (!isSelected) {
        residualLiterals.push_back(literalInstance);
      }
    }
    if (residualLiterals.size() != unit->asClause()->length()) {
      return false;
    }
    Kernel::Substitution renameSubstitution;
    std::vector<bool> usedActual(unit->asClause()->length(), false);
    for (Kernel::Literal* residualLiteral : residualLiterals) {
      bool matched = false;
      for (unsigned actualIndex = 0; actualIndex < unit->asClause()->length(); ++actualIndex) {
        if (usedActual[actualIndex]) {
          continue;
        }
        Kernel::Substitution attempt = cloneSubstitution(renameSubstitution);
        if (!matchLiteralWithoutReset(residualLiteral, (*unit->asClause())[actualIndex], attempt)) {
          continue;
        }
        renameSubstitution = cloneSubstitution(attempt);
        usedActual[actualIndex] = true;
        matched = true;
        break;
      }
      if (!matched) {
        return false;
      }
    }
    return true;
  };

  for (const auto& trace : urr->steps) {
    if (trace.selected == nullptr
      || trace.selectedSubstituted == nullptr
      || trace.unitParent == nullptr
      || trace.unitSubstituted == nullptr
      || trace.unitParent->length() != 1) {
      return fail("bad trace entry");
    }
  }

  std::function<bool(std::size_t, const Kernel::Substitution&)> selectTraceLiterals =
    [&](std::size_t traceIndex, const Kernel::Substitution& substitution) -> bool {
    if (traceIndex == urr->steps.size()) {
      if (!residualMatchesActual(candidateSelectedMainLiterals, substitution)
        && !residualMatchesActualModuloRename(candidateSelectedMainLiterals, substitution)) {
        return false;
      }
      selectedMainLiterals = candidateSelectedMainLiterals;
      mainSubstitution = cloneSubstitution(substitution);
      return true;
    }
    const auto& trace = urr->steps[traceIndex];
    for (Kernel::Literal* candidate : mainParent->iterLits()) {
      if (std::find(candidateSelectedMainLiterals.begin(), candidateSelectedMainLiterals.end(), candidate)
        != candidateSelectedMainLiterals.end()) {
        continue;
      }
      Kernel::Substitution attempt = cloneSubstitution(substitution);
      if (!matchLiteralWithoutReset(candidate, trace.selectedSubstituted, attempt)) {
        continue;
      }
      candidateSelectedMainLiterals.push_back(candidate);
      if (selectTraceLiterals(traceIndex + 1, attempt)) {
        return true;
      }
      candidateSelectedMainLiterals.pop_back();
    }
    return false;
  };
  Kernel::Substitution emptySubstitution;
  if (!selectTraceLiterals(0, emptySubstitution)) {
    return fail("selected main literal assignment not found");
  }

  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };

  std::string mainSubstitutionJson;
  std::string mainClauseJson;
  if (!certificateSubstitutionJson(mainSubstitution, mainSubstitutionJson)
    || !certificateSubstitutedClausePreservingEqualityJson(mainParent, mainSubstitution, mainClauseJson)) {
    return fail("main substitution json failed");
  }

  std::vector<std::string> initialClause;
  std::vector<std::pair<std::string, std::string>> symmetryCandidates;
  for (unsigned i = 0; i < mainParent->length(); ++i) {
    Kernel::Literal* literal = (*mainParent)[i];
    std::string literalJson;
    if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, mainSubstitution, literalJson)) {
      return fail("initial literal json failed");
    }
    initialClause.push_back(literalJson);
    if (literal->isEquality()) {
      std::string swappedJson;
      if (!certificateSubstitutedEqualityLiteralJson(literal, mainSubstitution, true, swappedJson)) {
        return fail("initial swapped literal json failed");
      }
      if (literalJson != swappedJson) {
        symmetryCandidates.push_back({literalJson, swappedJson});
      }
    }
  }
  std::sort(initialClause.begin(), initialClause.end());
  initialClause.erase(std::unique(initialClause.begin(), initialClause.end()), initialClause.end());

  std::vector<std::string> preFinalClause = initialClause;
  std::vector<std::size_t> resolutionTraceIndexes;
  std::vector<std::string> removedSelectedLiterals;
  for (std::size_t traceIndex = 0; traceIndex < urr->steps.size(); ++traceIndex) {
    std::string selectedJson;
    if (!certificateSubstitutedLiteralPreservingEqualityJson(selectedMainLiterals[traceIndex], mainSubstitution, selectedJson)) {
      return fail("selected json failed");
    }
    if (std::find(removedSelectedLiterals.begin(), removedSelectedLiterals.end(), selectedJson) != removedSelectedLiterals.end()) {
      continue;
    }
    auto selectedIt = std::find(preFinalClause.begin(), preFinalClause.end(), selectedJson);
    if (selectedIt == preFinalClause.end()) {
      return fail("selected literal missing from pre-final clause");
    }
    preFinalClause.erase(selectedIt);
    removedSelectedLiterals.push_back(selectedJson);
    resolutionTraceIndexes.push_back(traceIndex);
  }
  std::vector<Kernel::Literal*> preFinalLiterals;
  std::vector<std::string> literalsToRemove = removedSelectedLiterals;
  for (unsigned i = 0; i < mainParent->length(); ++i) {
    Kernel::Literal* literal = Kernel::SubstHelper::apply((*mainParent)[i], mainSubstitution);
    std::string literalJson;
    if (!certificateLiteralJson(literal, literalJson)) {
      return fail("pre-final literal json failed");
    }
    auto removeIt = std::find(literalsToRemove.begin(), literalsToRemove.end(), literalJson);
    if (removeIt != literalsToRemove.end()) {
      literalsToRemove.erase(removeIt);
      continue;
    }
    preFinalLiterals.push_back(literal);
  }

  auto canNormalizeBySymmetry = [&](const std::vector<std::string>& source, std::vector<std::pair<std::string, std::string>>& flips) {
    std::vector<std::string> current = source;
    flips.clear();
    for (std::size_t guard = 0; current != actualClause && guard < symmetryCandidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : symmetryCandidates) {
        if (std::find(actualClause.begin(), actualClause.end(), candidate.second) == actualClause.end()) {
          continue;
        }
        auto currentIt = std::find(current.begin(), current.end(), candidate.first);
        if (currentIt == current.end()) {
          continue;
        }
        *currentIt = candidate.second;
        std::sort(current.begin(), current.end());
        current.erase(std::unique(current.begin(), current.end()), current.end());
        flips.push_back(candidate);
        changed = true;
        break;
      }
      if (!changed) {
        break;
      }
    }
    return current == actualClause;
  };
  std::vector<std::pair<std::string, std::string>> finalSymmetryFlips;
  bool needsFinalRename = false;
  std::string finalRenameSubstitutionJson;
  std::string finalRenameClauseJson;
  if (!canNormalizeBySymmetry(preFinalClause, finalSymmetryFlips)) {
    auto matchLiteralForRename = [&](Kernel::Literal* base, Kernel::Literal* instance, Kernel::Substitution& substitution) {
      if (base == nullptr
        || instance == nullptr
        || !Kernel::Literal::headersMatch(base, instance, false)
        || base->arity() != instance->arity()) {
        return false;
      }
      auto matchWithOrientation = [&](bool reverseInstance) {
        Kernel::Substitution attempt;
        for (auto [var, term] : iterTraits(substitution.items())) {
          attempt.bindUnbound(var, term);
        }
        auto dereference = [&](Kernel::TermList term, Kernel::Substitution& subst) {
          Kernel::TermList current = term;
          Kernel::TermList binding;
          while (current.isVar() && subst.findBinding(current.var(), binding) && binding != current) {
            current = binding;
          }
          return current;
        };
        auto matchTerm = [&](auto&& self, Kernel::TermList baseTerm, Kernel::TermList instanceTerm, Kernel::Substitution& subst) -> bool {
          if (baseTerm.isVar()) {
            Kernel::TermList existing;
            if (!subst.findBinding(baseTerm.var(), existing)) {
              subst.bindUnbound(baseTerm.var(), instanceTerm);
              return true;
            }
            existing = dereference(existing, subst);
            if (existing == instanceTerm) {
              return true;
            }
            if (existing.isVar()) {
              subst.rebind(baseTerm.var(), instanceTerm);
              return true;
            }
            return false;
          }
          if (!instanceTerm.isTerm() || baseTerm.term()->functor() != instanceTerm.term()->functor()) {
            return false;
          }
          if (baseTerm.term()->arity() != instanceTerm.term()->arity()) {
            return false;
          }
          for (unsigned i = 0; i < baseTerm.term()->arity(); ++i) {
            if (!self(self, *baseTerm.term()->nthArgument(i), *instanceTerm.term()->nthArgument(i), subst)) {
              return false;
            }
          }
          return true;
        };
        for (unsigned i = 0; i < base->arity(); ++i) {
          unsigned instanceIndex = reverseInstance ? base->arity() - 1 - i : i;
          if (!matchTerm(matchTerm, *base->nthArgument(i), *instance->nthArgument(instanceIndex), attempt)) {
            return false;
          }
        }
        for (auto [var, term] : iterTraits(attempt.items())) {
          substitution.rebind(var, term);
        }
        return true;
      };
      if (base->isEquality() && base->arity() == 2) {
        if (matchWithOrientation(true)) {
          return true;
        }
      }
      return matchWithOrientation(false);
    };

    Kernel::Substitution finalRenameSubstitution;
    std::vector<bool> usedActual(unit->asClause()->length(), false);
    for (Kernel::Literal* expectedLiteral : preFinalLiterals) {
      bool matched = false;
      for (unsigned actualIndex = 0; actualIndex < unit->asClause()->length(); ++actualIndex) {
        if (usedActual[actualIndex]) {
          continue;
        }
        if (matchLiteralForRename(expectedLiteral, (*unit->asClause())[actualIndex], finalRenameSubstitution)) {
          usedActual[actualIndex] = true;
          matched = true;
          break;
        }
      }
      if (!matched) {
        return false;
      }
    }
    if (!certificateSubstitutionJson(finalRenameSubstitution, finalRenameSubstitutionJson)
      || finalRenameSubstitutionJson == "{}"
      || !certificateClauseJson(unit->asClause(), finalRenameClauseJson)) {
      return false;
    }
    needsFinalRename = true;
  }

  std::vector<std::string> steps;
  std::string stepBase = "u" + std::to_string(unit->number());
  std::string mainParentId = "u" + std::to_string(mainParent->number());
  if (mainSubstitutionJson != "{}") {
    std::string substituteId = stepBase + "_subst0";
    steps.push_back(
      "{\"id\":" + quote(substituteId) + ","
      "\"rule\":\"substitute\","
      "\"parents\":[" + quote(mainParentId) + "],"
      "\"substitution\":" + mainSubstitutionJson + ","
      "\"clause\":" + mainClauseJson + "}");
	    mainParentId = substituteId;
	  }

  std::string currentStepId = mainParentId;
  std::vector<std::string> currentClause = initialClause;
  for (std::size_t replayIndex = 0; replayIndex < resolutionTraceIndexes.size(); ++replayIndex) {
    std::size_t traceIndex = resolutionTraceIndexes[replayIndex];
    const auto& trace = urr->steps[traceIndex];
    Kernel::Clause* unitParent = trace.unitParent;
    Kernel::Literal* unitLiteral = (*unitParent)[0];
    Kernel::Literal* selectedComplementForUnit =
      Kernel::SubstHelper::apply(Kernel::Literal::complementaryLiteral(selectedMainLiterals[traceIndex]), mainSubstitution);
    Kernel::Substitution unitSubstitution;
    if (!Kernel::MatchingUtils::match(unitLiteral, selectedComplementForUnit, false, unitSubstitution)) {
      return false;
    }
    std::string unitSubstitutionJson;
    std::string unitClauseJson;
    if (!certificateSubstitutionJson(unitSubstitution, unitSubstitutionJson)
      || !certificateSubstitutedClausePreservingEqualityJson(unitParent, unitSubstitution, unitClauseJson)) {
      return false;
    }

    std::string unitParentId = "u" + std::to_string(unitParent->number());
    if (unitSubstitutionJson != "{}") {
      std::string substituteId = stepBase + "_unit_subst" + std::to_string(traceIndex);
      steps.push_back(
        "{\"id\":" + quote(substituteId) + ","
        "\"rule\":\"substitute\","
        "\"parents\":[" + quote(unitParentId) + "],"
        "\"substitution\":" + unitSubstitutionJson + ","
        "\"clause\":" + unitClauseJson + "}");
      unitParentId = substituteId;
    }

    Kernel::Literal* selectedSubstituted = Kernel::SubstHelper::apply(selectedMainLiterals[traceIndex], mainSubstitution);
    Kernel::Literal* unitSubstituted = Kernel::SubstHelper::apply(unitLiteral, unitSubstitution);
    std::string selectedJson;
    std::string selectedComplementJson;
    std::string unitJson;
    if (!certificateSubstitutedLiteralPreservingEqualityJson(selectedMainLiterals[traceIndex], mainSubstitution, selectedJson)
      || !certificateSubstitutedLiteralPreservingEqualityJson(Kernel::Literal::complementaryLiteral(selectedMainLiterals[traceIndex]), mainSubstitution, selectedComplementJson)
      || !certificateSubstitutedLiteralPreservingEqualityJson(unitLiteral, unitSubstitution, unitJson)) {
      return false;
    }

    if (unitJson != selectedComplementJson) {
      if (!unitSubstituted->isEquality()) {
        return false;
      }
      std::string swappedUnitJson;
      if (!certificateSubstitutedEqualityLiteralJson(unitLiteral, unitSubstitution, true, swappedUnitJson)
        || swappedUnitJson != selectedComplementJson) {
        return false;
      }
      std::string symmetryStepId = stepBase + "_unit_symmetry" + std::to_string(traceIndex);
      steps.push_back(
        "{\"id\":" + quote(symmetryStepId) + ","
        "\"rule\":\"equality_symmetry\","
        "\"parents\":[" + quote(unitParentId) + "],"
        "\"literal\":" + unitJson + ","
        "\"clause\":[" + swappedUnitJson + "]}");
      unitParentId = symmetryStepId;
      unitJson = swappedUnitJson;
    }

    std::string pivotJson;
    std::string leftParentId;
    std::string rightParentId;
    if (selectedSubstituted->isPositive()) {
      pivotJson = selectedJson;
      leftParentId = currentStepId;
      rightParentId = unitParentId;
    } else {
      pivotJson = unitJson;
      leftParentId = unitParentId;
      rightParentId = currentStepId;
    }

    auto selectedIt = std::find(currentClause.begin(), currentClause.end(), selectedJson);
    if (selectedIt == currentClause.end()) {
      return false;
    }
    currentClause.erase(selectedIt);
    std::string resolveStepId = replayIndex + 1 == resolutionTraceIndexes.size() && finalSymmetryFlips.empty() && !needsFinalRename
      ? stepBase
      : stepBase + "_resolve" + std::to_string(replayIndex);
    steps.push_back(
      "{\"id\":" + quote(resolveStepId) + ","
      "\"rule\":\"resolve\","
      "\"parents\":[" + quote(leftParentId) + "," + quote(rightParentId) + "],"
      "\"pivot\":" + pivotJson + ","
      "\"clause\":" + jsonArray(currentClause) + "}");
    currentStepId = resolveStepId;
  }

  for (std::size_t index = 0; index < finalSymmetryFlips.size(); ++index) {
    const auto& flip = finalSymmetryFlips[index];
    auto literalIt = std::find(currentClause.begin(), currentClause.end(), flip.first);
    if (literalIt == currentClause.end()) {
      return false;
    }
    *literalIt = flip.second;
    std::sort(currentClause.begin(), currentClause.end());
    currentClause.erase(std::unique(currentClause.begin(), currentClause.end()), currentClause.end());
    std::string normalizeStepId = index + 1 == finalSymmetryFlips.size()
      ? stepBase
      : stepBase + "_normalize" + std::to_string(index);
    steps.push_back(
      "{\"id\":" + quote(normalizeStepId) + ","
      "\"rule\":\"equality_symmetry\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"literal\":" + flip.first + ","
      "\"clause\":" + jsonArray(currentClause) + "}");
    currentStepId = normalizeStepId;
  }

  if (needsFinalRename) {
    steps.push_back(
      "{\"id\":" + quote(stepBase) + ","
      "\"rule\":\"substitute\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"substitution\":" + finalRenameSubstitutionJson + ","
      "\"clause\":" + finalRenameClauseJson + "}");
  }

  result = jsonArray(steps);
  return true;
}

bool MegalodonChecker::certificateSubstitutedResolutionStepsJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  if (!unit->isClause()
    || (
      unit->inference().rule() != Kernel::InferenceRule::RESOLUTION
      && unit->inference().rule() != Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
      && unit->inference().rule() != Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION
    )
    || replayInfo == nullptr
    || replayInfo->premises.size() != 2
    || replayInfo->substitutionForBanksSub.size() != 2) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return false;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2) {
    return false;
  }

  auto containsLiteral = [](Kernel::Clause* clause, Kernel::Literal* literal) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        return true;
      }
    }
    return false;
  };
  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };
  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string literalJson;
      if (!certificateLiteralJson(literal, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  auto orientation = [&](Kernel::Literal* leftPivot, std::size_t leftIndex, Kernel::Literal* rightPivot, std::size_t rightIndex, std::string& rendered) {
    if (!containsLiteral(parents[leftIndex], leftPivot) || !containsLiteral(parents[rightIndex], rightPivot)) {
      return false;
    }
    Kernel::Literal* leftSubstituted = Kernel::SubstHelper::apply(leftPivot, replayInfo->substitutionForBanksSub[leftIndex]);
    Kernel::Literal* rightSubstituted = Kernel::SubstHelper::apply(rightPivot, replayInfo->substitutionForBanksSub[rightIndex]);
    if (leftSubstituted->isPositive() == rightSubstituted->isPositive()) {
      return false;
    }
    std::string leftAtom;
    std::string rightAtom;
    if (!certificateAtomJson(leftSubstituted, leftAtom)
      || !certificateAtomJson(rightSubstituted, rightAtom)
      || leftAtom != rightAtom) {
      return false;
    }

    std::vector<std::string> expected;
    for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
      Kernel::Literal* excluded = parentIndex == leftIndex ? leftPivot : rightPivot;
      bool skipped = false;
      for (unsigned i = 0; i < parents[parentIndex]->length(); ++i) {
        Kernel::Literal* literal = (*parents[parentIndex])[i];
        if (!skipped && literal == excluded) {
          skipped = true;
          continue;
        }
        std::string literalJson;
        Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, replayInfo->substitutionForBanksSub[parentIndex]);
        if (!certificateLiteralJson(substituted, literalJson)) {
          return false;
        }
        expected.push_back(literalJson);
      }
      if (!skipped) {
        return false;
      }
    }
    std::sort(expected.begin(), expected.end());
    expected.erase(std::unique(expected.begin(), expected.end()), expected.end());
    std::vector<std::string> actual;
    if (!normalizedClause(unit->asClause(), actual) || expected != actual) {
      return false;
    }

    std::vector<std::string> steps;
    std::string stepBase = "u" + std::to_string(unit->number());
    std::string leftParentId;
    std::string rightParentId;
    for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
      std::string substitutionJson;
      std::string clauseJson;
      if (!certificateSubstitutionJson(replayInfo->substitutionForBanksSub[parentIndex], substitutionJson)
        || !certificateSubstitutedClausePreservingEqualityJson(parents[parentIndex], replayInfo->substitutionForBanksSub[parentIndex], clauseJson)) {
        return false;
      }
      std::string parentId = "u" + std::to_string(parents[parentIndex]->number());
      if (substitutionJson != "{}") {
        std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
        steps.push_back(
          "{\"id\":" + quote(substituteId) + ","
          "\"rule\":\"substitute\","
          "\"parents\":[" + quote(parentId) + "],"
          "\"substitution\":" + substitutionJson + ","
          "\"clause\":" + clauseJson + "}");
        parentId = substituteId;
      }
      if (parentIndex == leftIndex) {
        leftParentId = parentId;
      } else {
        rightParentId = parentId;
      }
    }

    std::string pivotJson;
    Kernel::Literal* leftSubstitutedPivot = Kernel::SubstHelper::apply(leftPivot, replayInfo->substitutionForBanksSub[leftIndex]);
    if (!leftSubstitutedPivot->isPositive()) {
      return false;
    }
    if (!certificateLiteralJson(leftSubstitutedPivot, pivotJson)) {
      return false;
    }
    std::string conclusionJson;
    if (!certificateClauseJson(unit->asClause(), conclusionJson)) {
      return false;
    }
    steps.push_back(
      "{\"id\":" + quote(stepBase) + ","
      "\"rule\":\"resolve\","
      "\"parents\":[" + quote(leftParentId) + "," + quote(rightParentId) + "],"
      "\"pivot\":" + pivotJson + ","
      "\"clause\":" + conclusionJson + "}");
    rendered = jsonArray(steps);
    return true;
  };

  if (unit->inference().rule() == Kernel::InferenceRule::RESOLUTION) {
    const auto* selected = static_cast<const Inferences::TwoLiteralInferenceExtra*>(extra);
    if (orientation(selected->selectedLiteral.selectedLiteral, 0, selected->otherLiteral, 1, result)) {
      return true;
    }
    if (orientation(selected->otherLiteral, 1, selected->selectedLiteral.selectedLiteral, 0, result)) {
      return true;
    }
    return false;
  }

  const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
  Kernel::Literal* selectedLiteral = selected->selectedLiteral;
  if (selectedLiteral == nullptr) {
    return false;
  }
  for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
    if (!containsLiteral(parents[parentIndex], selectedLiteral)) {
      continue;
    }
    std::size_t otherParentIndex = parentIndex == 0 ? 1 : 0;
    for (Kernel::Literal* candidate : parents[otherParentIndex]->iterLits()) {
      if (orientation(selectedLiteral, parentIndex, candidate, otherParentIndex, result)) {
        return true;
      }
      if (orientation(candidate, otherParentIndex, selectedLiteral, parentIndex, result)) {
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateSatSubsumptionResolutionStepsJson(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION
    )) {
    return false;
  }
  Kernel::Literal* proofSelectedLiteral = nullptr;
  const auto* extra = env.proofExtra.find(unit);
  if (extra != nullptr) {
    const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
    proofSelectedLiteral = selected->selectedLiteral;
  }

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2) {
    return false;
  }

  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };
  auto normalizedActualClause = [&](std::vector<std::string>& actual) {
    for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
      std::string rendered;
      if (!certificateLiteralJson(literal, rendered)) {
        return false;
      }
      actual.push_back(rendered);
    }
    std::sort(actual.begin(), actual.end());
    actual.erase(std::unique(actual.begin(), actual.end()), actual.end());
    return true;
  };
  auto normalize = [](std::vector<std::string>& literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
  };
  auto certificateSubstitutedEqualityAtomJson = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, bool swapEquality, std::string& atom) {
    if (!literal->isEquality()) {
      return false;
    }
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
    std::string equalitySort;
    std::string lhs;
    std::string rhs;
    unsigned lhsIndex = swapEquality ? 1 : 0;
    unsigned rhsIndex = swapEquality ? 0 : 1;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)
      || !certificateTermJson(Kernel::SubstHelper::apply(*literal->nthArgument(lhsIndex), substitution), lhs)
      || !certificateTermJson(Kernel::SubstHelper::apply(*literal->nthArgument(rhsIndex), substitution), rhs)) {
      return false;
    }
    if (equalitySort == "set") {
      atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
    } else {
      atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    return true;
  };

  std::vector<std::string> actual;
  if (!normalizedActualClause(actual)) {
    return false;
  }

  for (std::size_t mainParentIndex = 0; mainParentIndex < 2; ++mainParentIndex) {
    Kernel::Clause* mainParent = parents[mainParentIndex];
    std::size_t sideParentIndex = mainParentIndex == 0 ? 1 : 0;
    Kernel::Clause* sideParent = parents[sideParentIndex];
    for (unsigned i = 0; i < mainParent->length(); ++i) {
      Kernel::Literal* selectedLiteral = (*mainParent)[i];
      if (proofSelectedLiteral != nullptr && selectedLiteral != proofSelectedLiteral) {
        continue;
      }
      unsigned selectedLiteralIndex = i;

      SATSubsumption::SATSubsumptionAndResolution satSR;
      if (!satSR.checkSubsumptionResolutionWithLiteral(sideParent, mainParent, selectedLiteralIndex)) {
        continue;
      }
      Kernel::Substitution sideSubstitution = satSR.getBindingsForSubsumptionResolutionWithLiteral();
      std::string sideSubstitutionJson;
      if (!certificateSubstitutionJson(sideSubstitution, sideSubstitutionJson)) {
        continue;
      }

      for (Kernel::Literal* sideLiteral : sideParent->iterLits()) {
        Kernel::Literal* substitutedSideLiteral = Kernel::SubstHelper::apply(sideLiteral, sideSubstitution);
        if (selectedLiteral->isPositive() == substitutedSideLiteral->isPositive()) {
          continue;
        }
        std::string selectedAtom;
        std::string sideAtom;
        std::string sideLiteralJson;
        std::string swappedSideLiteralJson;
        if (!certificateAtomJson(selectedLiteral, selectedAtom)
          || !certificateSubstitutedLiteralPreservingEqualityJson(sideLiteral, sideSubstitution, sideLiteralJson)) {
          continue;
        }
        if (sideLiteral->isEquality()) {
          if (!certificateSubstitutedEqualityAtomJson(sideLiteral, sideSubstitution, false, sideAtom)) {
            continue;
          }
        } else if (!certificateAtomJson(substitutedSideLiteral, sideAtom)) {
          continue;
        }
        bool needsSideSymmetry = selectedAtom != sideAtom;
        if (needsSideSymmetry) {
          std::string swappedAtom;
          if (!sideLiteral->isEquality()
            || !certificateSubstitutedEqualityLiteralJson(sideLiteral, sideSubstitution, true, swappedSideLiteralJson)
            || !certificateSubstitutedEqualityAtomJson(sideLiteral, sideSubstitution, true, swappedAtom)
            || selectedAtom != swappedAtom) {
            continue;
          }
        } else {
          swappedSideLiteralJson = sideLiteralJson;
        }

        std::vector<std::string> expected;
        for (Kernel::Literal* literal : mainParent->iterLits()) {
          if (literal == selectedLiteral) {
            continue;
          }
          std::string rendered;
          if (!certificateLiteralJson(literal, rendered)) {
            expected.clear();
            break;
          }
          expected.push_back(rendered);
        }
        if (expected.empty() && mainParent->length() > 1) {
          continue;
        }
        normalize(expected);
        if (expected != actual) {
          continue;
        }

        std::string selectedLiteralJson;
        if (!certificateLiteralJson(selectedLiteral, selectedLiteralJson)) {
          continue;
        }
        std::string stepBase = "u" + std::to_string(unit->number());

        std::vector<std::string> sideCurrent;
        struct SideSymmetryOperation {
          std::size_t literalIndex;
          std::string literal;
          std::string swapped;
        };
        std::vector<SideSymmetryOperation> sideSymmetries;
        std::vector<std::string> resolvedExpected;
        bool skippedSidePivot = false;
        bool canExpandAsPrimitiveSteps = true;
        for (Kernel::Literal* literal : mainParent->iterLits()) {
          if (literal == selectedLiteral) {
            continue;
          }
          std::string rendered;
          if (!certificateLiteralJson(literal, rendered)) {
            canExpandAsPrimitiveSteps = false;
            break;
          }
          resolvedExpected.push_back(rendered);
        }
        if (canExpandAsPrimitiveSteps) {
          for (Kernel::Literal* literal : sideParent->iterLits()) {
            std::string rendered;
            if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, sideSubstitution, rendered)) {
              canExpandAsPrimitiveSteps = false;
              break;
            }
            std::string current = rendered;
            if (literal == sideLiteral && needsSideSymmetry) {
              current = swappedSideLiteralJson;
              sideSymmetries.push_back({sideCurrent.size(), rendered, swappedSideLiteralJson});
            } else if (literal != sideLiteral
              && !std::binary_search(actual.begin(), actual.end(), rendered)
              && literal->isEquality()) {
              std::string swapped;
              if (certificateSubstitutedEqualityLiteralJson(literal, sideSubstitution, true, swapped)
                && std::binary_search(actual.begin(), actual.end(), swapped)) {
                current = swapped;
                sideSymmetries.push_back({sideCurrent.size(), rendered, swapped});
              }
            }
            sideCurrent.push_back(rendered);
            if (!skippedSidePivot && literal == sideLiteral) {
              skippedSidePivot = true;
              continue;
            }
            resolvedExpected.push_back(current);
          }
        }
        if (canExpandAsPrimitiveSteps && skippedSidePivot) {
          normalize(resolvedExpected);
          if (resolvedExpected == actual) {
            std::vector<std::string> steps;
            std::string currentSideParentId = "u" + std::to_string(sideParent->number());
            if (sideSubstitutionJson != "{}") {
              std::string substitutedClauseJson;
              if (!certificateSubstitutedClausePreservingEqualityJson(sideParent, sideSubstitution, substitutedClauseJson)) {
                continue;
              }
              std::string substituteId = stepBase + "_side_subst";
              steps.push_back(
                "{\"id\":" + quote(substituteId) + ","
                "\"rule\":\"substitute\","
                "\"parents\":[" + quote(currentSideParentId) + "],"
                "\"substitution\":" + sideSubstitutionJson + ","
                "\"clause\":" + substitutedClauseJson + "}");
              currentSideParentId = substituteId;
            }
            std::vector<std::string> sideSymmetryState = sideCurrent;
            for (std::size_t symmetryIndex = 0; symmetryIndex < sideSymmetries.size(); ++symmetryIndex) {
              const SideSymmetryOperation& operation = sideSymmetries[symmetryIndex];
              sideSymmetryState[operation.literalIndex] = operation.swapped;
              std::string sideSymmetryClauseJson = jsonArray(sideSymmetryState);
              std::string symmetryId = stepBase + "_side_symmetry" + std::to_string(symmetryIndex);
              steps.push_back(
                "{\"id\":" + quote(symmetryId) + ","
                "\"rule\":\"equality_symmetry\","
                "\"parents\":[" + quote(currentSideParentId) + "],"
                "\"literal\":" + operation.literal + ","
                "\"clause\":" + sideSymmetryClauseJson + "}");
              currentSideParentId = symmetryId;
            }
            std::string conclusionJson;
            if (!certificateClauseJson(unit->asClause(), conclusionJson)) {
              continue;
            }
            steps.push_back(
              "{\"id\":" + quote(stepBase) + ","
              "\"rule\":\"resolve\","
              "\"parents\":[" + quote("u" + std::to_string(mainParent->number())) + "," + quote(currentSideParentId) + "],"
              "\"pivot\":" + selectedLiteralJson + ","
              "\"clause\":" + conclusionJson + "}");
            result = jsonArray(steps);
            return true;
          }
        }

      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateSuperpositionStepsJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::SUPERPOSITION
    || replayInfo == nullptr
    || replayInfo->premises.size() != 2
    || replayInfo->substitutionForBanksSub.size() != 2) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return false;
  }
  const auto* rewrite = static_cast<const Inferences::TwoLiteralRewriteInferenceExtra*>(extra);

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2 || parents[0] != replayInfo->premises[0] || parents[1] != replayInfo->premises[1]) {
    return false;
  }

  constexpr std::size_t targetParentIndex = 0;
  constexpr std::size_t equalityParentIndex = 1;
  Kernel::Clause* targetParent = parents[targetParentIndex];
  Kernel::Clause* equalityParent = parents[equalityParentIndex];
  Kernel::Literal* targetLiteral = rewrite->selected.selectedLiteral.selectedLiteral;
  Kernel::Literal* equalityLiteral = rewrite->selected.otherLiteral;
  auto containsLiteral = [](Kernel::Clause* clause, Kernel::Literal* literal) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        return true;
      }
    }
    return false;
  };
  if (targetLiteral == nullptr
    || equalityLiteral == nullptr
    || !equalityLiteral->isEquality()
    || !equalityLiteral->isPositive()
    || !containsLiteral(targetParent, targetLiteral)
    || !containsLiteral(equalityParent, equalityLiteral)) {
    return false;
  }

  auto jsonArray = [](const std::vector<std::string>& items) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i];
    }
    out << ']';
    return out.str();
  };
  auto certificateSubstitutionJson = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      items.push_back({var, quote(variableName(var)) + ":" + termJson});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < items.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << items[i].second;
    }
    out << '}';
    rendered = out.str();
    return true;
  };
  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string literalJson;
      if (!certificateLiteralJson(literal, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  std::vector<std::pair<std::string, std::string>> symmetryCandidates;
  auto appendSubstitutedClauseExcept = [&](std::vector<std::string>& literals, Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::Literal* excluded) {
    bool skipped = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      Kernel::Literal* literal = (*clause)[i];
      if (!skipped && literal == excluded) {
        skipped = true;
        continue;
      }
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
      if (literal->isEquality()) {
        std::string swappedJson;
        if (!certificateSubstitutedEqualityLiteralJson(literal, substitution, true, swappedJson)) {
          return false;
        }
        if (literalJson != swappedJson) {
          symmetryCandidates.push_back({literalJson, swappedJson});
        }
      }
    }
    return skipped;
  };
  auto collectTermPositions = [&](auto&& self, Kernel::TermList term, Kernel::TermList needle, std::vector<unsigned>& current, std::vector<std::vector<unsigned>>& positions) -> void {
    if (term == needle) {
      positions.push_back(current);
      return;
    }
    if (term.isApplication()) {
      current.push_back(0);
      self(self, term.lhs(), needle, current, positions);
      current.back() = 1;
      self(self, term.rhs(), needle, current, positions);
      current.pop_back();
      return;
    }
    if (!term.isTerm() || term.term()->isSpecial()) {
      return;
    }
    Kernel::Term* t = term.term();
    for (unsigned i = 0; i < t->numTermArguments(); ++i) {
      current.push_back(i);
      self(self, t->termArg(i), needle, current, positions);
      current.pop_back();
    }
  };
  auto collectPrintedSubstitutedLiteralAtomPositions = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, Kernel::TermList needle, std::vector<std::vector<unsigned>>& positions) {
    Kernel::Literal* indexed = literal->isEquality()
      ? literal
      : (literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal));
    unsigned arity = indexed->isEquality() ? 2 : indexed->arity();
    for (unsigned i = 0; i < arity; ++i) {
      Kernel::TermList argument = Kernel::SubstHelper::apply(*indexed->nthArgument(i), substitution);
      std::vector<unsigned> position;
      position.push_back(i);
      collectTermPositions(collectTermPositions, argument, needle, position, positions);
    }
    return !positions.empty();
  };
  auto positionJson = [](const std::vector<unsigned>& position) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < position.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << position[i];
    }
    out << ']';
    return out.str();
  };
  auto rewriteScopeJson = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, const std::vector<unsigned>& position, std::string& rendered) {
    if (position.empty()) {
      return false;
    }
    Kernel::Literal* indexed = literal->isEquality()
      ? literal
      : (literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal));
    unsigned arity = indexed->isEquality() ? 2 : indexed->arity();
    if (position[0] >= arity) {
      return false;
    }

    Kernel::TermList current = Kernel::SubstHelper::apply(*indexed->nthArgument(position[0]), substitution);
    unsigned lambdaDepth = 0;
    for (std::size_t depth = 1; depth < position.size(); ++depth) {
      unsigned index = position[depth];
      if (current.isLambdaTerm() && index == 0) {
        ++lambdaDepth;
      }
      if (current.isApplication()) {
        if (index > 1) {
          return false;
        }
        current = index == 0 ? current.lhs() : current.rhs();
        continue;
      }
      if (!current.isTerm() || current.term()->isSpecial()) {
        return false;
      }
      if (index >= current.term()->numTermArguments()) {
        return false;
      }
      current = current.term()->termArg(index);
    }

    auto dbIndex = current.deBruijnIndex();
    if (dbIndex.isNone() || dbIndex.unwrap() >= lambdaDepth) {
      return false;
    }
    rendered = "\"rewrite_scope\":{\"kind\":\"bound_lambda_var\","
      "\"lambda_depth\":" + std::to_string(lambdaDepth) + ","
      "\"db_index\":" + std::to_string(dbIndex.unwrap()) + "},";
    return true;
  };
  auto positionsJson = [&](const std::vector<std::vector<unsigned>>& positions) {
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < positions.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << positionJson(positions[i]);
    }
    out << ']';
    return out.str();
  };
  auto positiveEqualityLiteralJson = [&](Kernel::TermList lhsTerm, Kernel::TermList rhsTerm, std::string& rendered) {
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(equalityLiteral);
    std::string equalitySort;
    std::string lhs;
    std::string rhs;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)
      || !certificateTermJson(lhsTerm, lhs)
      || !certificateTermJson(rhsTerm, rhs)) {
      return false;
    }
    std::string atom;
    if (equalitySort == "set") {
      atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
    } else {
      atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    rendered = "{\"polarity\":true,\"atom\":" + atom + "}";
    return true;
  };
  auto replaceTermAtPrintedPosition = [&](auto&& self, Kernel::TermList term, const std::vector<unsigned>& rewritePosition, std::size_t depth, Kernel::TermList replacement, Kernel::TermList& result) -> bool {
    if (depth == rewritePosition.size()) {
      result = replacement;
      return true;
    }
    if (!term.isTerm()) {
      return false;
    }
    Kernel::Term* source = term.term();
    std::vector<Kernel::TermList> args;
    args.reserve(source->arity());
    for (unsigned i = 0; i < source->arity(); ++i) {
      args.push_back(*source->nthArgument(i));
    }
    unsigned printedIndex = rewritePosition[depth];
    unsigned argumentIndex;
    if (term.isApplication()) {
      if (printedIndex > 1) {
        return false;
      }
      argumentIndex = printedIndex == 0 ? 2 : 3;
    } else {
      unsigned typeArgs = source->numTypeArguments();
      if (printedIndex >= source->numTermArguments()) {
        return false;
      }
      argumentIndex = typeArgs + printedIndex;
    }
    Kernel::TermList rewrittenChild;
    if (!self(self, args[argumentIndex], rewritePosition, depth + 1, replacement, rewrittenChild)) {
      return false;
    }
    args[argumentIndex] = rewrittenChild;
    result = Kernel::TermList(Kernel::Term::create(source, args.data()));
    return true;
  };
  auto equalityLiteralFromTermsJson = [&](Kernel::Literal* literal, Kernel::TermList lhsTerm, Kernel::TermList rhsTerm, std::string& rendered) {
    if (!literal->isEquality()) {
      return false;
    }
    Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
    std::string equalitySort;
    std::string lhs;
    std::string rhs;
    if (!sortToMegalodon(equalityArgumentSort, equalitySort)
      || !certificateTermJson(lhsTerm, lhs)
      || !certificateTermJson(rhsTerm, rhs)) {
      return false;
    }
    std::string atom;
    if (equalitySort == "set") {
      atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
    } else {
      atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    rendered = "{\"polarity\":";
    rendered += literal->isPositive() ? "true" : "false";
    rendered += ",\"atom\":" + atom + "}";
    return true;
  };
  auto replacedSubstitutedLiteralPreservingEqualityJson = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, Kernel::TermList what, Kernel::TermList by, bool swapEquality, std::string& rendered) {
    if (literal->isEquality()) {
      Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
      std::string equalitySort;
      std::string lhs;
      std::string rhs;
      unsigned lhsIndex = swapEquality ? 1 : 0;
      unsigned rhsIndex = swapEquality ? 0 : 1;
      Kernel::TermList lhsTerm = Kernel::EqHelper::replace(Kernel::SubstHelper::apply(*literal->nthArgument(lhsIndex), substitution), what, by);
      Kernel::TermList rhsTerm = Kernel::EqHelper::replace(Kernel::SubstHelper::apply(*literal->nthArgument(rhsIndex), substitution), what, by);
      if (!sortToMegalodon(equalityArgumentSort, equalitySort)
        || !certificateTermJson(lhsTerm, lhs)
        || !certificateTermJson(rhsTerm, rhs)) {
        return false;
      }
      std::string atom;
      if (equalitySort == "set") {
        atom = "{\"eq\":[" + lhs + "," + rhs + "]}";
      } else {
        atom = "{\"eq\":[" + lhs + "," + rhs + "],\"sort\":" + quote(equalitySort) + "}";
      }
      rendered = "{\"polarity\":";
      rendered += literal->isPositive() ? "true" : "false";
      rendered += ",\"atom\":" + atom + "}";
      return true;
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
    Kernel::Literal* replaced = Kernel::EqHelper::replace(substituted, what, by);
    return certificateLiteralJson(replaced, rendered);
  };
  auto substitutedClauseReplacingOneLiteralJson = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::Literal* excluded, const std::string& replacement, std::string& rendered) {
    std::ostringstream out;
    out << '[';
    bool skipped = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      if (i != 0) {
        out << ',';
      }
      Kernel::Literal* literal = (*clause)[i];
      if (!skipped && literal == excluded) {
        skipped = true;
        out << replacement;
        continue;
      }
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      out << literalJson;
    }
    if (!skipped) {
      return false;
    }
    out << ']';
    rendered = out.str();
    return true;
  };
  struct TargetRewrite {
    std::string literalJson;
    std::string rewrittenJson;
    std::vector<std::vector<unsigned>> positions;
  };
  auto appendClauseWithAllReplacements = [&](std::vector<std::string>& literals, Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::TermList what, Kernel::TermList by, std::vector<TargetRewrite>& targetRewrites) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::vector<std::vector<unsigned>> positions;
      collectPrintedSubstitutedLiteralAtomPositions(literal, substitution, what, positions);
      if (positions.empty()) {
        std::string literalJson;
        if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
          return false;
        }
        literals.push_back(literalJson);
        continue;
      }

      std::string literalJson;
      std::string rewrittenJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)
        || !replacedSubstitutedLiteralPreservingEqualityJson(literal, substitution, what, by, false, rewrittenJson)) {
        return false;
      }
      literals.push_back(rewrittenJson);
      targetRewrites.push_back({literalJson, rewrittenJson, positions});

      if (literal->isEquality()) {
        std::string swappedRewrittenJson;
        if (!replacedSubstitutedLiteralPreservingEqualityJson(literal, substitution, what, by, true, swappedRewrittenJson)) {
          return false;
        }
        if (rewrittenJson != swappedRewrittenJson) {
          symmetryCandidates.push_back({rewrittenJson, swappedRewrittenJson});
        }
      }
    }
    return true;
  };
  auto substitutedClauseLiterals = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  auto substitutedClauseExceptLiterals = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::Literal* excluded, std::vector<std::string>& literals) {
    bool skipped = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      Kernel::Literal* literal = (*clause)[i];
      if (!skipped && literal == excluded) {
        skipped = true;
        continue;
      }
      std::string literalJson;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    if (!skipped) {
      return false;
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };

  Kernel::Literal* substitutedEquality = Kernel::SubstHelper::apply(equalityLiteral, replayInfo->substitutionForBanksSub[equalityParentIndex]);
  Kernel::TermList equalityLeft = *substitutedEquality->nthArgument(0);
  Kernel::TermList equalityRight = *substitutedEquality->nthArgument(1);
  Kernel::TermList preferredFrom = Kernel::SubstHelper::apply(rewrite->rewrite.lhs, replayInfo->substitutionForBanksSub[equalityParentIndex]);
  Kernel::TermList from;
  Kernel::TermList to;
  std::vector<std::vector<unsigned>> leftRedexPositions;
  std::vector<std::vector<unsigned>> rightRedexPositions;
  collectPrintedSubstitutedLiteralAtomPositions(
    targetLiteral,
    replayInfo->substitutionForBanksSub[targetParentIndex],
    equalityLeft,
    leftRedexPositions);
  collectPrintedSubstitutedLiteralAtomPositions(
    targetLiteral,
    replayInfo->substitutionForBanksSub[targetParentIndex],
    equalityRight,
    rightRedexPositions);
  std::vector<std::vector<unsigned>> redexPositions;
  if (preferredFrom == equalityLeft && !leftRedexPositions.empty()) {
    from = equalityLeft;
    to = equalityRight;
    redexPositions = leftRedexPositions;
  } else if (preferredFrom == equalityRight && !rightRedexPositions.empty()) {
    from = equalityRight;
    to = equalityLeft;
    redexPositions = rightRedexPositions;
  } else if (!leftRedexPositions.empty()) {
    from = equalityLeft;
    to = equalityRight;
    redexPositions = leftRedexPositions;
  } else if (!rightRedexPositions.empty()) {
    from = equalityRight;
    to = equalityLeft;
    redexPositions = rightRedexPositions;
  } else {
    return false;
  }
  Kernel::TermList targetRedex = from;
  std::vector<unsigned> position = redexPositions.front();
  bool simultaneousParamodulation = redexPositions.size() != 1;

  std::vector<std::string> paramClause;
  if (!appendSubstitutedClauseExcept(paramClause, targetParent, replayInfo->substitutionForBanksSub[targetParentIndex], targetLiteral)
    || !appendSubstitutedClauseExcept(paramClause, equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral)) {
    return false;
  }
  std::string rewrittenTargetJson;
  if (!replacedSubstitutedLiteralPreservingEqualityJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], targetRedex, to, false, rewrittenTargetJson)) {
    return false;
  }
  paramClause.push_back(rewrittenTargetJson);
  if (targetLiteral->isEquality()) {
    std::string swappedRewrittenTargetJson;
    if (!replacedSubstitutedLiteralPreservingEqualityJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], targetRedex, to, true, swappedRewrittenTargetJson)) {
      return false;
    }
    if (rewrittenTargetJson != swappedRewrittenTargetJson) {
      symmetryCandidates.push_back({rewrittenTargetJson, swappedRewrittenTargetJson});
    }
  }
  std::sort(paramClause.begin(), paramClause.end());
  paramClause.erase(std::unique(paramClause.begin(), paramClause.end()), paramClause.end());
  std::vector<std::string> actual;
  if (!normalizedClause(unit->asClause(), actual)) {
    return false;
  }

  auto canNormalizeBySymmetry = [&](const std::vector<std::string>& source, std::vector<std::pair<std::string, std::string>>& flips) {
    std::vector<std::string> current = source;
    flips.clear();
    for (std::size_t guard = 0; current != actual && guard < symmetryCandidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : symmetryCandidates) {
        if (std::find(actual.begin(), actual.end(), candidate.second) == actual.end()) {
          continue;
        }
        auto currentIt = std::find(current.begin(), current.end(), candidate.first);
        if (currentIt == current.end()) {
          continue;
        }
        *currentIt = candidate.second;
        std::sort(current.begin(), current.end());
        current.erase(std::unique(current.begin(), current.end()), current.end());
        flips.push_back(candidate);
        changed = true;
        break;
      }
      if (!changed) {
        break;
      }
    }
    return current == actual;
  };
  std::vector<std::pair<std::string, std::string>> finalSymmetryFlips;
  bool clauseWideParamodulation = false;
  std::vector<TargetRewrite> targetRewrites;
  if (!canNormalizeBySymmetry(paramClause, finalSymmetryFlips)) {
    std::vector<std::string> clauseWideParamClause;
    std::vector<TargetRewrite> clauseWideTargetRewrites;
    if (!appendClauseWithAllReplacements(
          clauseWideParamClause,
          targetParent,
          replayInfo->substitutionForBanksSub[targetParentIndex],
          targetRedex,
          to,
          clauseWideTargetRewrites)
      || !appendSubstitutedClauseExcept(
          clauseWideParamClause,
          equalityParent,
          replayInfo->substitutionForBanksSub[equalityParentIndex],
          equalityLiteral)) {
      return false;
    }
    std::sort(clauseWideParamClause.begin(), clauseWideParamClause.end());
    clauseWideParamClause.erase(std::unique(clauseWideParamClause.begin(), clauseWideParamClause.end()), clauseWideParamClause.end());
    if (!canNormalizeBySymmetry(clauseWideParamClause, finalSymmetryFlips)) {
      return false;
    }
    clauseWideParamodulation = true;
    paramClause = clauseWideParamClause;
    targetRewrites = clauseWideTargetRewrites;
  }

  std::string stepBase = "u" + std::to_string(unit->number());
  std::vector<std::string> steps;
  std::vector<std::string> parentIds(2);
  for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
    std::string substitutionJson;
    std::string clauseJson;
    if (!certificateSubstitutionJson(replayInfo->substitutionForBanksSub[parentIndex], substitutionJson)
      || !certificateSubstitutedClausePreservingEqualityJson(parents[parentIndex], replayInfo->substitutionForBanksSub[parentIndex], clauseJson)) {
      return false;
    }
    parentIds[parentIndex] = "u" + std::to_string(parents[parentIndex]->number());
    if (substitutionJson != "{}") {
      std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
      steps.push_back(
        "{\"id\":" + quote(substituteId) + ","
        "\"rule\":\"substitute\","
        "\"parents\":[" + quote(parentIds[parentIndex]) + "],"
        "\"substitution\":" + substitutionJson + ","
        "\"clause\":" + clauseJson + "}");
      parentIds[parentIndex] = substituteId;
    }
  }

  std::string equalityJson;
  std::string fromJson;
  std::string toJson;
  std::string targetJson;
  std::string conclusionJson;
  std::string equalityParentLiteralJson;
  if (!certificateSubstitutedLiteralPreservingEqualityJson(equalityLiteral, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityParentLiteralJson)
    || !positiveEqualityLiteralJson(from, to, equalityJson)
    || !certificateTermJson(from, fromJson)
    || !certificateTermJson(to, toJson)
    || !certificateSubstitutedLiteralPreservingEqualityJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], targetJson)
    || !certificateClauseJson(unit->asClause(), conclusionJson)) {
    return false;
  }
  std::string equalityParentId = parentIds[equalityParentIndex];
  if (equalityParentLiteralJson != equalityJson) {
    std::string symmetryClauseJson;
    if (!substitutedClauseReplacingOneLiteralJson(equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral, equalityJson, symmetryClauseJson)) {
      return false;
    }
    std::string symmetryStepId = stepBase + "_symmetry";
    steps.push_back(
      "{\"id\":" + quote(symmetryStepId) + ","
      "\"rule\":\"equality_symmetry\","
      "\"parents\":[" + quote(equalityParentId) + "],"
      "\"literal\":" + equalityParentLiteralJson + ","
      "\"clause\":" + symmetryClauseJson + "}");
    equalityParentId = symmetryStepId;
  }
  std::string paramodulateStepId = finalSymmetryFlips.empty() ? stepBase : stepBase + "_paramodulate";
  std::string paramodulateClauseJson = finalSymmetryFlips.empty() ? conclusionJson : jsonArray(paramClause);
  std::string ruleName = simultaneousParamodulation ? "paramodulate_all" : "paramodulate";
  std::string rewriteFields = "\"target\":" + targetJson + ",";
  if (clauseWideParamodulation) {
    if (targetRewrites.empty()) {
      return false;
    }
    std::vector<std::string> currentClause;
    std::vector<std::string> equalityRemainder;
    if (!substitutedClauseLiterals(targetParent, replayInfo->substitutionForBanksSub[targetParentIndex], currentClause)
      || !substitutedClauseExceptLiterals(equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral, equalityRemainder)) {
      return false;
    }
    std::string currentTargetId = parentIds[targetParentIndex];
    for (std::size_t rewriteIndex = 0; rewriteIndex < targetRewrites.size(); ++rewriteIndex) {
      const TargetRewrite& rewrite = targetRewrites[rewriteIndex];
      auto literalIt = std::find(currentClause.begin(), currentClause.end(), rewrite.literalJson);
      if (literalIt == currentClause.end()) {
        return false;
      }
      currentClause.erase(literalIt);
      currentClause.push_back(rewrite.rewrittenJson);
      currentClause.insert(currentClause.end(), equalityRemainder.begin(), equalityRemainder.end());
      std::sort(currentClause.begin(), currentClause.end());
      currentClause.erase(std::unique(currentClause.begin(), currentClause.end()), currentClause.end());

      bool lastRewrite = rewriteIndex + 1 == targetRewrites.size();
      std::string rewriteStepId = lastRewrite && finalSymmetryFlips.empty()
        ? stepBase
        : stepBase + "_paramodulate" + std::to_string(rewriteIndex);
      std::string rewriteRuleName = rewrite.positions.size() == 1 ? "paramodulate" : "paramodulate_all";
      std::string rewritePositionFields = rewrite.positions.size() == 1
        ? "\"position\":" + positionJson(rewrite.positions.front()) + ","
        : "\"positions\":" + positionsJson(rewrite.positions) + ",";
      std::string rewriteScopeFields;
      if (rewrite.positions.size() == 1) {
        rewriteScopeJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], rewrite.positions.front(), rewriteScopeFields);
      }
      std::string rewriteClauseJson = lastRewrite && finalSymmetryFlips.empty()
        ? conclusionJson
        : jsonArray(currentClause);
      steps.push_back(
        "{\"id\":" + quote(rewriteStepId) + ","
        "\"rule\":\"" + rewriteRuleName + "\","
        "\"parents\":["
        + quote(equalityParentId) + ","
        + quote(currentTargetId) + "],"
        "\"equality\":" + equalityJson + ","
        "\"from\":" + fromJson + ","
        "\"to\":" + toJson + ","
        "\"target\":" + rewrite.literalJson + ","
        "\"rewritten_target\":" + rewrite.rewrittenJson + ","
        + rewritePositionFields
        + rewriteScopeFields
        + "\"substitution\":{},"
        "\"clause\":" + rewriteClauseJson + "}");
      currentTargetId = rewriteStepId;
    }
    paramClause = currentClause;
    paramodulateStepId = currentTargetId;
  } else {
    if (simultaneousParamodulation && targetLiteral->isEquality()) {
      std::vector<std::string> currentParamClause;
      std::vector<std::string> equalityRemainder;
      if (!substitutedClauseLiterals(targetParent, replayInfo->substitutionForBanksSub[targetParentIndex], currentParamClause)
        || !substitutedClauseExceptLiterals(equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral, equalityRemainder)) {
        return false;
      }
      std::string currentTargetId = parentIds[targetParentIndex];
      std::string currentTargetJson = targetJson;
      Kernel::TermList currentLhs = Kernel::SubstHelper::apply(*targetLiteral->nthArgument(0), replayInfo->substitutionForBanksSub[targetParentIndex]);
      Kernel::TermList currentRhs = Kernel::SubstHelper::apply(*targetLiteral->nthArgument(1), replayInfo->substitutionForBanksSub[targetParentIndex]);
      for (std::size_t rewriteIndex = 0; rewriteIndex < redexPositions.size(); ++rewriteIndex) {
        const std::vector<unsigned>& rewritePosition = redexPositions[rewriteIndex];
        if (rewritePosition.empty() || rewritePosition[0] > 1) {
          return false;
        }
        std::vector<unsigned> sidePosition(rewritePosition.begin() + 1, rewritePosition.end());
        Kernel::TermList rewrittenSide;
        if (rewritePosition[0] == 0) {
          if (!replaceTermAtPrintedPosition(replaceTermAtPrintedPosition, currentLhs, sidePosition, 0, to, rewrittenSide)) {
            return false;
          }
          currentLhs = rewrittenSide;
        } else {
          if (!replaceTermAtPrintedPosition(replaceTermAtPrintedPosition, currentRhs, sidePosition, 0, to, rewrittenSide)) {
            return false;
          }
          currentRhs = rewrittenSide;
        }
        std::string nextTargetJson;
        if (!equalityLiteralFromTermsJson(targetLiteral, currentLhs, currentRhs, nextTargetJson)) {
          return false;
        }
        auto literalIt = std::find(currentParamClause.begin(), currentParamClause.end(), currentTargetJson);
        if (literalIt == currentParamClause.end()) {
          return false;
        }
        currentParamClause.erase(literalIt);
        currentParamClause.push_back(nextTargetJson);
        currentParamClause.insert(currentParamClause.end(), equalityRemainder.begin(), equalityRemainder.end());
        std::sort(currentParamClause.begin(), currentParamClause.end());
        currentParamClause.erase(std::unique(currentParamClause.begin(), currentParamClause.end()), currentParamClause.end());

        bool lastRewrite = rewriteIndex + 1 == redexPositions.size();
        std::string rewriteStepId = lastRewrite && finalSymmetryFlips.empty()
          ? stepBase
          : stepBase + "_paramodulate" + std::to_string(rewriteIndex);
        std::string rewriteClauseJson = lastRewrite && finalSymmetryFlips.empty()
          ? conclusionJson
          : jsonArray(currentParamClause);
        std::string rewriteScopeFields;
        rewriteScopeJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], rewritePosition, rewriteScopeFields);
        steps.push_back(
          "{\"id\":" + quote(rewriteStepId) + ","
          "\"rule\":\"paramodulate\","
          "\"parents\":["
          + quote(equalityParentId) + ","
          + quote(currentTargetId) + "],"
          "\"equality\":" + equalityJson + ","
          "\"from\":" + fromJson + ","
          "\"to\":" + toJson + ","
          "\"target\":" + currentTargetJson + ","
          "\"rewritten_target\":" + nextTargetJson + ","
          "\"position\":" + positionJson(redexPositions[rewriteIndex]) + ","
          + rewriteScopeFields
          + "\"substitution\":{},"
          "\"clause\":" + rewriteClauseJson + "}");
        currentTargetId = rewriteStepId;
        currentTargetJson = nextTargetJson;
      }
      paramClause = currentParamClause;
      paramodulateStepId = currentTargetId;
    } else {
      rewriteFields += "\"rewritten_target\":" + rewrittenTargetJson + ",";
      rewriteFields += simultaneousParamodulation
        ? "\"positions\":" + positionsJson(redexPositions) + ","
        : "\"position\":" + positionJson(position) + ",";
      if (!simultaneousParamodulation) {
        std::string rewriteScopeFields;
        if (rewriteScopeJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], position, rewriteScopeFields)) {
          rewriteFields += rewriteScopeFields;
        }
      }
      steps.push_back(
        "{\"id\":" + quote(paramodulateStepId) + ","
        "\"rule\":\"" + ruleName + "\","
        "\"parents\":["
        + quote(equalityParentId) + ","
        + quote(parentIds[targetParentIndex]) + "],"
        "\"equality\":" + equalityJson + ","
        "\"from\":" + fromJson + ","
        "\"to\":" + toJson + ","
        + rewriteFields
        + "\"substitution\":{},"
        "\"clause\":" + paramodulateClauseJson + "}");
    }
  }
  std::string currentStepId = paramodulateStepId;
  std::vector<std::string> currentClause = paramClause;
  for (std::size_t index = 0; index < finalSymmetryFlips.size(); ++index) {
    const auto& flip = finalSymmetryFlips[index];
    auto literalIt = std::find(currentClause.begin(), currentClause.end(), flip.first);
    if (literalIt == currentClause.end()) {
      return false;
    }
    *literalIt = flip.second;
    std::sort(currentClause.begin(), currentClause.end());
    currentClause.erase(std::unique(currentClause.begin(), currentClause.end()), currentClause.end());
    std::string normalizeStepId = index + 1 == finalSymmetryFlips.size()
      ? stepBase
      : stepBase + "_normalize" + std::to_string(index);
    steps.push_back(
      "{\"id\":" + quote(normalizeStepId) + ","
      "\"rule\":\"equality_symmetry\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"literal\":" + flip.first + ","
      "\"clause\":" + jsonArray(currentClause) + "}");
    currentStepId = normalizeStepId;
  }
  result = jsonArray(steps);
  return true;
}

bool MegalodonChecker::formulaToMegalodon(Kernel::Formula* formula, std::string& result)
{
  std::map<unsigned, Kernel::TermList> substitution;
  return formulaToMegalodon(formula, substitution, result);
}

bool MegalodonChecker::conjunctionToMegalodon(
  const std::vector<Kernel::Formula*>& conjuncts,
  std::size_t begin,
  const std::map<unsigned, Kernel::TermList>& substitution,
  std::string& result)
{
  if (begin >= conjuncts.size()) {
    return false;
  }
  if (begin + 1 == conjuncts.size()) {
    return formulaToMegalodon(conjuncts[begin], substitution, result);
  }

  std::string lhs;
  std::string rhs;
  if (!formulaToMegalodon(conjuncts[begin], substitution, lhs)
    || !conjunctionToMegalodon(conjuncts, begin + 1, substitution, rhs)) {
    return false;
  }
  _usesConjunction = true;
  result = "vampire_and " + parenthesize(lhs) + " " + parenthesize(rhs);
  return true;
}

std::string MegalodonChecker::existentialNameForSort(const std::string& sort) const
{
  std::string result = "vampire_exists_";
  bool previousSeparator = false;
  for (char ch : sort) {
    unsigned char uch = static_cast<unsigned char>(ch);
    if (std::isalnum(uch)) {
      result += ch;
      previousSeparator = false;
    } else if (!previousSeparator) {
      result += '_';
      previousSeparator = true;
    }
  }
  while (!result.empty() && result.back() == '_') {
    result.pop_back();
  }
  return result;
}

bool MegalodonChecker::formulaToMegalodon(Kernel::Formula* formula, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result)
{
  if (_renderDepth > 512) {
    return false;
  }
  struct RenderDepthGuard {
    unsigned& depth;
    RenderDepthGuard(unsigned& depth) : depth(depth) { ++depth; }
    ~RenderDepthGuard() { --depth; }
  } renderDepthGuard(_renderDepth);

  switch (formula->connective()) {
    case Kernel::LITERAL: {
      Kernel::Literal* literal = formula->literal();
      if (literal->isNegative()) {
        Kernel::Literal* positive = Kernel::Literal::complementaryLiteral(literal);
        if (!literalToMegalodon(positive, result)) {
          return false;
        }
        _usesFalse = true;
        result = parenthesize(result) + " -> vampire_false";
        return true;
      }
      if (literal->isEquality()) {
        Kernel::TermList equalityArgumentSort = Kernel::SortHelper::getEqualityArgumentSort(literal);
        std::string equalitySort;
        if (!sortToMegalodon(equalityArgumentSort, equalitySort)) {
          return false;
        }
        std::string lhs;
        std::string rhs;
        if (!termToMegalodon(*literal->nthArgument(0), substitution, lhs) || !termToMegalodon(*literal->nthArgument(1), substitution, rhs)) {
          return false;
        }
        if (equalitySort == "prop") {
          _usesPropEquality = true;
          result = "vampire_eq_prop " + parenthesize(lhs) + " " + parenthesize(rhs);
          return true;
        }
        if (_renderingReplayExtra) {
          result = lhs + " = " + rhs;
          return true;
        }
        if (!recordEqualitySort(equalityArgumentSort)) {
          return false;
        }
        result = lhs + " = " + rhs;
        return true;
      }
      std::string name = predicateName(literal->functor());
      if (literal->arity() == 0) {
        result = name;
        return true;
      }
      std::ostringstream out;
      out << name;
      for (unsigned i = 0; i < literal->arity(); ++i) {
        std::string arg;
        if (!termToMegalodon(*literal->nthArgument(i), substitution, arg)) {
          return false;
        }
        out << ' ' << arg;
      }
      result = out.str();
      return true;
    }
    case Kernel::BOOL_TERM:
      if (formula->getBooleanTerm().isVar()) {
        result = variableName(formula->getBooleanTerm().var());
        return true;
      }
      return termToMegalodon(formula->getBooleanTerm(), substitution, result);
    case Kernel::NAME:
      return signedNameToMegalodon(static_cast<Kernel::NamedFormula*>(formula)->name(), result);
    case Kernel::IMP: {
      std::string lhs;
      std::string rhs;
      if (!formulaToMegalodon(formula->left(), substitution, lhs) || !formulaToMegalodon(formula->right(), substitution, rhs)) {
        return false;
      }
      bool leftIsNegativeLiteral =
        formula->left()->connective() == Kernel::LITERAL
        && formula->left()->literal()->isNegative();
      if (
        formula->left()->connective() == Kernel::IMP
        || formula->left()->connective() == Kernel::FORALL
        || formula->left()->connective() == Kernel::NOT
        || formula->left()->connective() == Kernel::IFF
        || formula->left()->connective() == Kernel::XOR
        || leftIsNegativeLiteral
      ) {
        lhs = parenthesize(lhs);
      }
      result = lhs + " -> " + rhs;
      return true;
    }
    case Kernel::IFF: {
      std::string lhs;
      std::string rhs;
      if (!formulaToMegalodon(formula->left(), substitution, lhs) || !formulaToMegalodon(formula->right(), substitution, rhs)) {
        return false;
      }
      _usesConjunction = true;
      result = "vampire_and "
        + parenthesize(parenthesize(lhs) + " -> " + rhs) + " "
        + parenthesize(parenthesize(rhs) + " -> " + lhs);
      return true;
    }
    case Kernel::NOT: {
      std::string body;
      if (!formulaToMegalodon(formula->uarg(), substitution, body)) {
        return false;
      }
      _usesFalse = true;
      result = parenthesize(body) + " -> vampire_false";
      return true;
    }
    case Kernel::OR: {
      std::vector<std::string> disjuncts;
      auto args = formula->args()->iter();
      while (args.hasNext()) {
        std::string disjunct;
        if (!formulaToMegalodon(args.next(), substitution, disjunct)) {
          return false;
        }
        disjuncts.push_back(disjunct);
      }
      if (disjuncts.empty()) {
        return false;
      }
      if (disjuncts.size() == 1) {
        result = disjuncts[0];
        return true;
      }
      if (!skeletonDisjunctionToMegalodon(disjuncts, result)) {
        return false;
      }
      return true;
    }
    case Kernel::FORALL: {
      std::string body;
      if (!formulaToMegalodon(formula->qarg(), substitution, body)) {
        return false;
      }
      std::vector<std::pair<unsigned, Kernel::TermList>> vars;
      Kernel::VSList::Iterator vit(formula->vars());
      while (vit.hasNext()) {
        vars.push_back(vit.next());
      }
      for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
        std::string sort;
        if (!sortToMegalodon(it->second, sort)) {
          return false;
        }
        body = "forall " + variableName(it->first) + ":" + sort + ", " + body;
      }
      result = body;
      return true;
    }
    case Kernel::AND: {
      std::vector<Kernel::Formula*> conjuncts;
      auto args = formula->args()->iter();
      while (args.hasNext()) {
        conjuncts.push_back(args.next());
      }
      return conjunctionToMegalodon(conjuncts, 0, substitution, result);
    }
    case Kernel::EXISTS: {
      std::string body;
      if (!formulaToMegalodon(formula->qarg(), substitution, body)) {
        return false;
      }
      std::vector<std::pair<unsigned, Kernel::TermList>> vars;
      Kernel::VSList::Iterator vit(formula->vars());
      while (vit.hasNext()) {
        vars.push_back(vit.next());
      }
      for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
        std::string sort;
        if (!sortToMegalodon(it->second, sort)) {
          return false;
        }
        std::string existsName = existentialNameForSort(sort);
        if (sort == "set") {
          _usesSetExists = true;
        }
        body = existsName + " (fun " + variableName(it->first) + ":" + sort + " => " + body + ")";
      }
      result = body;
      return true;
    }
    case Kernel::TRUE:
      result = "true";
      return true;
    case Kernel::FALSE:
      result = "false";
      return true;
    default:
      return false;
  }
}

bool MegalodonChecker::quantifiedPropHypothesis(Kernel::Formula* formula, std::string& binderName, Kernel::Formula*& body)
{
  if (formula->connective() != Kernel::FORALL || Kernel::VSList::length(formula->vars()) != 1) {
    return false;
  }
  Kernel::VSList::Iterator vit(formula->vars());
  auto [var, sort] = vit.next();
  if (sort != Kernel::AtomicSort::boolSort() && sort != Kernel::AtomicSort::defaultSort()) {
    return false;
  }
  Kernel::Formula* arg = formula->qarg();
  if (arg->connective() != Kernel::BOOL_TERM || !arg->getBooleanTerm().isVar() || arg->getBooleanTerm().var() != var) {
    return false;
  }
  binderName = variableName(var);
  body = arg;
  return true;
}

bool MegalodonChecker::equalityLiteral(Kernel::Formula* formula, Kernel::TermList& lhs, Kernel::TermList& rhs)
{
  if (formula->connective() != Kernel::LITERAL) {
    return false;
  }
  Kernel::Literal* literal = formula->literal();
  if (!literal->isEquality() || literal->isNegative()) {
    return false;
  }
  std::string equalitySort;
  if (!sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort) || equalitySort != "set") {
    return false;
  }
  lhs = *literal->nthArgument(0);
  rhs = *literal->nthArgument(1);
  _usesEquality = true;
  return true;
}

bool MegalodonChecker::equalityProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result)
{
  Kernel::TermList goalLhs;
  Kernel::TermList goalRhs;
  if (!equalityLiteral(goal, goalLhs, goalRhs)) {
    return false;
  }

  std::string goalLhsText;
  if (!termToMegalodon(goalLhs, goalLhsText)) {
    return false;
  }
  std::string goalLhsArgument = parenthesize(goalLhsText);
  if (goalLhs == goalRhs) {
    result = parenthesize("fun Q:set->prop => fun H:Q " + goalLhsArgument + " => H");
    return true;
  }

  std::string goalRhsText;
  if (!termToMegalodon(goalRhs, goalRhsText)) {
    return false;
  }
  std::string goalRhsArgument = parenthesize(goalRhsText);
  std::string reflGoalRhs = parenthesize("fun Q:set->prop => fun H:Q " + goalRhsArgument + " => H");

  for (const Hypothesis& hypothesis : hypotheses) {
    Kernel::Formula* body = hypothesis.formula;
    std::vector<unsigned> variables;
    while (body->connective() == Kernel::FORALL) {
      Kernel::VSList::Iterator vit(body->vars());
      while (vit.hasNext()) {
        variables.push_back(vit.next().first);
      }
      body = body->qarg();
    }

    Kernel::TermList hypothesisLhs;
    Kernel::TermList hypothesisRhs;
    if (!equalityLiteral(body, hypothesisLhs, hypothesisRhs)) {
      continue;
    }

    std::map<unsigned, Kernel::TermList> directSubstitution;
    if (matchTerm(hypothesisLhs, goalLhs, variables, directSubstitution)
      && matchTerm(hypothesisRhs, goalRhs, variables, directSubstitution)) {
      std::ostringstream proof;
      proof << hypothesis.proof;
      bool complete = true;
      for (unsigned variable : variables) {
        auto found = directSubstitution.find(variable);
        if (found == directSubstitution.end()) {
          complete = false;
          break;
        }
        std::string arg;
        if (!termToMegalodon(found->second, arg)) {
          complete = false;
          break;
        }
        proof << ' ' << parenthesize(arg);
      }
      if (complete) {
        result = parenthesize(proof.str());
        return true;
      }
    }

    std::map<unsigned, Kernel::TermList> reverseSubstitution;
    if (!matchTerm(hypothesisLhs, goalRhs, variables, reverseSubstitution)
      || !matchTerm(hypothesisRhs, goalLhs, variables, reverseSubstitution)) {
      continue;
    }

    std::ostringstream proof;
    proof << hypothesis.proof;
    bool complete = true;
    for (unsigned variable : variables) {
      auto found = reverseSubstitution.find(variable);
      if (found == reverseSubstitution.end()) {
        complete = false;
        break;
      }
      std::string arg;
      if (!termToMegalodon(found->second, arg)) {
        complete = false;
        break;
      }
      proof << ' ' << parenthesize(arg);
    }
    if (!complete) {
      continue;
    }
    result = parenthesize(
      parenthesize(proof.str()) + " "
      + parenthesize("fun Zsym:set => Zsym = " + goalRhsArgument) + " "
      + reflGoalRhs
    );
    return true;
  }

  for (const Hypothesis& leftHypothesis : hypotheses) {
    Kernel::TermList leftLhs;
    Kernel::TermList leftRhs;
    if (!equalityLiteral(leftHypothesis.formula, leftLhs, leftRhs) || leftLhs != goalLhs) {
      continue;
    }
    for (const Hypothesis& rightHypothesis : hypotheses) {
      Kernel::TermList rightLhs;
      Kernel::TermList rightRhs;
      if (!equalityLiteral(rightHypothesis.formula, rightLhs, rightRhs)) {
        continue;
      }
      if (rightLhs != leftRhs || rightRhs != goalRhs) {
        continue;
      }
      result = parenthesize(
        "fun Q:set->prop => fun H:Q " + goalLhsArgument + " => "
        + rightHypothesis.proof + " Q (" + leftHypothesis.proof + " Q H)"
      );
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::matchTerm(
  Kernel::TermList pattern,
  Kernel::TermList target,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution)
{
  std::map<unsigned, Kernel::TermList> targetSubstitution;
  return matchTerm(pattern, target, targetSubstitution, variables, substitution);
}

bool MegalodonChecker::matchTerm(
  Kernel::TermList pattern,
  Kernel::TermList target,
  const std::map<unsigned, Kernel::TermList>& targetSubstitution,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution)
{
  if (target.isVar()) {
    auto foundTarget = targetSubstitution.find(target.var());
    if (foundTarget != targetSubstitution.end()) {
      target = foundTarget->second;
    }
  }
  if (pattern.isVar()) {
    if (std::find(variables.begin(), variables.end(), pattern.var()) != variables.end()) {
      auto found = substitution.find(pattern.var());
      if (found == substitution.end()) {
        substitution.emplace(pattern.var(), target);
        return true;
      }
      return found->second == target;
    }
    return pattern == target;
  }
  if (pattern.isApplication() || target.isApplication()) {
    if (!pattern.isApplication() || !target.isApplication()) {
      return false;
    }
    return matchTerm(pattern.lhs(), target.lhs(), targetSubstitution, variables, substitution)
      && matchTerm(pattern.rhs(), target.rhs(), targetSubstitution, variables, substitution);
  }
  if (!pattern.isTerm() || !target.isTerm()) {
    return pattern == target;
  }
  Kernel::Term* patternTerm = pattern.term();
  Kernel::Term* targetTerm = target.term();
  if (patternTerm->functor() != targetTerm->functor() || patternTerm->numTermArguments() != targetTerm->numTermArguments()) {
    return false;
  }
  for (unsigned i = 0; i < patternTerm->numTermArguments(); ++i) {
    if (!matchTerm(patternTerm->termArg(i), targetTerm->termArg(i), targetSubstitution, variables, substitution)) {
      return false;
    }
  }
  return true;
}

bool MegalodonChecker::matchFormula(
  Kernel::Formula* pattern,
  Kernel::Formula* target,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution)
{
  std::map<unsigned, Kernel::TermList> targetSubstitution;
  return matchFormula(pattern, target, targetSubstitution, variables, substitution);
}

bool MegalodonChecker::matchFormula(
  Kernel::Formula* pattern,
  Kernel::Formula* target,
  const std::map<unsigned, Kernel::TermList>& targetSubstitution,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution)
{
  if (pattern->connective() != target->connective()) {
    return false;
  }
  switch (pattern->connective()) {
    case Kernel::FORALL: {
      if (Kernel::VSList::length(pattern->vars()) != Kernel::VSList::length(target->vars())) {
        return false;
      }
      std::map<unsigned, Kernel::TermList> extendedTargetSubstitution = targetSubstitution;
      std::vector<unsigned> scopedVariables = variables;
      Kernel::VSList::Iterator pit(pattern->vars());
      Kernel::VSList::Iterator tit(target->vars());
      while (pit.hasNext() && tit.hasNext()) {
        auto [patternVar, patternSort] = pit.next();
        auto [targetVar, targetSort] = tit.next();
        std::string patternSortText;
        std::string targetSortText;
        if (!sortToMegalodon(patternSort, patternSortText) || !sortToMegalodon(targetSort, targetSortText) || patternSortText != targetSortText) {
          return false;
        }
        extendedTargetSubstitution[targetVar] = Kernel::TermList::var(patternVar);
        scopedVariables.erase(std::remove(scopedVariables.begin(), scopedVariables.end(), patternVar), scopedVariables.end());
      }
      return matchFormula(pattern->qarg(), target->qarg(), extendedTargetSubstitution, scopedVariables, substitution);
    }
    case Kernel::IMP:
      return matchFormula(pattern->left(), target->left(), targetSubstitution, variables, substitution)
        && matchFormula(pattern->right(), target->right(), targetSubstitution, variables, substitution);
    case Kernel::BOOL_TERM:
      return matchTerm(pattern->getBooleanTerm(), target->getBooleanTerm(), targetSubstitution, variables, substitution);
    case Kernel::LITERAL: {
      Kernel::Literal* patternLiteral = pattern->literal();
      Kernel::Literal* targetLiteral = target->literal();
      if (patternLiteral->functor() != targetLiteral->functor()
        || patternLiteral->polarity() != targetLiteral->polarity()
        || patternLiteral->arity() != targetLiteral->arity()) {
        return false;
      }
      for (unsigned i = 0; i < patternLiteral->arity(); ++i) {
        if (!matchTerm(*patternLiteral->nthArgument(i), *targetLiteral->nthArgument(i), targetSubstitution, variables, substitution)) {
          return false;
        }
      }
      return true;
    }
    case Kernel::TRUE:
    case Kernel::FALSE:
      return true;
    default:
      return false;
  }
}

bool MegalodonChecker::termMatchesAfterReplacement(
  Kernel::TermList source,
  Kernel::TermList target,
  Kernel::TermList needle,
  Kernel::TermList replacement,
  bool& replaced)
{
  if (source == needle) {
    if (target != replacement) {
      return false;
    }
    replaced = true;
    return true;
  }
  if (source.isVar()) {
    return source == target;
  }
  if (source.isApplication() || target.isApplication()) {
    if (!source.isApplication() || !target.isApplication()) {
      return false;
    }
    return termMatchesAfterReplacement(source.lhs(), target.lhs(), needle, replacement, replaced)
      && termMatchesAfterReplacement(source.rhs(), target.rhs(), needle, replacement, replaced);
  }
  if (!source.isTerm() || !target.isTerm()) {
    return source == target;
  }
  Kernel::Term* sourceTerm = source.term();
  Kernel::Term* targetTerm = target.term();
  if (sourceTerm->functor() != targetTerm->functor() || sourceTerm->numTermArguments() != targetTerm->numTermArguments()) {
    return false;
  }
  for (unsigned i = 0; i < sourceTerm->numTermArguments(); ++i) {
    if (!termMatchesAfterReplacement(sourceTerm->termArg(i), targetTerm->termArg(i), needle, replacement, replaced)) {
      return false;
    }
  }
  return true;
}

bool MegalodonChecker::formulaMatchesAfterReplacement(
  Kernel::Formula* source,
  Kernel::Formula* target,
  Kernel::TermList needle,
  Kernel::TermList replacement,
  bool& replaced)
{
  if (source->connective() != target->connective()) {
    return false;
  }
  switch (source->connective()) {
    case Kernel::BOOL_TERM:
      return termMatchesAfterReplacement(source->getBooleanTerm(), target->getBooleanTerm(), needle, replacement, replaced);
    case Kernel::LITERAL: {
      Kernel::Literal* sourceLiteral = source->literal();
      Kernel::Literal* targetLiteral = target->literal();
      if (sourceLiteral->functor() != targetLiteral->functor()
        || sourceLiteral->polarity() != targetLiteral->polarity()
        || sourceLiteral->arity() != targetLiteral->arity()) {
        return false;
      }
      for (unsigned i = 0; i < sourceLiteral->arity(); ++i) {
        if (!termMatchesAfterReplacement(*sourceLiteral->nthArgument(i), *targetLiteral->nthArgument(i), needle, replacement, replaced)) {
          return false;
        }
      }
      return true;
    }
    default:
      return false;
  }
}

bool MegalodonChecker::termMatchesAfterPatternReplacement(
  Kernel::TermList source,
  Kernel::TermList target,
  Kernel::TermList pattern,
  Kernel::TermList replacement,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution)
{
  std::map<unsigned, Kernel::TermList> candidateSubstitution;
  if (matchTerm(pattern, source, variables, candidateSubstitution)
    && matchTerm(replacement, target, variables, candidateSubstitution)) {
    substitution = candidateSubstitution;
    return true;
  }

  if (source.isApplication() || target.isApplication()) {
    if (!source.isApplication() || !target.isApplication()) {
      return false;
    }
    if (source.rhs() == target.rhs()
      && termMatchesAfterPatternReplacement(source.lhs(), target.lhs(), pattern, replacement, variables, candidateSubstitution)) {
      substitution = candidateSubstitution;
      return true;
    }
    if (source.lhs() == target.lhs()
      && termMatchesAfterPatternReplacement(source.rhs(), target.rhs(), pattern, replacement, variables, candidateSubstitution)) {
      substitution = candidateSubstitution;
      return true;
    }
    return false;
  }

  if (source.isVar() || target.isVar()) {
    return false;
  }

  if (!source.isTerm() || !target.isTerm()) {
    return false;
  }

  Kernel::Term* sourceTerm = source.term();
  Kernel::Term* targetTerm = target.term();
  if (sourceTerm->functor() != targetTerm->functor() || sourceTerm->numTermArguments() != targetTerm->numTermArguments()) {
    return false;
  }
  for (unsigned i = 0; i < sourceTerm->numTermArguments(); ++i) {
    candidateSubstitution.clear();
    if (!termMatchesAfterPatternReplacement(sourceTerm->termArg(i), targetTerm->termArg(i), pattern, replacement, variables, candidateSubstitution)) {
      continue;
    }
    bool complete = true;
    for (unsigned j = 0; j < sourceTerm->numTermArguments(); ++j) {
      if (i != j && sourceTerm->termArg(j) != targetTerm->termArg(j)) {
        complete = false;
        break;
      }
    }
    if (complete) {
      substitution = candidateSubstitution;
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::formulaMatchesAfterPatternReplacement(
  Kernel::Formula* source,
  Kernel::Formula* target,
  Kernel::TermList pattern,
  Kernel::TermList replacement,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution)
{
  if (source->connective() != target->connective()) {
    return false;
  }
  switch (source->connective()) {
    case Kernel::BOOL_TERM:
      return termMatchesAfterPatternReplacement(source->getBooleanTerm(), target->getBooleanTerm(), pattern, replacement, variables, substitution);
    case Kernel::LITERAL: {
      Kernel::Literal* sourceLiteral = source->literal();
      Kernel::Literal* targetLiteral = target->literal();
      if (sourceLiteral->functor() != targetLiteral->functor()
        || sourceLiteral->polarity() != targetLiteral->polarity()
        || sourceLiteral->arity() != targetLiteral->arity()) {
        return false;
      }
      for (unsigned i = 0; i < sourceLiteral->arity(); ++i) {
        std::map<unsigned, Kernel::TermList> candidateSubstitution;
        if (!termMatchesAfterPatternReplacement(*sourceLiteral->nthArgument(i), *targetLiteral->nthArgument(i), pattern, replacement, variables, candidateSubstitution)) {
          continue;
        }
        bool complete = true;
        for (unsigned j = 0; j < sourceLiteral->arity(); ++j) {
          if (i != j && *sourceLiteral->nthArgument(j) != *targetLiteral->nthArgument(j)) {
            complete = false;
            break;
          }
        }
        if (complete) {
          substitution = candidateSubstitution;
          return true;
        }
      }
      return false;
    }
    default:
      return false;
  }
}

bool MegalodonChecker::rewriteFormulaOnce(
  Kernel::Formula* source,
  Kernel::TermList pattern,
  Kernel::TermList replacement,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution,
  Kernel::Formula*& result)
{
  switch (source->connective()) {
    case Kernel::BOOL_TERM: {
      Kernel::TermList rewritten;
      if (!rewriteTermOnce(source->getBooleanTerm(), pattern, replacement, variables, substitution, rewritten)) {
        return false;
      }
      result = Kernel::BoolTermFormula::create(rewritten);
      return true;
    }
    case Kernel::LITERAL: {
      Kernel::Literal* literal = source->literal();
      for (unsigned i = 0; i < literal->arity(); ++i) {
        std::map<unsigned, Kernel::TermList> candidateSubstitution;
        Kernel::TermList rewrittenArg;
        if (!rewriteTermOnce(*literal->nthArgument(i), pattern, replacement, variables, candidateSubstitution, rewrittenArg)) {
          continue;
        }
        std::vector<Kernel::TermList> args;
        args.reserve(literal->arity());
        for (unsigned j = 0; j < literal->arity(); ++j) {
          args.push_back(j == i ? rewrittenArg : *literal->nthArgument(j));
        }
        result = new Kernel::AtomicFormula(Kernel::Literal::create(literal, args.data()));
        substitution = candidateSubstitution;
        return true;
      }
      return false;
    }
    default:
      return false;
  }
}

bool MegalodonChecker::substituteTerm(
  Kernel::TermList term,
  const std::map<unsigned, Kernel::TermList>& substitution,
  Kernel::TermList& result)
{
  if (term.isVar()) {
    auto found = substitution.find(term.var());
    result = found == substitution.end() ? term : found->second;
    return true;
  }
  if (term.isApplication()) {
    Kernel::TermList lhs;
    Kernel::TermList rhs;
    if (!substituteTerm(term.lhs(), substitution, lhs) || !substituteTerm(term.rhs(), substitution, rhs)) {
      return false;
    }
    if (lhs == term.lhs() && rhs == term.rhs()) {
      result = term;
      return true;
    }
    result = HOL::create::app(*term.term()->nthArgument(0), *term.term()->nthArgument(1), lhs, rhs);
    return true;
  }
  if (!term.isTerm() || term.term()->isSpecial()) {
    result = term;
    return true;
  }

  Kernel::Term* original = term.term();
  std::vector<Kernel::TermList> args;
  args.reserve(original->arity());
  bool changed = false;
  for (unsigned i = 0; i < original->arity(); ++i) {
    Kernel::TermList arg;
    if (!substituteTerm(*original->nthArgument(i), substitution, arg)) {
      return false;
    }
    changed = changed || arg != *original->nthArgument(i);
    args.push_back(arg);
  }
  result = changed ? Kernel::TermList(Kernel::Term::create(original->functor(), original->arity(), args.data())) : term;
  return true;
}

bool MegalodonChecker::rewriteTermOnce(
  Kernel::TermList term,
  Kernel::TermList pattern,
  Kernel::TermList replacement,
  const std::vector<unsigned>& variables,
  std::map<unsigned, Kernel::TermList>& substitution,
  Kernel::TermList& result)
{
  substitution.clear();
  if (matchTerm(pattern, term, variables, substitution)) {
    return substituteTerm(replacement, substitution, result);
  }

  if (term.isApplication()) {
    std::map<unsigned, Kernel::TermList> childSubstitution;
    Kernel::TermList lhs;
    if (rewriteTermOnce(term.lhs(), pattern, replacement, variables, childSubstitution, lhs)) {
      result = HOL::create::app(*term.term()->nthArgument(0), *term.term()->nthArgument(1), lhs, term.rhs());
      substitution = childSubstitution;
      return true;
    }
    Kernel::TermList rhs;
    if (rewriteTermOnce(term.rhs(), pattern, replacement, variables, childSubstitution, rhs)) {
      result = HOL::create::app(*term.term()->nthArgument(0), *term.term()->nthArgument(1), term.lhs(), rhs);
      substitution = childSubstitution;
      return true;
    }
    return false;
  }

  if (!term.isTerm() || term.term()->isSpecial()) {
    return false;
  }

  Kernel::Term* original = term.term();
  for (unsigned i = 0; i < original->arity(); ++i) {
    std::map<unsigned, Kernel::TermList> childSubstitution;
    Kernel::TermList rewrittenArg;
    if (!rewriteTermOnce(*original->nthArgument(i), pattern, replacement, variables, childSubstitution, rewrittenArg)) {
      continue;
    }
    std::vector<Kernel::TermList> args;
    args.reserve(original->arity());
    for (unsigned j = 0; j < original->arity(); ++j) {
      args.push_back(j == i ? rewrittenArg : *original->nthArgument(j));
    }
    result = Kernel::TermList(Kernel::Term::create(original->functor(), original->arity(), args.data()));
    substitution = childSubstitution;
    return true;
  }
  return false;
}

bool MegalodonChecker::appendEqualityRewriteStep(
  const Hypothesis& hypothesis,
  const std::vector<unsigned>& variables,
  Kernel::TermList lhs,
  Kernel::TermList rhs,
  bool forward,
  const std::map<unsigned, Kernel::TermList>& substitution,
  unsigned& nextLabel,
  std::vector<std::string>& lines)
{
  Kernel::TermList instantiatedLhs;
  Kernel::TermList instantiatedRhs;
  if (!substituteTerm(lhs, substitution, instantiatedLhs) || !substituteTerm(rhs, substitution, instantiatedRhs)) {
    return false;
  }

  std::string lhsText;
  std::string rhsText;
  if (!termToMegalodon(instantiatedLhs, lhsText) || !termToMegalodon(instantiatedRhs, rhsText)) {
    return false;
  }

  std::ostringstream proof;
  proof << hypothesis.proof;
  for (unsigned variable : variables) {
    auto found = substitution.find(variable);
    if (found == substitution.end()) {
      return false;
    }
    std::string arg;
    if (!termToMegalodon(found->second, arg)) {
      return false;
    }
    proof << ' ' << parenthesize(arg);
  }

  std::string label = "L" + std::to_string(nextLabel++);
  lines.push_back("claim " + label + ": " + lhsText + " = " + rhsText + ".");
  lines.push_back("{ exact " + parenthesize(proof.str()) + ". }");
  lines.push_back(std::string("rewrite ") + (forward ? "" : "<- ") + label + ".");
  return true;
}

void MegalodonChecker::implicationChain(Kernel::Formula* formula, std::vector<Kernel::Formula*>& premises, Kernel::Formula*& conclusion) const
{
  while (formula->connective() == Kernel::IMP) {
    premises.push_back(formula->left());
    formula = formula->right();
  }
  conclusion = formula;
}

bool MegalodonChecker::premiseProofTerm(
  Kernel::Formula* premise,
  std::map<unsigned, Kernel::TermList>& substitution,
  const std::vector<unsigned>& variables,
  const std::vector<Hypothesis>& hypotheses,
  std::string& result,
  unsigned depth)
{
  if (++_proofSearchCalls > 20000) {
    return false;
  }
  std::string premiseText;
  if (formulaToMegalodon(premise, substitution, premiseText)) {
    for (const Hypothesis& hypothesis : hypotheses) {
      if (hypothesis.proposition == premiseText) {
        result = hypothesis.proof;
        return true;
      }
    }
  }

  for (const Hypothesis& hypothesis : hypotheses) {
    std::map<unsigned, Kernel::TermList> extended = substitution;
    if (matchFormula(premise, hypothesis.formula, std::map<unsigned, Kernel::TermList>(), variables, extended)) {
      substitution = extended;
      result = hypothesis.proof;
      return true;
    }
  }

  if (premise->connective() == Kernel::FORALL) {
    return false;
  }

  return instantiatedProofTerm(premise, substitution, hypotheses, result, depth);
}

bool MegalodonChecker::instantiatedProofTerm(
  Kernel::Formula* goal,
  const std::map<unsigned, Kernel::TermList>& substitution,
  const std::vector<Hypothesis>& hypotheses,
  std::string& result,
  unsigned depth)
{
  if (++_proofSearchCalls > 20000) {
    return false;
  }
  std::string goalText;
  if (!formulaToMegalodon(goal, substitution, goalText)) {
    return false;
  }
  for (const Hypothesis& hypothesis : hypotheses) {
    if (hypothesis.proposition == goalText) {
      result = hypothesis.proof;
      return true;
    }
  }
  if (goal->connective() == Kernel::FORALL) {
    std::string inner;
    if (!instantiatedProofTerm(goal->qarg(), substitution, hypotheses, inner, depth)) {
      return false;
    }
    std::vector<std::pair<unsigned, Kernel::TermList>> vars;
    Kernel::VSList::Iterator vit(goal->vars());
    while (vit.hasNext()) {
      vars.push_back(vit.next());
    }
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
      std::string sort;
      if (!sortToMegalodon(it->second, sort)) {
        return false;
      }
      inner = "fun " + variableName(it->first) + ":" + sort + " => " + inner;
    }
    result = parenthesize(inner);
    return true;
  }
  if (goal->connective() == Kernel::IMP) {
    std::string lhs;
    if (!formulaToMegalodon(goal->left(), substitution, lhs)) {
      return false;
    }
    std::string hypName = "Hinst" + std::to_string(depth);
    std::vector<Hypothesis> extended = hypotheses;
    extended.push_back({lhs, hypName, goal->left()});
    std::string rhs;
    if (!instantiatedProofTerm(goal->right(), substitution, extended, rhs, depth)) {
      return false;
    }
    std::string lhsAnnotation = lhs;
    if (goal->left()->connective() != Kernel::BOOL_TERM && goal->left()->connective() != Kernel::LITERAL) {
      lhsAnnotation = parenthesize(lhsAnnotation);
    }
    result = parenthesize("fun " + hypName + ":" + lhsAnnotation + " => " + rhs);
    return true;
  }
  if (depth == 0) {
    return false;
  }

  for (const Hypothesis& hypothesis : hypotheses) {
    Kernel::Formula* body = hypothesis.formula;
    std::vector<unsigned> variables;
    while (body->connective() == Kernel::FORALL) {
      Kernel::VSList::Iterator vit(body->vars());
      while (vit.hasNext()) {
        variables.push_back(vit.next().first);
      }
      body = body->qarg();
    }
    if (variables.empty() || body->connective() != Kernel::IMP) {
      if (variables.empty()) {
        continue;
      }
      std::map<unsigned, Kernel::TermList> directSubstitution;
      if (!matchFormula(body, goal, substitution, variables, directSubstitution)) {
        continue;
      }
      std::ostringstream proof;
      proof << hypothesis.proof;
      bool complete = true;
      for (unsigned variable : variables) {
        auto found = directSubstitution.find(variable);
        if (found == directSubstitution.end()) {
          complete = false;
          break;
        }
        std::string arg;
        if (!termToMegalodon(found->second, arg)) {
          complete = false;
          break;
        }
        proof << ' ' << parenthesize(arg);
      }
      if (!complete) {
        continue;
      }
      result = parenthesize(proof.str());
      return true;
    }

    std::vector<Kernel::Formula*> premises;
    Kernel::Formula* conclusion = nullptr;
    implicationChain(body, premises, conclusion);
    if (conclusion == nullptr) {
      continue;
    }

    std::map<unsigned, Kernel::TermList> applicationSubstitution;
    if (!matchFormula(conclusion, goal, substitution, variables, applicationSubstitution)) {
      continue;
    }

    std::vector<std::string> premiseProofs;
    bool premisesComplete = true;
    for (Kernel::Formula* premise : premises) {
      std::string premiseProof;
      if (!premiseProofTerm(premise, applicationSubstitution, variables, hypotheses, premiseProof, depth - 1)) {
        premisesComplete = false;
        break;
      }
      premiseProofs.push_back(premiseProof);
    }
    if (!premisesComplete) {
      continue;
    }

    std::ostringstream proof;
    proof << hypothesis.proof;
    bool complete = true;
    for (unsigned variable : variables) {
      auto found = applicationSubstitution.find(variable);
      if (found == applicationSubstitution.end()) {
        complete = false;
        break;
      }
      std::string arg;
      if (!termToMegalodon(found->second, arg)) {
        complete = false;
        break;
      }
      proof << ' ' << parenthesize(arg);
    }
    if (!complete) {
      continue;
    }
    for (const std::string& premiseProof : premiseProofs) {
      proof << ' ' << parenthesize(premiseProof);
    }
    result = parenthesize(proof.str());
    return true;
  }
  return false;
}

bool MegalodonChecker::equalityRewriteProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result)
{
  for (const Hypothesis& equalityHypothesis : hypotheses) {
    Kernel::Formula* equalityBody = equalityHypothesis.formula;
    std::vector<unsigned> variables;
    while (equalityBody->connective() == Kernel::FORALL) {
      Kernel::VSList::Iterator vit(equalityBody->vars());
      while (vit.hasNext()) {
        variables.push_back(vit.next().first);
      }
      equalityBody = equalityBody->qarg();
    }

    Kernel::TermList lhs;
    Kernel::TermList rhs;
    if (!equalityLiteral(equalityBody, lhs, rhs)) {
      continue;
    }

    auto equalityProof = [&](const std::map<unsigned, Kernel::TermList>& substitution, std::string& proof) {
      std::ostringstream out;
      out << equalityHypothesis.proof;
      for (unsigned variable : variables) {
        auto found = substitution.find(variable);
        if (found == substitution.end()) {
          return false;
        }
        std::string arg;
        if (!termToMegalodon(found->second, arg)) {
          return false;
        }
        out << ' ' << parenthesize(arg);
      }
      proof = parenthesize(out.str());
      return true;
    };

    for (const Hypothesis& sourceHypothesis : hypotheses) {
      std::map<unsigned, Kernel::TermList> forwardSubstitution;
      if (formulaMatchesAfterPatternReplacement(sourceHypothesis.formula, goal, lhs, rhs, variables, forwardSubstitution)) {
        Kernel::TermList instantiatedLhs;
        if (!substituteTerm(lhs, forwardSubstitution, instantiatedLhs)) {
          continue;
        }
        std::string predicateBody;
        if (!formulaToMegalodonReplacing(sourceHypothesis.formula, instantiatedLhs, "Zeq", predicateBody)) {
          continue;
        }
        std::string proof;
        if (!equalityProof(forwardSubstitution, proof)) {
          continue;
        }
        result = parenthesize(
          proof + " "
          + parenthesize("fun Zeq:set => " + predicateBody) + " "
          + parenthesize(sourceHypothesis.proof)
        );
        return true;
      }

      std::map<unsigned, Kernel::TermList> reverseSubstitution;
      if (!formulaMatchesAfterPatternReplacement(sourceHypothesis.formula, goal, rhs, lhs, variables, reverseSubstitution)) {
        continue;
      }

      Kernel::TermList instantiatedLhs;
      Kernel::TermList instantiatedRhs;
      if (!substituteTerm(lhs, reverseSubstitution, instantiatedLhs) || !substituteTerm(rhs, reverseSubstitution, instantiatedRhs)) {
        continue;
      }

      std::string lhsText;
      if (!termToMegalodon(instantiatedLhs, lhsText)) {
        continue;
      }

      std::string predicateBody;
      if (!formulaToMegalodonReplacing(sourceHypothesis.formula, instantiatedRhs, "Zeq", predicateBody)) {
        continue;
      }

      std::string proof;
      if (!equalityProof(reverseSubstitution, proof)) {
        continue;
      }
      std::string lhsArgument = parenthesize(lhsText);
      std::string symmetryProof = parenthesize(
        proof + " "
        + parenthesize("fun Zsym:set => Zsym = " + lhsArgument) + " "
        + parenthesize("fun Q:set->prop => fun H:Q " + lhsArgument + " => H")
      );
      result = parenthesize(
        symmetryProof + " "
        + parenthesize("fun Zeq:set => " + predicateBody) + " "
        + parenthesize(sourceHypothesis.proof)
      );
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::equalitySimplificationProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp)
{
  auto termSize = [&](auto&& self, Kernel::TermList term) -> unsigned {
    if (term.isVar()) {
      return 1;
    }
    if (term.isApplication()) {
      return 1 + self(self, term.lhs()) + self(self, term.rhs());
    }
    if (!term.isTerm()) {
      return 1;
    }
    unsigned result = 1;
    Kernel::Term* t = term.term();
    for (unsigned i = 0; i < t->numTermArguments(); ++i) {
      result += self(self, t->termArg(i));
    }
    return result;
  };
  auto termOccurrences = [&](auto&& self, Kernel::TermList term, Kernel::TermList needle) -> unsigned {
    unsigned result = term == needle ? 1 : 0;
    if (term.isApplication()) {
      return result + self(self, term.lhs(), needle) + self(self, term.rhs(), needle);
    }
    if (!term.isTerm() || term.term()->isSpecial()) {
      return result;
    }
    Kernel::Term* t = term.term();
    for (unsigned i = 0; i < t->numTermArguments(); ++i) {
      result += self(self, t->termArg(i), needle);
    }
    return result;
  };
  auto formulaOccurrences = [&](auto&& self, Kernel::Formula* formula, Kernel::TermList needle) -> unsigned {
    switch (formula->connective()) {
      case Kernel::BOOL_TERM:
        return termOccurrences(termOccurrences, formula->getBooleanTerm(), needle);
      case Kernel::LITERAL: {
        unsigned result = 0;
        Kernel::Literal* literal = formula->literal();
        for (unsigned i = 0; i < literal->arity(); ++i) {
          result += termOccurrences(termOccurrences, *literal->nthArgument(i), needle);
        }
        return result;
      }
      case Kernel::NOT:
        return self(self, formula->uarg(), needle);
      case Kernel::AND:
      case Kernel::OR:
      case Kernel::IMP:
      case Kernel::IFF:
      case Kernel::XOR:
        return self(self, formula->left(), needle) + self(self, formula->right(), needle);
      case Kernel::FORALL:
      case Kernel::EXISTS:
        return self(self, formula->qarg(), needle);
      default:
        return 0U;
    }
  };

  for (const Hypothesis& equalityHypothesis : hypotheses) {
    Kernel::Formula* equalityBody = equalityHypothesis.formula;
    std::vector<unsigned> variables;
    while (equalityBody->connective() == Kernel::FORALL) {
      Kernel::VSList::Iterator vit(equalityBody->vars());
      while (vit.hasNext()) {
        variables.push_back(vit.next().first);
      }
      equalityBody = equalityBody->qarg();
    }

    Kernel::TermList lhs;
    Kernel::TermList rhs;
    if (!equalityLiteral(equalityBody, lhs, rhs)) {
      continue;
    }

    unsigned lhsSize = termSize(termSize, lhs);
    unsigned rhsSize = termSize(termSize, rhs);
    if (lhsSize == rhsSize) {
      continue;
    }

    Kernel::TermList pattern = lhsSize > rhsSize ? lhs : rhs;
    Kernel::TermList replacement = lhsSize > rhsSize ? rhs : lhs;
    bool equalityForward = lhsSize < rhsSize;

    std::map<unsigned, Kernel::TermList> substitution;
    Kernel::Formula* simplifiedGoal = nullptr;
    if (!rewriteFormulaOnce(goal, pattern, replacement, variables, substitution, simplifiedGoal)) {
      continue;
    }

    Kernel::TermList instantiatedLhs;
    Kernel::TermList instantiatedRhs;
    if (!substituteTerm(lhs, substitution, instantiatedLhs) || !substituteTerm(rhs, substitution, instantiatedRhs)) {
      continue;
    }

    Kernel::TermList premiseTerm = equalityForward ? instantiatedLhs : instantiatedRhs;
    if (formulaOccurrences(formulaOccurrences, simplifiedGoal, premiseTerm) != 1) {
      continue;
    }
    std::string predicateBody;
    if (!formulaToMegalodonReplacing(simplifiedGoal, premiseTerm, "Zeq", predicateBody)) {
      continue;
    }

    std::string sourceProof;
    if (!proofTerm(simplifiedGoal, hypotheses, sourceProof, nextHyp)) {
      continue;
    }

    std::ostringstream equalityProof;
    equalityProof << equalityHypothesis.proof;
    bool complete = true;
    for (unsigned variable : variables) {
      auto found = substitution.find(variable);
      if (found == substitution.end()) {
        complete = false;
        break;
      }
      std::string arg;
      if (!termToMegalodon(found->second, arg)) {
        complete = false;
        break;
      }
      equalityProof << ' ' << parenthesize(arg);
    }
    if (!complete) {
      continue;
    }

    std::string transportProof = parenthesize(equalityProof.str());
    if (!equalityForward) {
      std::string lhsText;
      if (!termToMegalodon(instantiatedLhs, lhsText)) {
        continue;
      }
      std::string lhsArgument = parenthesize(lhsText);
      transportProof = parenthesize(
        transportProof + " "
        + parenthesize("fun Zsym:set => Zsym = " + lhsArgument) + " "
        + parenthesize("fun Q:set->prop => fun H:Q " + lhsArgument + " => H")
      );
    }

    result = parenthesize(
      transportProof + " "
      + parenthesize("fun Zeq:set => " + predicateBody) + " "
      + parenthesize(sourceProof)
    );
    return true;
  }
  return false;
}

bool MegalodonChecker::equalityRewriteScript(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::vector<std::string>& lines)
{
  for (const Hypothesis& equalityHypothesis : hypotheses) {
    Kernel::TermList lhs;
    Kernel::TermList rhs;
    if (!equalityLiteral(equalityHypothesis.formula, lhs, rhs)) {
      continue;
    }

    std::string equalityText;
    if (!formulaToMegalodon(equalityHypothesis.formula, equalityText)) {
      continue;
    }

    for (const Hypothesis& sourceHypothesis : hypotheses) {
      bool forwardReplaced = false;
      if (formulaMatchesAfterReplacement(sourceHypothesis.formula, goal, lhs, rhs, forwardReplaced) && forwardReplaced) {
        lines.push_back("claim L0: " + equalityText + ".");
        lines.push_back("{ exact " + equalityHypothesis.proof + ". }");
        lines.push_back("rewrite <- L0.");
        lines.push_back("exact " + sourceHypothesis.proof + ".");
        return true;
      }

      bool backwardReplaced = false;
      if (formulaMatchesAfterReplacement(sourceHypothesis.formula, goal, rhs, lhs, backwardReplaced) && backwardReplaced) {
        lines.push_back("claim L0: " + equalityText + ".");
        lines.push_back("{ exact " + equalityHypothesis.proof + ". }");
        lines.push_back("rewrite L0.");
        lines.push_back("exact " + sourceHypothesis.proof + ".");
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::equalityNormalizationScript(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::vector<std::string>& lines)
{
  Kernel::TermList goalLhs;
  Kernel::TermList goalRhs;
  if (!equalityLiteral(goal, goalLhs, goalRhs)) {
    return false;
  }

  struct EqualityRule {
    const Hypothesis* hypothesis;
    std::vector<unsigned> variables;
    Kernel::TermList lhs;
    Kernel::TermList rhs;
    bool forward;
  };

  std::vector<EqualityRule> rules;
  auto termSize = [&](auto&& self, Kernel::TermList term) -> unsigned {
    if (term.isVar()) {
      return 1;
    }
    if (term.isApplication()) {
      return 1 + self(self, term.lhs()) + self(self, term.rhs());
    }
    if (!term.isTerm()) {
      return 1;
    }
    unsigned result = 1;
    Kernel::Term* t = term.term();
    for (unsigned i = 0; i < t->numTermArguments(); ++i) {
      result += self(self, t->termArg(i));
    }
    return result;
  };
  for (const Hypothesis& hypothesis : hypotheses) {
    Kernel::Formula* body = hypothesis.formula;
    std::vector<unsigned> variables;
    while (body->connective() == Kernel::FORALL) {
      Kernel::VSList::Iterator vit(body->vars());
      while (vit.hasNext()) {
        variables.push_back(vit.next().first);
      }
      body = body->qarg();
    }
    Kernel::TermList lhs;
    Kernel::TermList rhs;
    if (!equalityLiteral(body, lhs, rhs)) {
      continue;
    }
    unsigned lhsSize = termSize(termSize, lhs);
    unsigned rhsSize = termSize(termSize, rhs);
    if (rhsSize < lhsSize) {
      rules.push_back({&hypothesis, variables, lhs, rhs, true});
    } else if (lhsSize < rhsSize) {
      rules.push_back({&hypothesis, variables, rhs, lhs, false});
    }
  }
  if (rules.empty()) {
    return false;
  }

  std::vector<std::string> script;
  unsigned nextLabel = 0;
  constexpr unsigned maxStepsPerSide = 8;
  auto normalize = [&](Kernel::TermList& term) {
    for (unsigned step = 0; step < maxStepsPerSide; ++step) {
      bool changed = false;
      for (const EqualityRule& rule : rules) {
        std::map<unsigned, Kernel::TermList> substitution;
        Kernel::TermList rewritten;
        if (!rewriteTermOnce(term, rule.lhs, rule.rhs, rule.variables, substitution, rewritten)) {
          continue;
        }
        if (rewritten == term) {
          continue;
        }
        if (!appendEqualityRewriteStep(*rule.hypothesis, rule.variables, rule.forward ? rule.lhs : rule.rhs, rule.forward ? rule.rhs : rule.lhs, rule.forward, substitution, nextLabel, script)) {
          return false;
        }
        term = rewritten;
        changed = true;
        break;
      }
      if (!changed) {
        return true;
      }
    }
    return false;
  };

  Kernel::TermList normalizedLhs = goalLhs;
  Kernel::TermList normalizedRhs = goalRhs;
  if (!normalize(normalizedLhs) || !normalize(normalizedRhs) || normalizedLhs != normalizedRhs || script.empty()) {
    return false;
  }

  std::string normalizedText;
  if (!termToMegalodon(normalizedLhs, normalizedText)) {
    return false;
  }
  script.push_back("exact " + parenthesize("fun Q:set->prop => fun H:Q " + parenthesize(normalizedText) + " => H") + ".");
  lines.insert(lines.end(), script.begin(), script.end());
  return true;
}

bool MegalodonChecker::hypothesisApplicationProofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result)
{
  if (++_proofSearchCalls > 20000) {
    return false;
  }
  for (const Hypothesis& hypothesis : hypotheses) {
    Kernel::Formula* body = hypothesis.formula;
    std::vector<unsigned> variables;
    while (body->connective() == Kernel::FORALL) {
      Kernel::VSList::Iterator vit(body->vars());
      while (vit.hasNext()) {
        variables.push_back(vit.next().first);
      }
      body = body->qarg();
    }
    if (variables.empty()) {
      continue;
    }

    std::vector<Kernel::Formula*> premises;
    Kernel::Formula* conclusion = nullptr;
    implicationChain(body, premises, conclusion);
    if (conclusion == nullptr) {
      continue;
    }

    std::map<unsigned, Kernel::TermList> substitution;
    if (!matchFormula(conclusion, goal, variables, substitution)) {
      continue;
    }

    std::vector<std::string> premiseProofs;
    bool premisesComplete = true;
    for (Kernel::Formula* premise : premises) {
      std::string premiseProof;
      if (!premiseProofTerm(premise, substitution, variables, hypotheses, premiseProof, 4)) {
        premisesComplete = false;
        break;
      }
      premiseProofs.push_back(premiseProof);
    }
    if (!premisesComplete) {
      continue;
    }

    std::ostringstream proof;
    proof << hypothesis.proof;
    bool complete = true;
    for (unsigned variable : variables) {
      auto found = substitution.find(variable);
      if (found == substitution.end()) {
        complete = false;
        break;
      }
      std::string arg;
      if (!termToMegalodon(found->second, arg)) {
        complete = false;
        break;
      }
      proof << ' ' << parenthesize(arg);
    }
    if (!complete) {
      continue;
    }
    for (const std::string& premiseProof : premiseProofs) {
      proof << ' ' << parenthesize(premiseProof);
    }
    result = parenthesize(proof.str());
    return true;
  }
  return false;
}

bool MegalodonChecker::conjunctionIntroductionProofTerm(
  Kernel::Formula* goal,
  const std::vector<Hypothesis>& hypotheses,
  std::string& result,
  unsigned& nextHyp)
{
  if (goal->connective() != Kernel::AND) {
    return false;
  }
  std::vector<Kernel::Formula*> conjuncts;
  auto args = goal->args()->iter();
  while (args.hasNext()) {
    conjuncts.push_back(args.next());
  }
  return conjunctionIntroductionProofTerm(conjuncts, 0, hypotheses, result, nextHyp);
}

bool MegalodonChecker::conjunctionIntroductionProofTerm(
  const std::vector<Kernel::Formula*>& conjuncts,
  std::size_t begin,
  const std::vector<Hypothesis>& hypotheses,
  std::string& result,
  unsigned& nextHyp)
{
  if (begin + 1 >= conjuncts.size()) {
    return false;
  }

  std::string lhsText;
  std::string rhsText;
  if (!formulaToMegalodon(conjuncts[begin], lhsText)
    || !conjunctionToMegalodon(conjuncts, begin + 1, std::map<unsigned, Kernel::TermList>(), rhsText)) {
    return false;
  }

  std::string lhsProof;
  if (!proofTerm(conjuncts[begin], hypotheses, lhsProof, nextHyp)) {
    return false;
  }

  std::string rhsProof;
  if (begin + 2 == conjuncts.size()) {
    if (!proofTerm(conjuncts[begin + 1], hypotheses, rhsProof, nextHyp)) {
      return false;
    }
  } else if (!conjunctionIntroductionProofTerm(conjuncts, begin + 1, hypotheses, rhsProof, nextHyp)) {
    return false;
  }

  result = parenthesize(
    "fun P:prop => fun H:" + parenthesize(lhsText) + " -> " + parenthesize(rhsText) + " -> P => "
    + "H " + parenthesize(lhsProof) + " " + parenthesize(rhsProof)
  );
  return true;
}

bool MegalodonChecker::conjunctionProjectionProofTerm(Kernel::Formula* source, const std::string& sourceProof, Kernel::Formula* goal, std::string& result)
{
  if (source->connective() != Kernel::AND) {
    return false;
  }

  std::string goalText;
  if (!formulaToMegalodon(goal, goalText)) {
    return false;
  }

  std::vector<Kernel::Formula*> conjuncts;
  auto args = source->args()->iter();
  while (args.hasNext()) {
    conjuncts.push_back(args.next());
  }
  return conjunctionProjectionProofTerm(conjuncts, 0, sourceProof, goalText, result);
}

bool MegalodonChecker::conjunctionProjectionProofTerm(
  const std::vector<Kernel::Formula*>& conjuncts,
  std::size_t begin,
  const std::string& sourceProof,
  const std::string& goalText,
  std::string& result)
{
  if (begin + 1 >= conjuncts.size()) {
    return false;
  }

  std::string lhsText;
  std::string rhsText;
  if (!formulaToMegalodon(conjuncts[begin], lhsText)
    || !conjunctionToMegalodon(conjuncts, begin + 1, std::map<unsigned, Kernel::TermList>(), rhsText)) {
    return false;
  }

  if (lhsText == goalText) {
    result = parenthesize(
      sourceProof + " " + parenthesize(goalText) + " "
      + parenthesize("fun Hleft:" + parenthesize(lhsText) + " => fun Hright:" + parenthesize(rhsText) + " => Hleft")
    );
    return true;
  }

  std::string rhsProjection = parenthesize(
    sourceProof + " " + parenthesize(rhsText) + " "
    + parenthesize("fun Hleft:" + parenthesize(lhsText) + " => fun Hright:" + parenthesize(rhsText) + " => Hright")
  );
  if (rhsText == goalText) {
    result = rhsProjection;
    return true;
  }
  return conjunctionProjectionProofTerm(conjuncts, begin + 1, rhsProjection, goalText, result);
}

bool MegalodonChecker::proofTerm(Kernel::Formula* goal, const std::vector<Hypothesis>& hypotheses, std::string& result, unsigned& nextHyp)
{
  if (++_proofSearchCalls > 20000) {
    return false;
  }
  std::string goalText;
  if (!formulaToMegalodon(goal, goalText)) {
    return false;
  }

  for (const Hypothesis& hypothesis : hypotheses) {
    if (hypothesis.proposition == goalText) {
      result = hypothesis.proof;
      return true;
    }
  }

  for (const Hypothesis& hypothesis : hypotheses) {
    if (conjunctionProjectionProofTerm(hypothesis.formula, hypothesis.proof, goal, result)) {
      return true;
    }
  }

  if (equalityProofTerm(goal, hypotheses, result)) {
    return true;
  }

  if (equalityRewriteProofTerm(goal, hypotheses, result)) {
    return true;
  }

  if (equalitySimplificationProofTerm(goal, hypotheses, result, nextHyp)) {
    return true;
  }

  if (hypothesisApplicationProofTerm(goal, hypotheses, result)) {
    return true;
  }

  for (const Hypothesis& hypothesis : hypotheses) {
    std::string binderName;
    Kernel::Formula* body = nullptr;
    if (quantifiedPropHypothesis(hypothesis.formula, binderName, body)) {
      result = parenthesize(hypothesis.proof + " " + parenthesize(goalText));
      return true;
    }
  }

  if (conjunctionIntroductionProofTerm(goal, hypotheses, result, nextHyp)) {
    return true;
  }

  if (goal->connective() == Kernel::FORALL) {
    std::string inner;
    if (!proofTerm(goal->qarg(), hypotheses, inner, nextHyp)) {
      return false;
    }
    std::vector<std::pair<unsigned, Kernel::TermList>> vars;
    Kernel::VSList::Iterator vit(goal->vars());
    while (vit.hasNext()) {
      vars.push_back(vit.next());
    }
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
      std::string sort;
      if (!sortToMegalodon(it->second, sort)) {
        return false;
      }
      inner = "fun " + variableName(it->first) + ":" + sort + " => " + inner;
    }
    result = parenthesize(inner);
    return true;
  }

  if (goal->connective() == Kernel::IMP) {
    std::string lhs;
    if (!formulaToMegalodon(goal->left(), lhs)) {
      return false;
    }
    std::string lhsAnnotation = lhs;
    if (goal->left()->connective() != Kernel::BOOL_TERM && goal->left()->connective() != Kernel::LITERAL) {
      lhsAnnotation = parenthesize(lhsAnnotation);
    }
    std::string hypName = "H" + std::to_string(nextHyp++);
    std::vector<Hypothesis> extended = hypotheses;
    extended.push_back({lhs, hypName, goal->left()});
    std::string rhs;
    if (!proofTerm(goal->right(), extended, rhs, nextHyp)) {
      return false;
    }
    result = parenthesize("fun " + hypName + ":" + lhsAnnotation + " => " + rhs);
    return true;
  }

  return false;
}

bool MegalodonChecker::tryMegalodonSource(Kernel::Formula* formula, const std::vector<Hypothesis>& assumptions, std::vector<std::string>& lines)
{
  _functions.clear();
  _predicates.clear();
  _usedSymbolNames.clear();
  _usesEquality = false;
  _equalitySort.clear();
  _usesConjunction = false;
  _usesFalse = false;
  _usesDisjunction = false;
  _usesSetExists = false;
  _usesTrue = false;
  _usesPropEquality = false;

  std::vector<std::string> assumptionLines;
  std::vector<Hypothesis> hypotheses;
  for (const Hypothesis& assumption : assumptions) {
    std::string proposition;
    if (!formulaToMegalodon(assumption.formula, proposition)) {
      continue;
    }
    std::string name = "ax" + std::to_string(hypotheses.size());
    assumptionLines.push_back("Axiom " + name + ":" + proposition + ".");
    hypotheses.push_back({proposition, name, assumption.formula});
  }

  std::string theorem;
  if (!formulaToMegalodon(formula, theorem)) {
    return false;
  }

  unsigned nextHyp = 0;
  std::string proof;
  std::vector<std::string> proofLines;
  _proofSearchCalls = 0;
  if (!equalityRewriteScript(formula, hypotheses, proofLines)
    && !equalityNormalizationScript(formula, hypotheses, proofLines)
    && proofTerm(formula, hypotheses, proof, nextHyp)) {
    proofLines.push_back("exact " + parenthesize(proof) + ".");
  }
  if (proofLines.empty()) {
    return false;
  }

  if (_usesEquality) {
    lines.push_back(equalityDefinition());
  }
  if (_usesPropEquality) {
    lines.push_back(propEqualityDefinition());
  }
  if (_usesConjunction) {
    lines.push_back("Definition vampire_and : prop->prop->prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.");
  }
  if (_usesTrue) {
    lines.push_back("Definition vampire_true : prop := forall P:prop, P -> P.");
  }
  if (_usesSetExists) {
    lines.push_back("Variable vampire_exists_set:(set->prop)->prop.");
  }
  for (const auto& entry : _functions) {
    std::string decl = functionDeclaration(entry.first, entry.second);
    if (decl.empty()) {
      return false;
    }
    lines.push_back(decl);
  }
  for (const auto& entry : _predicates) {
    std::string decl = predicateDeclaration(entry.first, entry.second);
    if (decl.empty()) {
      return false;
    }
    lines.push_back(decl);
  }
  for (const std::string& line : assumptionLines) {
    lines.push_back(line);
  }
  lines.push_back("Theorem vampire_reconstructed: " + theorem + ".");
  for (const std::string& line : proofLines) {
    lines.push_back(line);
  }
  return true;
}

bool MegalodonChecker::tryMegalodonClaimSkeleton(Kernel::Formula* formula, const std::vector<Hypothesis>& assumptions, std::vector<std::string>& lines)
{
  _functions.clear();
  _predicates.clear();
  _usedSymbolNames.clear();
  _usesEquality = false;
  _equalitySort.clear();
  _usesConjunction = false;
  _usesFalse = false;
  _usesDisjunction = false;
  _usesSetExists = false;
  _usesTrue = false;

  auto symbolsDeclarable = [&]() {
    for (const auto& entry : _functions) {
      if (functionDeclaration(entry.first, entry.second).empty()) {
        return false;
      }
    }
    for (const auto& entry : _predicates) {
      if (predicateDeclaration(entry.first, entry.second).empty()) {
        return false;
      }
    }
    return true;
  };

  std::string theorem;
  if (!formulaToMegalodon(formula, theorem) || !symbolsDeclarable()) {
    return false;
  }

  std::vector<std::string> assumptionLines;
  unsigned renderedAssumption = 0;
  for (std::size_t i = 0; i < assumptions.size(); ++i) {
    auto functionsSnapshot = _functions;
    auto predicatesSnapshot = _predicates;
    auto usedSymbolNamesSnapshot = _usedSymbolNames;
    bool usesEqualitySnapshot = _usesEquality;
    std::string equalitySortSnapshot = _equalitySort;
    bool usesConjunctionSnapshot = _usesConjunction;
    bool usesFalseSnapshot = _usesFalse;
    bool usesDisjunctionSnapshot = _usesDisjunction;
    bool usesSetExistsSnapshot = _usesSetExists;
    bool usesTrueSnapshot = _usesTrue;
    bool usesPropEqualitySnapshot = _usesPropEquality;

    std::string proposition;
    if (!formulaToMegalodon(assumptions[i].formula, proposition) || !symbolsDeclarable()) {
      _functions = functionsSnapshot;
      _predicates = predicatesSnapshot;
      _usedSymbolNames = usedSymbolNamesSnapshot;
      _usesEquality = usesEqualitySnapshot;
      _equalitySort = equalitySortSnapshot;
      _usesConjunction = usesConjunctionSnapshot;
      _usesFalse = usesFalseSnapshot;
      _usesDisjunction = usesDisjunctionSnapshot;
      _usesSetExists = usesSetExistsSnapshot;
      _usesTrue = usesTrueSnapshot;
      _usesPropEquality = usesPropEqualitySnapshot;
      continue;
    }
    assumptionLines.push_back("Axiom ax" + std::to_string(renderedAssumption++) + ":" + proposition + ".");
  }

  std::vector<std::string> claimLines;
  for (Kernel::Unit* unit : proof) {
    auto functionsSnapshot = _functions;
    auto predicatesSnapshot = _predicates;
    auto usedSymbolNamesSnapshot = _usedSymbolNames;
    bool usesEqualitySnapshot = _usesEquality;
    std::string equalitySortSnapshot = _equalitySort;
    bool usesConjunctionSnapshot = _usesConjunction;
    bool usesFalseSnapshot = _usesFalse;
    bool usesDisjunctionSnapshot = _usesDisjunction;
    bool usesSetExistsSnapshot = _usesSetExists;
    bool usesTrueSnapshot = _usesTrue;
    bool usesPropEqualitySnapshot = _usesPropEquality;

    std::string proposition;
    bool rendered = false;
    if (unit->isClause()) {
      rendered = skeletonClauseToMegalodon(unit->asClause(), proposition);
    } else {
      Kernel::Formula* stepFormula = static_cast<Kernel::FormulaUnit*>(unit)->formula();
      if (unit->inference().rule() == Kernel::InferenceRule::NEGATED_CONJECTURE && stepFormula->connective() == Kernel::NOT) {
        stepFormula = stepFormula->uarg();
      }
      rendered = formulaToMegalodon(stepFormula, proposition);
    }
    if (!rendered || !symbolsDeclarable()) {
      _functions = functionsSnapshot;
      _predicates = predicatesSnapshot;
      _usedSymbolNames = usedSymbolNamesSnapshot;
      _usesEquality = usesEqualitySnapshot;
      _equalitySort = equalitySortSnapshot;
      _usesConjunction = usesConjunctionSnapshot;
      _usesFalse = usesFalseSnapshot;
      _usesDisjunction = usesDisjunctionSnapshot;
      _usesSetExists = usesSetExistsSnapshot;
      _usesTrue = usesTrueSnapshot;
      _usesPropEquality = usesPropEqualitySnapshot;
      continue;
    }
    std::string name = "S" + std::to_string(unit->number());
    claimLines.push_back("claim " + name + ": " + proposition + ".");
    claimLines.push_back("{ admit. }");
  }

  if (_usesFalse) {
    lines.push_back("Definition vampire_false : prop := forall P:prop, P.");
  }
  if (_usesDisjunction) {
    lines.push_back("Definition vampire_or : prop->prop->prop := fun A B:prop => forall P:prop, (A -> P) -> (B -> P) -> P.");
  }
  if (_usesEquality) {
    lines.push_back(equalityDefinition());
  }
  if (_usesPropEquality) {
    lines.push_back(propEqualityDefinition());
  }
  if (_usesConjunction) {
    lines.push_back("Definition vampire_and : prop->prop->prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.");
  }
  if (_usesTrue) {
    lines.push_back("Definition vampire_true : prop := forall P:prop, P -> P.");
  }
  if (_usesSetExists) {
    lines.push_back("Variable vampire_exists_set:(set->prop)->prop.");
  }
  for (const auto& entry : _functions) {
    std::string decl = functionDeclaration(entry.first, entry.second);
    if (decl.empty()) {
      return false;
    }
    lines.push_back(decl);
  }
  for (const auto& entry : _predicates) {
    std::string decl = predicateDeclaration(entry.first, entry.second);
    if (decl.empty()) {
      return false;
    }
    lines.push_back(decl);
  }
  for (const std::string& line : assumptionLines) {
    lines.push_back(line);
  }
  lines.push_back("Theorem vampire_reconstruction_skeleton: " + theorem + ".");
  for (const std::string& line : claimLines) {
    lines.push_back(line);
  }
  lines.push_back("admit.");
  lines.push_back("Qed.");
  return true;
}

void MegalodonChecker::printMegalodonSourceCandidate()
{
  std::vector<Hypothesis> assumptions;
  for (Kernel::Unit* unit : proof) {
    if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::INPUT) {
      continue;
    }
    if (unit->inputType() != Kernel::UnitInputType::AXIOM && unit->inputType() != Kernel::UnitInputType::ASSUMPTION) {
      continue;
    }
    Kernel::Formula* formula = static_cast<Kernel::FormulaUnit*>(unit)->formula();
    assumptions.push_back({"", "", formula});
  }

  for (Kernel::Unit* unit : proof) {
    if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::NEGATED_CONJECTURE) {
      continue;
    }
    Kernel::Formula* formula = static_cast<Kernel::FormulaUnit*>(unit)->formula();
    if (formula->connective() == Kernel::NOT) {
      formula = formula->uarg();
    }
    std::vector<std::string> lines;
    if (!tryMegalodonSource(formula, assumptions, lines)) {
      continue;
    }
    out << "megalodon_source_candidate_start.\n";
    for (const std::string& line : lines) {
      out << "megalodon_source_line(" << quote(line) << ").\n";
    }
    out << "megalodon_source_candidate_end.\n";
    return;
  }
}

void MegalodonChecker::printMegalodonClaimSkeleton()
{
  std::vector<Hypothesis> assumptions;
  for (Kernel::Unit* unit : proof) {
    if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::INPUT) {
      continue;
    }
    if (unit->inputType() != Kernel::UnitInputType::AXIOM && unit->inputType() != Kernel::UnitInputType::ASSUMPTION) {
      continue;
    }
    Kernel::Formula* formula = static_cast<Kernel::FormulaUnit*>(unit)->formula();
    assumptions.push_back({"", "", formula});
  }

  for (Kernel::Unit* unit : proof) {
    if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::NEGATED_CONJECTURE) {
      continue;
    }
    Kernel::Formula* formula = static_cast<Kernel::FormulaUnit*>(unit)->formula();
    if (formula->connective() == Kernel::NOT) {
      formula = formula->uarg();
    }
    std::vector<std::string> lines;
    if (!tryMegalodonClaimSkeleton(formula, assumptions, lines)) {
      continue;
    }
    out << "megalodon_claim_skeleton_start.\n";
    for (const std::string& line : lines) {
      out << "megalodon_source_line(" << quote(line) << ").\n";
    }
    out << "megalodon_claim_skeleton_end.\n";
    return;
  }
}

void MegalodonChecker::print()
{
  out << "% Megalodon proof reconstruction output generated by Vampire\n";
  out << "% format: vampire-megalodon-proof-outline-v1\n";
  out << "megalodon_reconstruction_start.\n";
  out << "megalodon_reconstruction_version(1).\n";
  AbstractProofPrinter::print();
  printMegalodonSymbolDeclarations();
  printMegalodonSourceCandidate();
  printMegalodonClaimSkeleton();
  out << "megalodon_final_step(" << (*proof.rbegin())->number() << ").\n";
  out << "megalodon_reconstruction_end.\n";
}

void MegalodonChecker::recordStepSymbols(Kernel::Unit* u)
{
  std::string ignored;
  if (u->isClause()) {
    skeletonClauseToMegalodon(u->asClause(), ignored);
    return;
  }
  Kernel::Formula* stepFormula = static_cast<Kernel::FormulaUnit*>(u)->formula();
  if (u->inference().rule() == Kernel::InferenceRule::NEGATED_CONJECTURE && stepFormula->connective() == Kernel::NOT) {
    stepFormula = stepFormula->uarg();
  }
  formulaToMegalodon(stepFormula, ignored);
}

void MegalodonChecker::printMegalodonSymbolDeclarations()
{
  for (const auto& entry : _functions) {
    std::string decl = functionDeclaration(entry.first, entry.second);
    if (!decl.empty()) {
      out << "megalodon_symbol_declaration(" << quote(decl) << ").\n";
    }
  }
  for (const auto& entry : _predicates) {
    std::string decl = predicateDeclaration(entry.first, entry.second);
    if (!decl.empty()) {
      out << "megalodon_symbol_declaration(" << quote(decl) << ").\n";
    }
  }
}

void MegalodonChecker::printStepVariableSorts(Kernel::Unit* u)
{
  Lib::DHMap<unsigned, Kernel::TermList> varSorts;
  Kernel::SortHelper::collectVariableSorts(u, varSorts);
  std::vector<std::pair<unsigned, std::string>> rendered;
  Lib::DHMap<unsigned, Kernel::TermList>::Iterator it(varSorts);
  while (it.hasNext()) {
    unsigned var;
    Kernel::TermList sort;
    it.next(var, sort);
    std::string sortText;
    if (sortToMegalodon(sort, sortText)) {
      rendered.push_back({var, variableName(var) + ":" + sortText});
    }
  }
  if (rendered.empty()) {
    return;
  }
  std::sort(rendered.begin(), rendered.end(), [](const auto& left, const auto& right) {
    return left.first < right.first;
  });
  out << "megalodon_step_variable_sorts(" << u->number() << ",[";
  for (std::size_t i = 0; i < rendered.size(); ++i) {
    if (i != 0) {
      out << ',';
    }
    out << quote(rendered[i].second);
  }
  out << "]).\n";
}

void MegalodonChecker::printStep(Kernel::Unit* u)
{
  recordStepSymbols(u);
  const Kernel::InferenceRule& rule = u->inference().rule();
  bool replayed = false;
  unsigned substitutions = 0;
  const InferenceRecorder::InferenceInformation* replayInfo = nullptr;
  if (inferenceNeedsReplayInformation(rule)) {
    if (u->isClause()) {
      InferenceRecorder::instance()->setCurrentGoal(u->asClause());
    }
    _replayer.replayInference(u);
    if (rule == Kernel::InferenceRule::RECTIFY) {
      replayed = InferenceRecorder::instance()->getGenericLastInferenceInformation() != nullptr;
    } else {
      replayInfo = InferenceRecorder::instance()->getLastRecordedInferenceInformation();
      replayed = replayInfo != nullptr;
      if (replayInfo != nullptr) {
        substitutions = replayInfo->substitutionForBanksSub.size();
      }
    }
  }
  bool hasNontrivialReplaySubstitution = false;
  if (replayInfo != nullptr) {
    for (std::size_t premiseIndex = 0;
         premiseIndex < replayInfo->premises.size()
           && premiseIndex < replayInfo->substitutionForBanksSub.size();
         ++premiseIndex) {
      std::set<unsigned> premiseVariables;
      for (Kernel::Literal* literal : replayInfo->premises[premiseIndex]->iterLits()) {
        Kernel::TermVarIterator variables(literal);
        while (variables.hasNext()) {
          premiseVariables.insert(variables.next());
        }
      }
      const auto& substitution = replayInfo->substitutionForBanksSub[premiseIndex];
      Kernel::Substitution substitutionCopy = substitution;
      for (auto [var, term] : iterTraits(substitutionCopy.items())) {
        if (premiseVariables.find(var) == premiseVariables.end()) {
          continue;
        }
        if (!term.isVar() || term.var() != var) {
          hasNontrivialReplaySubstitution = true;
          break;
        }
      }
      if (hasNontrivialReplaySubstitution) {
        break;
      }
    }
  }

  std::string propositionText;
  bool hasProposition = false;
  if (u->isClause()) {
    hasProposition = skeletonClauseToMegalodon(u->asClause(), propositionText);
  } else {
    bool renderingReplayExtra = _renderingReplayExtra;
    _renderingReplayExtra = true;
    hasProposition = formulaToMegalodon(u->getFormula(), propositionText);
    _renderingReplayExtra = renderingReplayExtra;
  }
  std::string formulaText = u->isClause()
    ? "cnf(u" + std::to_string(u->number()) + ",plain,$true).\n"
    : "tff(u" + std::to_string(u->number()) + ",plain,$true).\n";

  out << "megalodon_step("
      << u->number() << ','
      << quote(Kernel::ruleName(rule)) << ','
      << quote(unitKind(u)) << ','
      << parents(u) << ','
      << (replayed ? "true" : "false") << ','
      << substitutions << ','
      << quote(formulaText)
      << ").\n";
  if (hasProposition) {
    out << "megalodon_step_proposition("
        << u->number() << ','
        << quote(propositionText)
        << ").\n";
  } else if (!u->isClause()) {
    Kernel::Formula* formula = u->getFormula();
    out << "megalodon_step_extra("
        << u->number() << ','
        << quote("proposition") << ",["
        << quote("conversion_failed=1") << ','
        << quote("connective=" + std::to_string(static_cast<int>(formula->connective()))) << ','
        << quote("raw=" + formula->toString())
        << "]).\n";
  }
  if (u->isClause()) {
    std::string certificateClause;
    if (certificateClauseJson(u->asClause(), certificateClause)) {
      out << "megalodon_certificate_clause("
          << u->number() << ','
          << certificateClause
          << ").\n";
    } else {
      out << "megalodon_step_extra("
          << u->number() << ','
          << quote("certificate_clause") << ",["
          << quote("conversion_failed=1")
          << "]).\n";
    }
    std::string certificateStep;
    if (certificateDefinitionInputStepJson(u, certificateStep)) {
      out << "megalodon_certificate_step("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (hasNontrivialReplaySubstitution
      && certificateSubstitutedResolutionStepsJson(u, replayInfo, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if ((rule == Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
        || rule == Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION)
      && certificateSubstitutedResolutionStepsJson(u, replayInfo, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if ((rule == Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
        || rule == Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION)
      && certificateSatSubsumptionResolutionStepsJson(u, certificateStep)) {
      if (!certificateStep.empty() && certificateStep.front() == '[') {
        out << "megalodon_certificate_steps("
            << u->number() << ','
            << certificateStep
            << ").\n";
      } else {
        out << "megalodon_certificate_step("
            << u->number() << ','
            << certificateStep
            << ").\n";
      }
    } else if (certificateResolveStepJson(u, certificateStep)) {
      out << "megalodon_certificate_step("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateUnitResultingResolutionStepsJson(u, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateSubstitutedResolutionStepsJson(u, replayInfo, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateSatSubsumptionResolutionStepsJson(u, certificateStep)) {
      if (!certificateStep.empty() && certificateStep.front() == '[') {
        out << "megalodon_certificate_steps("
            << u->number() << ','
            << certificateStep
            << ").\n";
      } else {
        out << "megalodon_certificate_step("
            << u->number() << ','
            << certificateStep
            << ").\n";
      }
    } else if (certificateEqualityResolutionStepJson(u, replayInfo, certificateStep)) {
      if (!certificateStep.empty() && certificateStep.front() == '[') {
        out << "megalodon_certificate_steps("
            << u->number() << ','
            << certificateStep
            << ").\n";
      } else {
        out << "megalodon_certificate_step("
            << u->number() << ','
            << certificateStep
            << ").\n";
      }
    } else if (certificateFactorStepJson(u, certificateStep)) {
      out << "megalodon_certificate_step("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateEqualityFactoringStepJson(u, replayInfo, certificateStep)) {
      if (!certificateStep.empty() && certificateStep.front() == '[') {
        out << "megalodon_certificate_steps("
            << u->number() << ','
            << certificateStep
            << ").\n";
      } else {
        out << "megalodon_certificate_step("
            << u->number() << ','
            << certificateStep
            << ").\n";
      }
    } else if (certificateDemodulationStepsJson(u, replayInfo, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateParamodulateStepJson(u, certificateStep)) {
      out << "megalodon_certificate_step("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateParamodulateThenSymmetryStepsJson(u, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    } else if (certificateSuperpositionStepsJson(u, replayInfo, certificateStep)) {
      out << "megalodon_certificate_steps("
          << u->number() << ','
          << certificateStep
          << ").\n";
    }
  }
  out << "megalodon_step_replay_kind("
      << u->number() << ','
      << quote(replayKind(rule))
      << ").\n";
  printStepVariableSorts(u);
  if (replayed) {
    printReplaySubstitutions(u, replayInfo);
  }
  printReplayExtra(u, replayInfo);
}

} // namespace Shell
