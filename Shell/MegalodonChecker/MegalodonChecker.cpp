#include "MegalodonChecker.hpp"

#include "Forwards.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Kernel/HOL/HOL.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/SortHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Options.hpp"
#include "Shell/TPTPPrinter.hpp"

#include <algorithm>
#include <set>
#include <sstream>
#include <utility>

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
    case Kernel::InferenceRule::FACTORING:
    case Kernel::InferenceRule::EQUALITY_RESOLUTION:
    case Kernel::InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION:
    case Kernel::InferenceRule::EQUALITY_FACTORING:
    case Kernel::InferenceRule::SUPERPOSITION:
    case Kernel::InferenceRule::FORWARD_DEMODULATION:
    case Kernel::InferenceRule::BACKWARD_DEMODULATION:
    case Kernel::InferenceRule::RECTIFY:
      return true;
    default:
      return false;
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

std::string MegalodonChecker::functionName(unsigned functor)
{
  auto found = _functions.find(functor);
  if (found != _functions.end()) {
    return found->second;
  }
  std::string name = "f" + std::to_string(_functions.size());
  _functions.emplace(functor, name);
  return name;
}

std::string MegalodonChecker::predicateName(unsigned predicate)
{
  auto found = _predicates.find(predicate);
  if (found != _predicates.end()) {
    return found->second;
  }
  std::string name = "p" + std::to_string(_predicates.size());
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

bool MegalodonChecker::termToMegalodon(Kernel::TermList term, std::string& result)
{
  std::map<unsigned, Kernel::TermList> substitution;
  return termToMegalodon(term, substitution, result);
}

bool MegalodonChecker::termToMegalodon(Kernel::TermList term, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result)
{
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
      if (it->isApplication()) {
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
    if (!termToMegalodon(t->termArg(i), substitution, arg)) {
      return false;
    }
    if (t->termArg(i).isTerm() && t->termArg(i).term()->numTermArguments() > 0) {
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
      if (it->isApplication()) {
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
    if (t->termArg(i).isTerm() && t->termArg(i).term()->numTermArguments() > 0) {
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
        return false;
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
    std::string equalitySort;
    if (!sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort) || equalitySort != "set") {
      return false;
    }
    _usesEquality = true;
    std::string lhs;
    std::string rhs;
    if (!termToMegalodon(*literal->nthArgument(0), substitution, lhs) || !termToMegalodon(*literal->nthArgument(1), substitution, rhs)) {
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

bool MegalodonChecker::formulaToMegalodon(Kernel::Formula* formula, const std::map<unsigned, Kernel::TermList>& substitution, std::string& result)
{
  switch (formula->connective()) {
    case Kernel::LITERAL: {
      Kernel::Literal* literal = formula->literal();
      if (literal->isNegative()) {
        return false;
      }
      if (literal->isEquality()) {
        std::string equalitySort;
        if (!sortToMegalodon(Kernel::SortHelper::getEqualityArgumentSort(literal), equalitySort) || equalitySort != "set") {
          return false;
        }
        _usesEquality = true;
        std::string lhs;
        std::string rhs;
        if (!termToMegalodon(*literal->nthArgument(0), substitution, lhs) || !termToMegalodon(*literal->nthArgument(1), substitution, rhs)) {
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
      return termToMegalodon(formula->getBooleanTerm(), substitution, result);
    case Kernel::IMP: {
      std::string lhs;
      std::string rhs;
      if (!formulaToMegalodon(formula->left(), substitution, lhs) || !formulaToMegalodon(formula->right(), substitution, rhs)) {
        return false;
      }
      if (formula->left()->connective() == Kernel::IMP || formula->left()->connective() == Kernel::FORALL) {
        lhs = parenthesize(lhs);
      }
      result = lhs + " -> " + rhs;
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
  _usesEquality = false;
  _usesConjunction = false;

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
  if (!equalityRewriteScript(formula, hypotheses, proofLines)
    && !equalityNormalizationScript(formula, hypotheses, proofLines)
    && proofTerm(formula, hypotheses, proof, nextHyp)) {
    proofLines.push_back("exact " + parenthesize(proof) + ".");
  }
  if (proofLines.empty()) {
    return false;
  }

  if (_usesEquality) {
    lines.push_back("Definition vampire_eq : set->set->prop := fun x y:set => forall Q:set->prop, Q x -> Q y.");
    lines.push_back("Infix = 502 := vampire_eq.");
  }
  if (_usesConjunction) {
    lines.push_back("Definition vampire_and : prop->prop->prop := fun A B:prop => forall P:prop, (A -> B -> P) -> P.");
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

void MegalodonChecker::print()
{
  out << "% Megalodon proof reconstruction output generated by Vampire\n";
  out << "% format: vampire-megalodon-proof-outline-v1\n";
  out << "megalodon_reconstruction_start.\n";
  out << "megalodon_reconstruction_version(1).\n";
  AbstractProofPrinter::print();
  printMegalodonSourceCandidate();
  out << "megalodon_final_step(" << (*proof.rbegin())->number() << ").\n";
  out << "megalodon_reconstruction_end.\n";
}

void MegalodonChecker::printStep(Kernel::Unit* u)
{
  const Kernel::InferenceRule& rule = u->inference().rule();
  bool replayed = false;
  unsigned substitutions = 0;
  if (inferenceNeedsReplayInformation(rule)) {
    if (u->isClause()) {
      InferenceRecorder::instance()->setCurrentGoal(u->asClause());
    }
    _replayer.replayInference(u);
    if (rule == Kernel::InferenceRule::RECTIFY) {
      replayed = InferenceRecorder::instance()->getGenericLastInferenceInformation() != nullptr;
    } else {
      const InferenceRecorder::InferenceInformation* info =
        InferenceRecorder::instance()->getLastRecordedInferenceInformation();
      replayed = info != nullptr;
      if (info != nullptr) {
        substitutions = info->substitutionForBanksSub.size();
      }
    }
  }

  out << "megalodon_step("
      << u->number() << ','
      << quote(Kernel::ruleName(rule)) << ','
      << quote(unitKind(u)) << ','
      << parents(u) << ','
      << (replayed ? "true" : "false") << ','
      << substitutions << ','
      << quote(TPTPPrinter::toString(u))
      << ").\n";
}

} // namespace Shell
