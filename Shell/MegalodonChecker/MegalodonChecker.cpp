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
#include "Parse/TPTP.hpp"
#include "Lib/DHMap.hpp"
#include "Lib/Environment.hpp"
#include "Lib/Exception.hpp"
#include "Lib/SharedSet.hpp"
#include "SAT/SATInference.hpp"
#include "SATSubsumption/SATSubsumptionAndResolution.hpp"
#include "Saturation/Splitter.hpp"
#include "Shell/InferenceRecorder.hpp"
#include "Shell/Options.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelSyntax.hpp"
#include "Shell/TPTPPrinter.hpp"
#include "Shell/TweeGoalTransformation.hpp"

#include <algorithm>
#include <cctype>
#include <cstdlib>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <utility>
#include <vector>

namespace Shell {

namespace {

bool emitLegacyMegalodonJsonDiagnostics()
{
  return std::getenv("VAMPIRE_MEGALODON_LEGACY_JSON") != nullptr;
}

}

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
    case Kernel::InferenceRule::RECTIFY:
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
    case Kernel::InferenceRule::CONDENSATION:
      return "condensation";
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

std::string MegalodonChecker::sexprQuote(const std::string& value) const
{
  return quote(value);
}

bool MegalodonChecker::certificateTypeSexpr(Kernel::TermList sort, std::string& result)
{
  if (sort.isArrowSort()) {
    std::string domain;
    std::string range;
    if (!certificateTypeSexpr(sort.domain(), domain) || !certificateTypeSexpr(sort.result(), range)) {
      return false;
    }
    result = "(AR " + domain + " " + range + ")";
    return true;
  }
  std::string rendered;
  if (!sortToMegalodon(sort, rendered)) {
    return false;
  }
  if (rendered == "prop") {
    result = "(PROP)";
    return true;
  }
  if (rendered == "set") {
    result = "(SET)";
    return true;
  }
  return false;
}

bool MegalodonChecker::certificateTermSexpr(Kernel::TermList term, std::string& result)
{
  if (term.isVar()) {
    result = "(TMH " + sexprQuote(variableName(term.var())) + ")";
    return true;
  }
  if (term.isApplication()) {
    std::string lhs;
    std::string rhs;
    if (!certificateTermSexpr(term.lhs(), lhs) || !certificateTermSexpr(term.rhs(), rhs)) {
      return false;
    }
    result = "(AP " + lhs + " " + rhs + ")";
    return true;
  }
  if (term.isTerm() && term.term()->isSpecial()) {
    Kernel::Term* special = term.term();
    switch (special->specialFunctor()) {
    case Kernel::SpecialFunctor::FORMULA:
      return certificateFormulaTermSexpr(special->getSpecialData()->getFormula(), result);
    case Kernel::SpecialFunctor::LAMBDA: {
      const Kernel::Term::SpecialTermData* data = special->getSpecialData();
      Kernel::TermList lambdaBody = data->getLambdaExp();
      std::string body;
      if (lambdaBody.isTerm() && lambdaBody.term()->isFormula()) {
        if (!certificateFormulaTermSexpr(lambdaBody.term()->getSpecialData()->getFormula(), body)) {
          return false;
        }
      } else if (!certificateTermSexpr(lambdaBody, body)) {
        return false;
      }

      std::vector<std::pair<unsigned, Kernel::TermList>> vars;
      Kernel::VSList::Iterator vit(data->getLambdaVars());
      while (vit.hasNext()) {
        vars.push_back(vit.next());
      }
      for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
        std::string type;
        if (!certificateTypeSexpr(it->second, type)) {
          return false;
        }
        body = "(VLAMV " + sexprQuote(variableName(it->first)) + " " + type + " " + body + ")";
      }
      result = body;
      return true;
    }
    default:
      return false;
    }
  }
  if (!term.isTerm() || term.term()->isSpecial()) {
    return false;
  }

  Kernel::Term* t = term.term();
  std::string rendered = "(TMH " + sexprQuote(functionName(t->functor())) + ")";
  for (unsigned i = 0; i < t->numTermArguments(); ++i) {
    std::string arg;
    if (!certificateTermSexpr(t->termArg(i), arg)) {
      return false;
    }
    rendered = "(AP " + rendered + " " + arg + ")";
  }
  result = rendered;
  return true;
}

bool MegalodonChecker::certificateEqualityAtomSexpr(
  Kernel::TermList sort,
  const std::string& lhs,
  const std::string& rhs,
  std::string& result)
{
  static const std::string megalodonEqualityHash =
    "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
  std::string type;
  if (!certificateTypeSexpr(sort, type)) {
    return false;
  }
  result = "(AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") "
    + type + ") " + lhs + ") " + rhs + ")";
  return true;
}

bool MegalodonChecker::certificateAtomSexpr(Kernel::Literal* literal, std::string& result)
{
  Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
  if (positive->isEquality()) {
    std::string lhs;
    std::string rhs;
    if (!certificateTermSexpr(*positive->nthArgument(0), lhs)
      || !certificateTermSexpr(*positive->nthArgument(1), rhs)) {
      return false;
    }
    return certificateEqualityAtomSexpr(
      Kernel::SortHelper::getEqualityArgumentSort(positive), lhs, rhs, result);
  }

  std::string rendered = "(TMH " + sexprQuote(predicateName(positive->functor())) + ")";
  for (unsigned i = 0; i < positive->arity(); ++i) {
    std::string arg;
    if (!certificateTermSexpr(*positive->nthArgument(i), arg)) {
      return false;
    }
    rendered = "(AP " + rendered + " " + arg + ")";
  }
  result = rendered;
  return true;
}

bool MegalodonChecker::certificateLiteralSexpr(Kernel::Literal* literal, std::string& result)
{
  std::string atom;
  if (!certificateAtomSexpr(literal, atom)) {
    return false;
  }
  result = std::string("(") + (literal->isPositive() ? "pos " : "neg ") + atom + ")";
  return true;
}

bool MegalodonChecker::certificateSplitLiteralSexpr(unsigned split, std::string& result)
{
  std::string rawName = Saturation::Splitter::getFormulaStringFromName(split, true);
  bool negative = false;
  if (!rawName.empty() && rawName[0] == '~') {
    negative = true;
    rawName = rawName.substr(1);
  } else if (rawName.rfind("¬", 0) == 0) {
    negative = true;
    rawName = rawName.substr(2);
  }
  result = std::string("(")
    + (negative ? "neg " : "pos ")
    + "(TMH " + sexprQuote(sanitizeMegalodonName(rawName, "split")) + "))";
  return true;
}

bool MegalodonChecker::appendCertificateSplitLiteralsSexpr(Kernel::Clause* clause, std::vector<std::string>& literals)
{
  if (!clause->splits() || clause->splits()->isEmpty()) {
    return true;
  }
  for (unsigned split : iterTraits(clause->splits()->iter())) {
    std::string rendered;
    if (!certificateSplitLiteralSexpr(split, rendered)) {
      return false;
    }
    literals.push_back(rendered);
  }
  return true;
}

bool MegalodonChecker::appendCertificateClauseLiteralsSexpr(Kernel::Clause* clause, std::vector<std::string>& literals)
{
  for (unsigned i = 0; i < clause->length(); ++i) {
    Kernel::Literal* literal = (*clause)[i];
    std::string rendered;
    if (!certificateLiteralSexpr(literal, rendered)) {
      return false;
    }
    literals.push_back(rendered);
  }
  return appendCertificateSplitLiteralsSexpr(clause, literals);
}

bool MegalodonChecker::certificateClauseSexpr(Kernel::Clause* clause, std::string& result)
{
  std::vector<std::string> literals;
  if (!appendCertificateClauseLiteralsSexpr(clause, literals)) {
    return false;
  }
  std::ostringstream out;
  out << "(clause";
  for (const std::string& literal : literals) {
    out << ' ' << literal;
  }
  out << ')';
  result = out.str();
  return true;
}

namespace {

std::set<unsigned> certificateClauseVariables(Kernel::Clause* clause)
{
  std::set<unsigned> variables;
  if (clause == nullptr) {
    return variables;
  }
  Lib::DHMap<unsigned, Kernel::TermList> varSorts;
  Kernel::SortHelper::collectVariableSorts(clause, varSorts);
  Lib::DHMap<unsigned, Kernel::TermList>::Iterator it(varSorts);
  while (it.hasNext()) {
    unsigned var;
    Kernel::TermList sort;
    it.next(var, sort);
    variables.insert(var);
  }
  return variables;
}

} // namespace

bool MegalodonChecker::certificateSubstitutionSexpr(const Kernel::Substitution& substitution, std::string& result)
{
  std::vector<std::pair<unsigned, std::string>> items;
  Kernel::Substitution substitutionCopy = substitution;
  for (auto [var, term] : iterTraits(substitutionCopy.items())) {
    if (term.isVar() && term.var() == var) {
      continue;
    }
    std::string termSexpr;
    if (!certificateTermSexpr(term, termSexpr)) {
      return false;
    }
    items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
  }
  std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
    return left.first < right.first;
  });
  std::ostringstream out;
  out << "(subst";
  for (const auto& item : items) {
    out << ' ' << item.second;
  }
  out << ')';
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateSubstitutionSexprForClause(
  const Kernel::Substitution& substitution,
  Kernel::Clause* parent,
  std::string& result)
{
  const std::set<unsigned> variables = certificateClauseVariables(parent);
  std::vector<std::pair<unsigned, std::string>> items;
  Kernel::Substitution substitutionCopy = substitution;
  for (auto [var, term] : iterTraits(substitutionCopy.items())) {
    if (variables.find(var) == variables.end()) {
      continue;
    }
    if (term.isVar() && term.var() == var) {
      continue;
    }
    std::string termSexpr;
    if (!certificateTermSexpr(term, termSexpr)) {
      return false;
    }
    items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
  }
  std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
    return left.first < right.first;
  });
  std::ostringstream out;
  out << "(subst";
  for (const auto& item : items) {
    out << ' ' << item.second;
  }
  out << ')';
  result = out.str();
  return true;
}

std::string MegalodonChecker::certificateClauseSexprFromRenderedLiterals(
  const std::vector<std::string>& literals) const
{
  std::ostringstream out;
  out << "(clause";
  for (const std::string& literal : literals) {
    out << ' ' << literal;
  }
  out << ')';
  return out.str();
}

bool MegalodonChecker::certificateInstantiationKernelMetadataSexpr(
  const std::string& id,
  const std::string& parentId,
  const std::vector<std::string>& parentLiterals,
  const std::string& substitution,
  const std::vector<std::string>& resultLiterals,
  std::string& result) const
{
  const std::string parentClause = certificateClauseSexprFromRenderedLiterals(parentLiterals);
  const std::string resultClause = certificateClauseSexprFromRenderedLiterals(resultLiterals);

  MegalodonKernelSyntax::MegalodonKernelStep step =
    MegalodonKernelSyntax::kernelStep(id, "instantiation");
  MegalodonKernelSyntax::addPrimitiveExpansion(
    step,
    MegalodonKernelSyntax::primitiveExpansion(id, "substitute"));
  std::vector<std::string> stepFields;
  stepFields.push_back("conclusion_unit=" + id);
  stepFields.push_back("result_clause=" + resultClause);
  stepFields.push_back("conclusion_clause=" + resultClause);
  stepFields.push_back("substitution=" + substitution);
  stepFields.push_back("result_literal_count=" + std::to_string(resultLiterals.size()));
  for (std::size_t i = 0; i < resultLiterals.size(); ++i) {
    stepFields.push_back("result_literal_" + std::to_string(i) + "=" + resultLiterals[i]);
  }
  stepFields.push_back("parent_count=1");
  stepFields.push_back("parent_0_unit=" + parentId);
  stepFields.push_back("parent_0_clause=" + parentClause);
  stepFields.push_back("parent_0_literal_count=" + std::to_string(parentLiterals.size()));
  for (std::size_t i = 0; i < parentLiterals.size(); ++i) {
    stepFields.push_back("parent_0_literal_" + std::to_string(i) + "=" + parentLiterals[i]);
  }
  stepFields.push_back("parent_0_substitution=" + substitution);
  stepFields.push_back("parent_0_substituted_literal_count=" + std::to_string(resultLiterals.size()));
  for (std::size_t i = 0; i < resultLiterals.size(); ++i) {
    stepFields.push_back("parent_0_substituted_literal_" + std::to_string(i) + "=" + resultLiterals[i]);
  }
  MegalodonKernelSyntax::addFields(step, stepFields);

  const std::vector<std::string> fields = MegalodonKernelSyntax::kernelStepFields(step);
  std::ostringstream out;
  out << "(step_extra " << sexprQuote(id) << " \"kernel_v1\" (";
  for (std::size_t i = 0; i < fields.size(); ++i) {
    if (i != 0) {
      out << ' ';
    }
    out << sexprQuote(fields[i]);
  }
  out << "))";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateSubstituteStepSexpr(
  const std::string& id,
  const std::string& parentId,
  Kernel::Clause* parent,
  const Kernel::Substitution& substitution,
  std::string& result)
{
  std::string step;
  std::vector<std::string> metadata;
  if (!certificateSubstituteStepPartsSexpr(id, parentId, parent, substitution, step, metadata)) {
    return false;
  }
  std::ostringstream out;
  out << step;
  for (const std::string& item : metadata) {
    out << "\n  " << item;
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateSubstituteStepPartsSexpr(
  const std::string& id,
  const std::string& parentId,
  Kernel::Clause* parent,
  const Kernel::Substitution& substitution,
  std::string& step,
  std::vector<std::string>& metadata)
{
  std::string substitutionSexpr;
  if (!certificateSubstitutionSexprForClause(substitution, parent, substitutionSexpr)) {
    return false;
  }

  std::vector<std::string> parentLiterals;
  if (!appendCertificateClauseLiteralsSexpr(parent, parentLiterals)) {
    return false;
  }

  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };

  std::vector<std::tuple<unsigned, std::string, std::string>> replacements;
  const std::set<unsigned> variables = certificateClauseVariables(parent);
  Kernel::Substitution substitutionCopy = substitution;
  for (auto [var, term] : iterTraits(substitutionCopy.items())) {
    if (variables.find(var) == variables.end()) {
      continue;
    }
    if (term.isVar() && term.var() == var) {
      continue;
    }
    std::string termSexpr;
    if (!certificateTermSexpr(term, termSexpr)) {
      return false;
    }
    replacements.push_back({var, "(TMH " + sexprQuote(variableName(var)) + ")", termSexpr});
  }
  std::sort(replacements.begin(), replacements.end(), [](const auto& left, const auto& right) {
    return std::get<0>(left) < std::get<0>(right);
  });

  std::vector<std::string> substitutedLiterals = parentLiterals;
  for (std::string& literal : substitutedLiterals) {
    for (std::size_t i = 0; i < replacements.size(); ++i) {
      replaceAll(literal, std::get<1>(replacements[i]), "(TMH " + sexprQuote("__mg_subst_" + std::to_string(i)) + ")");
    }
    for (std::size_t i = 0; i < replacements.size(); ++i) {
      replaceAll(literal, "(TMH " + sexprQuote("__mg_subst_" + std::to_string(i)) + ")", std::get<2>(replacements[i]));
    }
  }
  const std::string resultClause = certificateClauseSexprFromRenderedLiterals(substitutedLiterals);

  Lib::DHMap<unsigned, Kernel::TermList> resultVarSorts;
  for (Kernel::Literal* literal : parent->iterLits()) {
    Kernel::Literal* substituted = nullptr;
    if (!safeApplySubstitution(literal, substitution, substituted)) {
      return false;
    }
    Kernel::SortHelper::collectVariableSorts(substituted, resultVarSorts);
  }
  std::vector<std::pair<unsigned, std::string>> renderedResultVarSorts;
  Lib::DHMap<unsigned, Kernel::TermList>::Iterator resultVarSortIterator(resultVarSorts);
  while (resultVarSortIterator.hasNext()) {
    unsigned var;
    Kernel::TermList sort;
    resultVarSortIterator.next(var, sort);
    std::string sortText;
    if (sortToMegalodon(sort, sortText)) {
      renderedResultVarSorts.push_back({var, variableName(var) + ":" + sortText});
    }
  }
  std::sort(renderedResultVarSorts.begin(), renderedResultVarSorts.end(), [](const auto& left, const auto& right) {
    return left.first < right.first;
  });

  std::ostringstream stepOut;
  stepOut << "(substitute " << sexprQuote(id)
      << " (parent " << sexprQuote(parentId) << ") "
      << substitutionSexpr
      << " (result " << resultClause << "))";
  if (!renderedResultVarSorts.empty()) {
    std::ostringstream metadataOut;
    metadataOut << "(step_variable_sorts " << sexprQuote(id) << " (";
    for (std::size_t i = 0; i < renderedResultVarSorts.size(); ++i) {
      if (i != 0) {
        metadataOut << ' ';
      }
      metadataOut << sexprQuote(renderedResultVarSorts[i].second);
    }
    metadataOut << "))";
    metadata.push_back(metadataOut.str());
  }
  std::string kernelMetadata;
  if (!certificateInstantiationKernelMetadataSexpr(
        id,
        parentId,
        parentLiterals,
        substitutionSexpr,
        substitutedLiterals,
        kernelMetadata)) {
    return false;
  }
  metadata.push_back(kernelMetadata);
  step = stepOut.str();
  return true;
}

bool MegalodonChecker::certificateAvatarComponentStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::AVATAR_COMPONENT) {
    return false;
  }
  Kernel::Clause* clause = unit->asClause();
  if (clause->noSplits()) {
    return false;
  }
  std::string renderedClause;
  if (!certificateClauseSexpr(clause, renderedClause)) {
    return false;
  }
  result = "(avatar_component " + sexprQuote("u" + std::to_string(unit->number()))
    + " (result " + renderedClause + "))";
  return true;
}

bool MegalodonChecker::certificateAvatarSplitStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->inference().rule() != Kernel::InferenceRule::AVATAR_SPLIT_CLAUSE) {
    return false;
  }
  std::string renderedClause;
  if (unit->isClause()) {
    if (!certificateClauseSexpr(unit->asClause(), renderedClause)) {
      return false;
    }
  } else {
    std::string formula;
    if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), formula)) {
      return false;
    }
    renderedClause = "(clause (pos " + formula + "))";
  }
  if (renderedClause.empty()) {
    return false;
  }
  std::ostringstream out;
  out << "(avatar_split " << sexprQuote("u" + std::to_string(unit->number())) << " (parents";
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    out << ' ' << sexprQuote("u" + std::to_string(parent->number()));
  }
  out << ") (result " << renderedClause << "))";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateAvatarContradictionStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->inference().rule() != Kernel::InferenceRule::AVATAR_CONTRADICTION_CLAUSE) {
    return false;
  }
  std::string renderedClause;
  if (unit->isClause()) {
    if (!certificateClauseSexpr(unit->asClause(), renderedClause)) {
      return false;
    }
  } else {
    std::string formula;
    if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), formula)) {
      return false;
    }
    renderedClause = "(clause (pos " + formula + "))";
  }
  if (renderedClause.empty()) {
    return false;
  }
  std::ostringstream out;
  out << "(avatar_contradiction " << sexprQuote("u" + std::to_string(unit->number())) << " (parents";
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    out << ' ' << sexprQuote("u" + std::to_string(parent->number()));
  }
  out << ") (result " << renderedClause << "))";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateAvatarRefutationStepSexpr(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::AVATAR_REFUTATION
      && rule != Kernel::InferenceRule::AVATAR_REFUTATION_SMT
    )
    || unit->asClause()->length() != 0) {
    return false;
  }

  auto satClauseSexpr = [](SAT::SATClause* clause) {
    std::ostringstream out;
    out << "(sat_clause";
    for (SATLiteral literal : clause->iter()) {
      out << " (lit " << literal.var() << ' ' << (literal.positive() ? "true" : "false") << ')';
    }
    out << ')';
    return out.str();
  };

  auto satProofSexpr = [&](SAT::SATClause* root) {
    struct CompareSATClauses {
      bool operator()(SAT::SATClause* left, SAT::SATClause* right) const
      {
        return left->number < right->number;
      }
    };

    std::set<SAT::SATClause*, CompareSATClauses> proof;
    std::vector<SAT::SATClause*> todo;
    todo.push_back(root);
    while (!todo.empty()) {
      SAT::SATClause* current = todo.back();
      todo.pop_back();
      if (current == nullptr || !proof.insert(current).second) {
        continue;
      }
      SAT::SATInference* inference = current->inference();
      if (inference == nullptr || inference->getType() != SAT::SATInference::PROP_INF) {
        continue;
      }
      SAT::PropInference* prop = static_cast<SAT::PropInference*>(inference);
      for (SAT::SATClause* parent : iterTraits(prop->getPremises()->iter())) {
        todo.push_back(parent);
      }
    }

    std::ostringstream out;
    out << "(sat_proof";
    for (SAT::SATClause* clause : proof) {
      SAT::SATInference* inference = clause->inference();
      if (inference == nullptr) {
        return std::string();
      }
      switch (inference->getType()) {
        case SAT::SATInference::FO_CONVERSION:
          out << " (sat_input " << clause->number << ' ' << satClauseSexpr(clause) << ')';
          break;
        case SAT::SATInference::PROP_INF: {
          SAT::PropInference* prop = static_cast<SAT::PropInference*>(inference);
          out << " (sat_rup " << clause->number << " (parents";
          for (SAT::SATClause* parent : iterTraits(prop->getPremises()->iter())) {
            out << ' ' << parent->number;
          }
          out << ") (result " << satClauseSexpr(clause) << "))";
          break;
        }
      }
    }
    out << ')';
    return out.str();
  };

  auto satClauseAsSplitClauseSexpr = [&](SAT::SATClause* clause, std::string& rendered) {
    if (clause == nullptr) {
      return false;
    }
    std::ostringstream out;
    out << "(clause";
    for (SATLiteral literal : clause->iter()) {
      out << " (" << (literal.positive() ? "pos" : "neg")
          << " (TMH " << sexprQuote("split_" + std::to_string(literal.var())) << "))";
    }
    out << ')';
    rendered = out.str();
    return true;
  };

  auto syntheticAvatarOriginStepSexpr = [&](Kernel::Unit* origin, SAT::SATClause* clause, std::string& rendered) {
    std::string resultClause;
    if (origin == nullptr || !satClauseAsSplitClauseSexpr(clause, resultClause)) {
      return false;
    }
    std::ostringstream out;
    out << "(avatar_split " << sexprQuote("u" + std::to_string(origin->number())) << " (parents";
    for (Kernel::Unit* parent : iterTraits(origin->getParents())) {
      if (_certificateNativeStepIds.find(parent->number()) != _certificateNativeStepIds.end()) {
        out << ' ' << sexprQuote("u" + std::to_string(parent->number()));
      }
    }
    out << ") (result " << resultClause << "))";
    rendered = out.str();
    return true;
  };

  std::vector<std::string> satClauses;
  std::vector<std::string> parentIds;
  std::vector<std::string> originSteps;
  std::string satProof;
  if (SAT::SATClause* refutation = unit->inference().satPremise()) {
    satProof = satProofSexpr(refutation);
    SAT::SATInference::visitFOConversions(refutation, [&](SAT::SATClause* clause) {
      Kernel::Unit* origin = clause->inference()->foConversion()->getOrigin();
      if (origin == nullptr) {
        return;
      }
      parentIds.push_back("u" + std::to_string(origin->number()));
      satClauses.push_back(satClauseSexpr(clause));
      if (origin != nullptr
        && origin != unit
        && _certificateNativeStepIds.find(origin->number()) == _certificateNativeStepIds.end()) {
        std::string originStep;
        const Kernel::InferenceRule& originRule = origin->inference().rule();
        bool emitted =
          certificateAvatarSplitStepSexpr(origin, originStep)
          || certificateAvatarContradictionStepSexpr(origin, originStep);
        if (!emitted) {
          emitted = syntheticAvatarOriginStepSexpr(origin, clause, originStep);
        }
        if (!emitted
          && originRule != Kernel::InferenceRule::AVATAR_REFUTATION
          && originRule != Kernel::InferenceRule::AVATAR_REFUTATION_SMT) {
          emitted = certificateNativeStepSexpr(origin, nullptr, originStep);
        }
        if (emitted) {
          _certificateNativeStepIds.insert(origin->number());
          originSteps.push_back(originStep);
        }
      }
    });
  }

  if (satClauses.empty()) {
    for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
      const auto* extra = env.proofExtra.find(parent);
      if (extra == nullptr) {
        continue;
      }
      const auto* satExtra = static_cast<const Indexing::SATClauseExtra*>(extra);
      if (satExtra->clause == nullptr) {
        continue;
      }
      parentIds.push_back("u" + std::to_string(parent->number()));
      satClauses.push_back(satClauseSexpr(satExtra->clause));
    }
  }
  if (satClauses.empty()) {
    return false;
  }

  std::ostringstream out;
  for (const std::string& originStep : originSteps) {
    out << originStep << "\n  ";
  }
  out << "(avatar_refutation " << sexprQuote("u" + std::to_string(unit->number()));
  if (!parentIds.empty()) {
    out << " (parents";
    for (const std::string& parentId : parentIds) {
      out << ' ' << sexprQuote(parentId);
    }
    out << ')';
  }
  out << " (sat_clauses";
  for (const std::string& clause : satClauses) {
    out << ' ' << clause;
  }
  out << ')';
  if (!satProof.empty()) {
    out << ' ' << satProof;
  }
  out << " (result (clause)))";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateCondensationStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::CONDENSATION) {
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
  Kernel::Clause* child = unit->asClause();
  if (parent->length() <= child->length()) {
    return false;
  }

  auto substitutionSexpr = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termSexpr;
      if (!certificateTermSexpr(term, termSexpr)) {
        return false;
      }
      items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : items) {
      out << ' ' << item.second;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto substitutedAtomSexpr = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (positive->isEquality()) {
      std::string lhs;
      std::string rhs;
      Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(0), substitution);
      Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(1), substitution);
      if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
        return false;
      }
      Kernel::TermList sort =
        Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(positive), substitution);
      return certificateEqualityAtomSexpr(sort, lhs, rhs, rendered);
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
    return certificateAtomSexpr(substituted, rendered);
  };
  auto substitutedLiteralSexpr = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
    std::string atom;
    if (!substitutedAtomSexpr(literal, substitution, atom)) {
      return false;
    }
    rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ") + atom + ")";
    return true;
  };
  auto substitutedParentLiterals = [&](const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : parent->iterLits()) {
      std::string literalSexpr;
      if (!substitutedLiteralSexpr(literal, substitution, literalSexpr)) {
        return false;
      }
      literals.push_back(literalSexpr);
    }
    return appendCertificateSplitLiteralsSexpr(parent, literals);
  };
  auto normalizedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    if (!appendCertificateClauseLiteralsSexpr(clause, literals)) {
      return false;
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto literalMultiplicity =
    [](const std::vector<std::string>& literals, const std::string& literal) {
      return static_cast<unsigned>(std::count(literals.begin(), literals.end(), literal));
    };
  auto removeAt = [](const std::vector<std::string>& literals, unsigned index) {
    std::vector<std::string> result;
    result.reserve(literals.size() == 0 ? 0 : literals.size() - 1);
    for (unsigned i = 0; i < literals.size(); ++i) {
      if (i != index) {
        result.push_back(literals[i]);
      }
    }
    return result;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    const std::string typedPosPrefix =
      "(pos (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    const std::string typedNegPrefix =
      "(neg (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    std::string prefix;
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else if (literal.rfind(typedPosPrefix, 0) == 0 || literal.rfind(typedNegPrefix, 0) == 0) {
      const std::string typedPrefix =
        literal.rfind(typedPosPrefix, 0) == 0 ? typedPosPrefix : typedNegPrefix;
      std::size_t typeStart = typedPrefix.size();
      std::size_t typeEnd = std::string::npos;
      if (!termEnd(typeStart, typeEnd)
        || typeEnd + 2 >= literal.size()
        || literal[typeEnd] != ')'
        || literal[typeEnd + 1] != ' ') {
        return false;
      }
      prefix = literal.substr(0, typeEnd + 2);
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };

  auto matchTerm = [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, std::map<unsigned, Kernel::TermList>& bindings) -> bool {
    if (pattern.isVar()) {
      auto existing = bindings.find(pattern.var());
      if (existing == bindings.end()) {
        bindings.emplace(pattern.var(), target);
        return true;
      }
      return existing->second == target;
    }
    if (pattern.isApplication() || target.isApplication()) {
      return pattern.isApplication()
        && target.isApplication()
        && self(self, pattern.lhs(), target.lhs(), bindings)
        && self(self, pattern.rhs(), target.rhs(), bindings);
    }
    if (!pattern.isTerm() || !target.isTerm()) {
      return pattern == target;
    }
    Kernel::Term* patternTerm = pattern.term();
    Kernel::Term* targetTerm = target.term();
    if (patternTerm->functor() != targetTerm->functor()
      || patternTerm->arity() != targetTerm->arity()) {
      return false;
    }
    for (unsigned index = 0; index < patternTerm->arity(); ++index) {
      if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), bindings)) {
        return false;
      }
    }
    return true;
  };
  auto matchLiteralOriented = [&](Kernel::Literal* pattern, Kernel::Literal* target, bool reverseEquality, std::map<unsigned, Kernel::TermList>& bindings) {
    if (pattern->polarity() != target->polarity()
      || pattern->isEquality() != target->isEquality()) {
      return false;
    }
    if (pattern->isEquality()) {
      if (!matchTerm(matchTerm,
          Kernel::SortHelper::getEqualityArgumentSort(pattern),
          Kernel::SortHelper::getEqualityArgumentSort(target),
          bindings)) {
        return false;
      }
      Kernel::TermList targetLeft = *target->nthArgument(reverseEquality ? 1 : 0);
      Kernel::TermList targetRight = *target->nthArgument(reverseEquality ? 0 : 1);
      return matchTerm(matchTerm, *pattern->nthArgument(0), targetLeft, bindings)
        && matchTerm(matchTerm, *pattern->nthArgument(1), targetRight, bindings);
    }
    if (pattern->functor() != target->functor()
      || pattern->arity() != target->arity()) {
      return false;
    }
    for (unsigned index = 0; index < pattern->arity(); ++index) {
      if (!matchTerm(matchTerm, *pattern->nthArgument(index), *target->nthArgument(index), bindings)) {
        return false;
      }
    }
    return true;
  };
  auto matchLiteral = [&](Kernel::Literal* pattern, Kernel::Literal* target, std::map<unsigned, Kernel::TermList>& bindings) {
    std::map<unsigned, Kernel::TermList> trial = bindings;
    if (matchLiteralOriented(pattern, target, false, trial)) {
      bindings = std::move(trial);
      return true;
    }
    if (pattern->isEquality()) {
      trial = bindings;
      if (matchLiteralOriented(pattern, target, true, trial)) {
        bindings = std::move(trial);
        return true;
      }
    }
    return false;
  };

  std::vector<std::string> actual;
  if (!normalizedClause(child, actual)) {
    return false;
  }

  auto emitFromSubstitution = [&](const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::string> substitutedRaw;
    if (!substitutedParentLiterals(substitution, substitutedRaw)) {
      return false;
    }
    std::vector<std::string> substituted = substitutedRaw;
    std::sort(substituted.begin(), substituted.end());
    substituted.erase(std::unique(substituted.begin(), substituted.end()), substituted.end());

    std::string subst;
    if (!substitutionSexpr(substitution, subst)) {
      return false;
    }
    if (substituted == actual) {
      std::string renderedClause;
      if (!certificateClauseSexpr(child, renderedClause)) {
        return false;
      }
      rendered = "(condensation " + sexprQuote("u" + std::to_string(unit->number()))
        + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ") "
        + subst
        + " (result " + renderedClause + "))";
      return true;
    }

    std::vector<std::string> actualRaw;
    if (!appendCertificateClauseLiteralsSexpr(child, actualRaw)) {
      return false;
    }
    std::vector<std::string> steps;
    const std::string stepBase = "u" + std::to_string(unit->number());
    std::string currentParentId = stepBase + "_subst0";
    std::vector<std::string> current = substitutedRaw;
    std::string substituteStep;
    std::vector<std::string> substituteMetadata;
    if (!certificateSubstituteStepPartsSexpr(
          currentParentId,
          "u" + std::to_string(parent->number()),
          parent,
          substitution,
          substituteStep,
          substituteMetadata)) {
      return false;
    }
    steps.push_back(substituteStep);
    _certificateNativeMetadata.insert(
      _certificateNativeMetadata.end(),
      substituteMetadata.begin(),
      substituteMetadata.end());

    unsigned symmetryCount = 0;
    bool changed = true;
    while (changed) {
      changed = false;
      for (unsigned index = 0; index < current.size(); ++index) {
        if (literalMultiplicity(current, current[index]) <= literalMultiplicity(actualRaw, current[index])) {
          continue;
        }
        std::string swapped;
        if (!swappedEqualityLiteral(current[index], swapped)
          || literalMultiplicity(actualRaw, swapped) == 0) {
          continue;
        }
        std::vector<std::string> next = current;
        next[index] = swapped;
        const std::string symmetryId = stepBase + "_symmetry" + std::to_string(symmetryCount++);
        steps.push_back(
          "(equality_symmetry " + sexprQuote(symmetryId)
          + " (parent " + sexprQuote(currentParentId) + ")"
          + " (literal " + std::to_string(index) + ")"
          + " (result " + clauseSexprFromLiterals(next) + "))");
        current = next;
        currentParentId = symmetryId;
        changed = true;
        break;
      }
    }

    unsigned factorCount = 0;
    changed = true;
    while (changed) {
      changed = false;
      for (unsigned left = 0; left < current.size() && !changed; ++left) {
        for (unsigned right = left + 1; right < current.size(); ++right) {
          if (current[left] != current[right]) {
            continue;
          }
          if (literalMultiplicity(current, current[left]) <= literalMultiplicity(actualRaw, current[left])) {
            continue;
          }
          std::vector<std::string> next = removeAt(current, right);
          const std::string factorId = stepBase + "_factor" + std::to_string(factorCount++);
          steps.push_back(
            "(factor " + sexprQuote(factorId)
            + " (parent " + sexprQuote(currentParentId) + ")"
            + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
            + " (result " + clauseSexprFromLiterals(next) + "))");
          current = next;
          currentParentId = factorId;
          changed = true;
          break;
        }
      }
    }

    if (!sameMultiset(current, actualRaw)) {
      return false;
    }
    steps.push_back(
      "(substitute " + sexprQuote(stepBase)
      + " (parent " + sexprQuote(currentParentId) + ") (subst)"
      + " (result " + clauseSexprFromLiterals(actualRaw) + "))");
    std::ostringstream out;
    for (std::size_t i = 0; i < steps.size(); ++i) {
      if (i != 0) {
        out << "\n  ";
      }
      out << steps[i];
    }
    rendered = out.str();
    return true;
  };

  for (unsigned omitted = 0; omitted < parent->length(); ++omitted) {
    std::vector<Kernel::Literal*> baseLiterals;
    baseLiterals.reserve(parent->length() - 1);
    for (unsigned parentIndex = 0; parentIndex < parent->length(); ++parentIndex) {
      if (parentIndex != omitted) {
        baseLiterals.push_back((*parent)[parentIndex]);
      }
    }

    std::function<bool(std::size_t, std::map<unsigned, Kernel::TermList>&)> matchRest =
      [&](std::size_t baseIndex, std::map<unsigned, Kernel::TermList>& bindings) {
        if (baseIndex == baseLiterals.size()) {
          return true;
        }
        Kernel::Literal* pattern = baseLiterals[baseIndex];
        for (Kernel::Literal* target : child->iterLits()) {
          std::map<unsigned, Kernel::TermList> trial = bindings;
          if (!matchLiteral(pattern, target, trial)) {
            continue;
          }
          if (matchRest(baseIndex + 1, trial)) {
            bindings = std::move(trial);
            return true;
          }
        }
        return false;
      };

    std::map<unsigned, Kernel::TermList> bindings;
    if (!matchRest(0, bindings)) {
      continue;
    }

    Kernel::Substitution substitution;
    for (const auto& binding : bindings) {
      substitution.rebind(binding.first, binding.second);
    }

    if (emitFromSubstitution(substitution, result)) {
      return true;
    }
  }

  for (unsigned patternIndex = 0; patternIndex < parent->length(); ++patternIndex) {
    for (unsigned targetIndex = 0; targetIndex < parent->length(); ++targetIndex) {
      if (patternIndex == targetIndex) {
        continue;
      }
      for (bool reverseEquality : {false, true}) {
        std::map<unsigned, Kernel::TermList> bindings;
        if (!matchLiteralOriented((*parent)[patternIndex], (*parent)[targetIndex], reverseEquality, bindings)) {
          continue;
        }
        Kernel::Substitution substitution;
        for (const auto& binding : bindings) {
          substitution.rebind(binding.first, binding.second);
        }
        if (emitFromSubstitution(substitution, result)) {
          return true;
        }
      }
    }
  }

  return false;
}

bool MegalodonChecker::certificateRewriteTermAtMegalodonPosition(
  Kernel::TermList term,
  Kernel::TermList needle,
  Kernel::TermList replacement,
  std::vector<unsigned>& position,
  Kernel::TermList& rewritten)
{
  if (term.sameContent(needle)) {
    position.clear();
    rewritten = replacement;
    return true;
  }
  if (term.isVar()) {
    return false;
  }
  if (term.isApplication()) {
    std::vector<unsigned> childPosition;
    Kernel::TermList childRewritten;
    if (certificateRewriteTermAtMegalodonPosition(term.lhs(), needle, replacement, childPosition, childRewritten)) {
      position.clear();
      position.push_back(0);
      position.insert(position.end(), childPosition.begin(), childPosition.end());
      return safeHolApplication(HOL::lhsSort(term), childRewritten, term.rhs(), rewritten);
    }
    if (certificateRewriteTermAtMegalodonPosition(term.rhs(), needle, replacement, childPosition, childRewritten)) {
      position.clear();
      position.push_back(1);
      position.insert(position.end(), childPosition.begin(), childPosition.end());
      return safeHolApplication(HOL::lhsSort(term), term.lhs(), childRewritten, rewritten);
    }
    return false;
  }

  Kernel::Term* original = term.term();
  if (original->isSpecial() || original->numTermArguments() == 0) {
    return false;
  }
  std::vector<Kernel::TermList> args;
  args.reserve(original->arity());
  for (unsigned i = 0; i < original->arity(); ++i) {
    args.push_back(*original->nthArgument(i));
  }
  const unsigned termArgOffset = original->numTypeArguments();
  for (unsigned i = 0; i < original->numTermArguments(); ++i) {
    std::vector<unsigned> childPosition;
    Kernel::TermList childRewritten;
    if (!certificateRewriteTermAtMegalodonPosition(args[termArgOffset + i], needle, replacement, childPosition, childRewritten)) {
      continue;
    }
    args[termArgOffset + i] = childRewritten;
    position.clear();
    for (unsigned j = i + 1; j < original->numTermArguments(); ++j) {
      position.push_back(0);
    }
    position.push_back(1);
    position.insert(position.end(), childPosition.begin(), childPosition.end());
    rewritten = Kernel::TermList(Kernel::Term::create(original->functor(), original->arity(), args.data()));
    return true;
  }
  return false;
}

bool MegalodonChecker::certificateRewriteLiteralAtMegalodonPosition(
  Kernel::Literal* literal,
  Kernel::TermList needle,
  Kernel::TermList replacement,
  std::vector<unsigned>& position,
  Kernel::Literal*& rewrittenLiteral)
{
  rewrittenLiteral = nullptr;
  Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
  if (positive->isEquality()) {
    for (unsigned side = 0; side < 2; ++side) {
      std::vector<unsigned> childPosition;
      Kernel::TermList childRewritten;
      if (!certificateRewriteTermAtMegalodonPosition(*positive->nthArgument(side), needle, replacement, childPosition, childRewritten)) {
        continue;
      }
      Kernel::TermList left = side == 0 ? childRewritten : *positive->nthArgument(0);
      Kernel::TermList right = side == 1 ? childRewritten : *positive->nthArgument(1);
      rewrittenLiteral = Kernel::Literal::createEquality(
        literal->isPositive(),
        left,
        right,
        Kernel::SortHelper::getEqualityArgumentSort(positive));
      position.clear();
      if (side == 0) {
        position.push_back(0);
        position.push_back(1);
      } else {
        position.push_back(1);
      }
      position.insert(position.end(), childPosition.begin(), childPosition.end());
      return true;
    }
    return false;
  }

  std::vector<Kernel::TermList> args;
  args.reserve(positive->arity());
  for (unsigned i = 0; i < positive->arity(); ++i) {
    args.push_back(*positive->nthArgument(i));
  }
  for (unsigned i = 0; i < positive->arity(); ++i) {
    std::vector<unsigned> childPosition;
    Kernel::TermList childRewritten;
    if (!certificateRewriteTermAtMegalodonPosition(args[i], needle, replacement, childPosition, childRewritten)) {
      continue;
    }
    args[i] = childRewritten;
    rewrittenLiteral = Kernel::Literal::create(
      positive->functor(),
      positive->arity(),
      literal->isPositive(),
      args.data());
    position.clear();
    for (unsigned j = i + 1; j < positive->arity(); ++j) {
      position.push_back(0);
    }
    position.push_back(1);
    position.insert(position.end(), childPosition.begin(), childPosition.end());
    return true;
  }
  return false;
}

bool MegalodonChecker::certificateRewriteLiteralAtMegalodonPosition(
  Kernel::Literal* literal,
  Kernel::TermList needle,
  Kernel::TermList replacement,
  std::vector<unsigned>& position,
  std::string& rendered)
{
  Kernel::Literal* rewritten = nullptr;
  return certificateRewriteLiteralAtMegalodonPosition(literal, needle, replacement, position, rewritten)
    && certificateLiteralSexpr(rewritten, rendered);
}

bool MegalodonChecker::safeHolApplication(
  Kernel::TermList sort,
  Kernel::TermList lhs,
  Kernel::TermList rhs,
  Kernel::TermList& result) const
{
  try {
    result = HOL::create::app(sort, lhs, rhs);
    return true;
  } catch (...) {
    return false;
  }
}

bool MegalodonChecker::safeHolApplication(
  Kernel::TermList s1,
  Kernel::TermList s2,
  Kernel::TermList lhs,
  Kernel::TermList rhs,
  Kernel::TermList& result) const
{
  try {
    result = HOL::create::app(s1, s2, lhs, rhs);
    return true;
  } catch (...) {
    return false;
  }
}

bool MegalodonChecker::safeApplySubstitution(
  Kernel::TermList term,
  const Kernel::Substitution& substitution,
  Kernel::TermList& result) const
{
  try {
    result = Kernel::SubstHelper::apply(term, substitution);
    return true;
  } catch (...) {
    return false;
  }
}

bool MegalodonChecker::safeApplySubstitution(
  Kernel::Literal* literal,
  const Kernel::Substitution& substitution,
  Kernel::Literal*& result) const
{
  try {
    result = Kernel::SubstHelper::apply(literal, substitution);
    return true;
  } catch (...) {
    return false;
  }
}

std::string MegalodonChecker::certificatePositionSexpr(const std::vector<unsigned>& position) const
{
  std::ostringstream out;
  out << "(position";
  for (unsigned index : position) {
    out << ' ' << index;
  }
  out << ')';
  return out.str();
}

bool MegalodonChecker::certificateSource(Kernel::Unit* unit, std::string& result)
{
  Kernel::Unit* sourceUnit = unit;
  std::string sourceKind = "axiom";
  bool negatedConjectureInference = unit->inference().rule() == Kernel::InferenceRule::NEGATED_CONJECTURE;
  if (negatedConjectureInference) {
    UnitIterator parentIterator = unit->getParents();
    if (parentIterator.hasNext()) {
      sourceUnit = parentIterator.next();
    }
  }

  std::string sourceRole;
  bool hasSourceRole = Parse::TPTP::findUnitRole(sourceUnit, sourceRole);
  if (hasSourceRole) {
    if (sourceRole == "definition") {
      sourceKind = "definition";
    } else if (sourceRole == "conjecture") {
      if (negatedConjectureInference || unit->inputType() == Kernel::UnitInputType::NEGATED_CONJECTURE) {
        sourceKind = "negated_conjecture";
      } else {
        sourceKind = "conjecture";
      }
    } else if (sourceRole == "negated_conjecture") {
      sourceKind = "negated_conjecture";
    } else {
      sourceKind = "axiom";
    }
  } else {
    if (negatedConjectureInference) {
      if (sourceUnit->inputType() == Kernel::UnitInputType::CONJECTURE
        || sourceUnit->inputType() == Kernel::UnitInputType::NEGATED_CONJECTURE) {
        sourceKind = "negated_conjecture";
      }
    } else if (unit->inputType() == Kernel::UnitInputType::NEGATED_CONJECTURE) {
      sourceKind = "negated_conjecture";
    } else if (unit->inputType() == Kernel::UnitInputType::CONJECTURE) {
      sourceKind = "conjecture";
    }
  }

  std::string sourceName = "u" + std::to_string(sourceUnit->number());
  std::string axiomName;
  if (Parse::TPTP::findAxiomName(sourceUnit, axiomName) && !axiomName.empty()) {
    sourceName = axiomName;
  }
  result = "(source " + sourceKind + " " + sexprQuote(sourceName) + ")";
  return true;
}

bool MegalodonChecker::certificateFormulaTermSexpr(Kernel::Formula* formula, std::string& result)
{
  switch (formula->connective()) {
  case Kernel::LITERAL: {
    std::string atom;
    if (!certificateAtomSexpr(formula->literal(), atom)) {
      return false;
    }
    if (formula->literal()->isNegative()) {
      result = "(IMP " + atom + " (TMH \"vampire_false\"))";
    } else {
      result = atom;
    }
    return true;
  }
  case Kernel::BOOL_TERM:
    return certificateTermSexpr(formula->getBooleanTerm(), result);
  case Kernel::TRUE:
    result = "(TMH \"vampire_true\")";
    return true;
  case Kernel::FALSE:
    result = "(TMH \"vampire_false\")";
    return true;
  case Kernel::NOT: {
    std::string body;
    if (!certificateFormulaTermSexpr(formula->uarg(), body)) {
      return false;
    }
    result = "(IMP " + body + " (TMH \"vampire_false\"))";
    return true;
  }
  case Kernel::IMP: {
    std::string left;
    std::string right;
    if (!certificateFormulaTermSexpr(formula->left(), left)
      || !certificateFormulaTermSexpr(formula->right(), right)) {
      return false;
    }
    result = "(IMP " + left + " " + right + ")";
    return true;
  }
  case Kernel::OR:
  case Kernel::AND: {
    std::vector<std::string> args;
    auto iterator = formula->args()->iter();
    while (iterator.hasNext()) {
      std::string arg;
      if (!certificateFormulaTermSexpr(iterator.next(), arg)) {
        return false;
      }
      args.push_back(arg);
    }
    if (args.empty()) {
      return false;
    }
    const std::string name = formula->connective() == Kernel::OR ? "vampire_or" : "vampire_and";
    std::string rendered = args.back();
    for (auto it = args.rbegin() + 1; it != args.rend(); ++it) {
      rendered = "(AP (AP (TMH " + sexprQuote(name) + ") " + *it + ") " + rendered + ")";
    }
    result = rendered;
    return true;
  }
  case Kernel::FORALL: {
    std::string body;
    if (!certificateFormulaTermSexpr(formula->qarg(), body)) {
      return false;
    }
    std::vector<std::pair<unsigned, Kernel::TermList>> vars;
    Kernel::VSList::Iterator vit(formula->vars());
    while (vit.hasNext()) {
      vars.push_back(vit.next());
    }
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
      std::string type;
      if (!certificateTypeSexpr(it->second, type)) {
        return false;
      }
      body = "(ALLV " + sexprQuote(variableName(it->first)) + " " + type + " " + body + ")";
    }
    result = body;
    return true;
  }
  case Kernel::EXISTS: {
    std::string body;
    if (!certificateFormulaTermSexpr(formula->qarg(), body)) {
      return false;
    }
    std::vector<std::pair<unsigned, Kernel::TermList>> vars;
    Kernel::VSList::Iterator vit(formula->vars());
    while (vit.hasNext()) {
      vars.push_back(vit.next());
    }
    for (auto it = vars.rbegin(); it != vars.rend(); ++it) {
      std::string type;
      if (!certificateTypeSexpr(it->second, type)) {
        return false;
      }
      body = "(AP (TMH \"vampire_exists_prop\") (VLAMV "
        + sexprQuote(variableName(it->first)) + " " + type + " " + body + "))";
    }
    result = body;
    return true;
  }
  default:
    return false;
  }
}

bool MegalodonChecker::certificateFormulaNativeLiteralSexpr(Kernel::Formula* formula, bool& positive, std::string& atom)
{
  switch (formula->connective()) {
  case Kernel::LITERAL:
    positive = formula->literal()->isPositive();
    return certificateAtomSexpr(formula->literal(), atom);
  case Kernel::BOOL_TERM:
    positive = true;
    return certificateTermSexpr(formula->getBooleanTerm(), atom);
  case Kernel::NOT:
    if (!certificateFormulaNativeLiteralSexpr(formula->uarg(), positive, atom)) {
      return false;
    }
    positive = !positive;
    return true;
  case Kernel::IMP:
    if (formula->right()->connective() != Kernel::FALSE) {
      return false;
    }
    if (!certificateFormulaNativeLiteralSexpr(formula->left(), positive, atom)) {
      return false;
    }
    positive = !positive;
    return true;
  default:
    return false;
  }
}

bool MegalodonChecker::certificateFormulaNativeLiteralSexpr(Kernel::Formula* formula, std::string& result)
{
  bool positive;
  std::string atom;
  if (!certificateFormulaNativeLiteralSexpr(formula, positive, atom)) {
    return false;
  }
  result = std::string(positive ? "(pos " : "(neg ") + atom + ")";
  return true;
}

bool MegalodonChecker::certificateInputStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()) {
    return false;
  }
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (rule != Kernel::InferenceRule::INPUT) {
    return false;
  }

  std::string clause;
  std::string source;
  if (!certificateClauseSexpr(unit->asClause(), clause)
    || !certificateSource(unit, source)) {
    return false;
  }
  const std::string id = "u" + std::to_string(unit->number());
  result = "(input " + sexprQuote(id) + " " + source + " " + clause + ")";
  return true;
}

bool MegalodonChecker::certificateFormulaInputStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::INPUT) {
    return false;
  }
  std::string literal;
  std::string source;
  if (!certificateFormulaNativeLiteralSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), literal)
    || !certificateSource(unit, source)) {
    return false;
  }
  const std::string id = "u" + std::to_string(unit->number());
  result = "(formula_input " + sexprQuote(id) + " " + source + " " + literal + ")";
  return true;
}

bool MegalodonChecker::certificateFormulaTermInputStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause()) {
    return false;
  }
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (rule != Kernel::InferenceRule::INPUT && rule != Kernel::InferenceRule::NEGATED_CONJECTURE) {
    return false;
  }
  std::string formula;
  std::string source;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), formula)
    || !certificateSource(unit, source)) {
    return false;
  }
  const std::string id = "u" + std::to_string(unit->number());
  result = "(formula_term_input " + sexprQuote(id) + " " + source + " (formula " + formula + "))";
  return true;
}

bool MegalodonChecker::certificateFormulaCopyStepSexpr(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (rule != Kernel::InferenceRule::RECTIFY
    && rule != Kernel::InferenceRule::FLATTEN
    && rule != Kernel::InferenceRule::NNF
    && rule != Kernel::InferenceRule::REORIENT_EQUATIONS) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  std::string parentLiteral;
  std::string resultLiteral;
  if (!certificateFormulaNativeLiteralSexpr(static_cast<Kernel::FormulaUnit*>(parent)->formula(), parentLiteral)) {
    return false;
  }
  if (unit->isClause()) {
    if (unit->asClause()->length() != 1
      || !certificateLiteralSexpr((*unit->asClause())[0], resultLiteral)) {
      return false;
    }
  } else if (!certificateFormulaNativeLiteralSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultLiteral)) {
    return false;
  }
  if (parentLiteral != resultLiteral) {
    return false;
  }
  result = "(formula_copy " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + " (result " + resultLiteral + "))";
  return true;
}

bool MegalodonChecker::certificateFormulaTermCopyStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause()) {
    return false;
  }
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (rule != Kernel::InferenceRule::RECTIFY
    && rule != Kernel::InferenceRule::FLATTEN
    && rule != Kernel::InferenceRule::NNF) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  std::string parentFormula;
  std::string resultFormula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(parent)->formula(), parentFormula)
    || !certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultFormula)
    || parentFormula != resultFormula) {
    return false;
  }
  result = "(formula_term_copy " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + " (result (formula " + resultFormula + ")))";
  return true;
}

bool MegalodonChecker::certificateRectifyFormulaStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::RECTIFY) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  std::string resultFormula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultFormula)) {
    return false;
  }
  std::string renamings;
  const auto* genericInfo = InferenceRecorder::instance()->getGenericInferenceInformation(unit->number());
  if (genericInfo == nullptr) {
    genericInfo = InferenceRecorder::instance()->getGenericLastInferenceInformation();
  }
  const auto* rectifyInfo = static_cast<const InferenceRecorder::RectifyInferenceExtra*>(genericInfo);
  if (rectifyInfo != nullptr && !rectifyInfo->renamings.empty()) {
    std::ostringstream out;
    out << " (renamings";
    for (const auto& renaming : rectifyInfo->renamings) {
      Kernel::Formula* newFormula = renaming.first;
      Kernel::Formula* sourceFormula = renaming.second.first;
      const Kernel::Substitution& substitution = renaming.second.second;
      std::string sourceSexpr;
      std::string targetSexpr;
      std::string substitutionSexpr;
      if (!certificateFormulaTermSexpr(sourceFormula, sourceSexpr)
        || !certificateFormulaTermSexpr(newFormula, targetSexpr)
        || !certificateSubstitutionSexpr(substitution, substitutionSexpr)) {
        return false;
      }
      out << " (renaming"
          << " (source (formula " << sourceSexpr << "))"
          << " " << substitutionSexpr
          << " (target (formula " << targetSexpr << ")))";
    }
    out << ')';
    renamings = out.str();
  }
  result = "(rectify_formula " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + renamings
    + " (result (formula " + resultFormula + ")))";
  return true;
}

bool MegalodonChecker::certificateFoolBoolStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::FOOL_ELIMINATION) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  bool parentPositive;
  std::string parentAtom;
  std::string resultLiteral;
  if (!certificateFormulaNativeLiteralSexpr(static_cast<Kernel::FormulaUnit*>(parent)->formula(), parentPositive, parentAtom)
    || !certificateFormulaNativeLiteralSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultLiteral)) {
    return false;
  }
  std::string expectedAtom;
  if (!certificateEqualityAtomSexpr(Kernel::AtomicSort::boolSort(), parentAtom, "(TMH \"f__true\")", expectedAtom)) {
    return false;
  }
  const std::string expectedLiteral = std::string(parentPositive ? "(pos " : "(neg ") + expectedAtom + ")";
  if (resultLiteral != expectedLiteral) {
    return false;
  }
  result = "(fool_bool " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + " (result " + resultLiteral + "))";
  return true;
}

bool MegalodonChecker::certificateFoolFormulaStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::FOOL_ELIMINATION) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  std::string parentFormula;
  std::string resultFormula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(parent)->formula(), parentFormula)
    || !certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultFormula)
    || parentFormula == resultFormula) {
    return false;
  }
  Kernel::Formula* source = static_cast<Kernel::FormulaUnit*>(parent)->formula();
  Kernel::Formula* target = static_cast<Kernel::FormulaUnit*>(unit)->formula();
  std::vector<std::tuple<std::string, std::string, std::string, Kernel::Formula*>> primitives;
  unsigned pairCount = 0;
  const unsigned pairLimit = 48;
  std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned, std::string)> collectPairs =
    [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth, std::string path) {
      if (left == nullptr || right == nullptr || depth > 24 || pairCount >= pairLimit) {
        return;
      }
      if (left->toString() == right->toString()) {
        return;
      }
      std::string leftText;
      std::string rightText;
      if (certificateFormulaTermSexpr(left, leftText) && certificateFormulaTermSexpr(right, rightText)) {
        primitives.push_back(std::make_tuple(leftText, rightText, path, right));
        ++pairCount;
      }
      if (left->connective() != right->connective()) {
        return;
      }
      switch (left->connective()) {
        case Kernel::AND:
        case Kernel::OR: {
          Kernel::FormulaList::Iterator leftIt(left->args());
          Kernel::FormulaList::Iterator rightIt(right->args());
          unsigned index = 0;
          while (leftIt.hasNext() && rightIt.hasNext()) {
            collectPairs(leftIt.next(), rightIt.next(), depth + 1, path + ".arg[" + std::to_string(index) + "]");
            ++index;
          }
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
  collectPairs(source, target, 0, "root");

  std::ostringstream out;
  const std::string unitId = "u" + std::to_string(unit->number());
  for (std::size_t index = 0; index < primitives.size(); ++index) {
    const auto& [sourceText, targetText, path, targetFormula] = primitives[index];
    const std::string primitiveId = unitId + "_fool_atom_" + std::to_string(index);
    std::string proposition;
    bool renderingReplayExtra = _renderingReplayExtra;
    _renderingReplayExtra = true;
    bool hasProposition = formulaToMegalodon(targetFormula, proposition);
    _renderingReplayExtra = renderingReplayExtra;
    if (hasProposition) {
      out << "(step_proposition " << sexprQuote(primitiveId) << " " << sexprQuote(proposition) << ")\n  ";
    }
    out << "(fool_atom_lift " << sexprQuote(primitiveId)
        << " (source (formula " << sourceText << "))"
        << " (target (formula " << targetText << "))"
        << " (path " << sexprQuote(path) << "))\n  ";
  }
  out << "(fool_formula " << sexprQuote(unitId)
      << " (parent " << sexprQuote("u" + std::to_string(parent->number())) << ")"
      << " (result (formula " << resultFormula << ")))";
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateEnnfFormulaStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::ENNF) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  std::string sourceFormula;
  std::string resultFormula;
  Kernel::Formula* source = static_cast<Kernel::FormulaUnit*>(parent)->formula();
  Kernel::Formula* target = static_cast<Kernel::FormulaUnit*>(unit)->formula();
  if (!certificateFormulaTermSexpr(source, sourceFormula)
    || !certificateFormulaTermSexpr(target, resultFormula)) {
    return false;
  }

  auto formulaArgs = [](Kernel::Formula* formula) {
    std::vector<Kernel::Formula*> result;
    Kernel::FormulaList::Iterator args(formula->args());
    while (args.hasNext()) {
      result.push_back(args.next());
    }
    return result;
  };
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

  unsigned pairCount = 0;
  const unsigned pairLimit = 32;
  std::vector<std::tuple<std::string, std::string, std::string, std::string>> pairs;
  auto connectiveKind = [](Kernel::Connective connective) {
    switch (connective) {
      case Kernel::IMP: return std::string("imp");
      case Kernel::FORALL: return std::string("forall");
      case Kernel::EXISTS: return std::string("exists");
      case Kernel::AND: return std::string("and");
      case Kernel::OR: return std::string("or");
      case Kernel::NOT: return std::string("not");
      case Kernel::IFF: return std::string("iff");
      case Kernel::XOR: return std::string("xor");
      default: return std::string("other");
    }
  };
  auto pairKind = [&](Kernel::Formula* left, Kernel::Formula* right) {
    if (left == nullptr || right == nullptr) {
      return std::string("unknown");
    }
    if (left->connective() == right->connective()) {
      return std::string("context_") + connectiveKind(left->connective());
    }
    std::vector<Kernel::Formula*> rightArgs;
    if (right->connective() == Kernel::AND || right->connective() == Kernel::OR) {
      rightArgs = formulaArgs(right);
    }
    if (left->connective() == Kernel::IMP && right->connective() == Kernel::OR && rightArgs.size() == 2) {
      return std::string("imp_to_or");
    }
    Kernel::Formula* negated = negatedBody(left);
    if (negated == nullptr) {
      return std::string("unknown");
    }
    if (negated->connective() == Kernel::IMP && right->connective() == Kernel::AND && rightArgs.size() == 2) {
      return std::string("not_imp_to_and");
    }
    if (negated->connective() == Kernel::FORALL && right->connective() == Kernel::EXISTS) {
      return std::string("not_forall_to_exists");
    }
    if (negated->connective() == Kernel::AND && right->connective() == Kernel::OR) {
      return std::string("not_and_to_or");
    }
    if (negated->connective() == Kernel::OR && right->connective() == Kernel::AND) {
      return std::string("not_or_to_and");
    }
    return std::string("unknown");
  };
  auto emitPair = [&](Kernel::Formula* left, Kernel::Formula* right, const std::string& path) {
    if (left == nullptr || right == nullptr || pairCount >= pairLimit) {
      return false;
    }
    std::string leftText;
    std::string rightText;
    if (!certificateFormulaTermSexpr(left, leftText)
      || !certificateFormulaTermSexpr(right, rightText)
      || leftText == rightText) {
      return false;
    }
    pairs.push_back(std::make_tuple(path, leftText, rightText, pairKind(left, right)));
    ++pairCount;
    return true;
  };

  std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned, std::string)> collectPairs;
  std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned, std::string)> collectEnnfPairs;
  collectPairs =
    [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth, std::string path) {
      if (left == nullptr || right == nullptr || depth > 16 || pairCount >= pairLimit) {
        return;
      }
      emitPair(left, right, path);
      if (left->connective() != right->connective()) {
        collectEnnfPairs(left, right, depth + 1, path);
        return;
      }
      switch (left->connective()) {
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
        case Kernel::AND:
        case Kernel::OR: {
          std::vector<Kernel::Formula*> leftArgs = formulaArgs(left);
          std::vector<Kernel::Formula*> rightArgs = formulaArgs(right);
          const std::size_t argCount = std::min(leftArgs.size(), rightArgs.size());
          for (std::size_t index = 0; index < argCount; ++index) {
            collectPairs(leftArgs[index], rightArgs[index], depth + 1,
              path + "." + (left->connective() == Kernel::AND ? "and" : "or")
              + "[" + std::to_string(index) + "]");
          }
          return;
        }
        default:
          return;
      }
    };
  collectEnnfPairs =
    [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth, std::string path) {
      if (left == nullptr || right == nullptr || depth > 16 || pairCount >= pairLimit) {
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
      if (negated->connective() == Kernel::FORALL && right->connective() == Kernel::EXISTS) {
        collectPairs(negatedFormula(negated->qarg()), right->qarg(), depth + 1, path + ".ennf_neg_forall_body");
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
        const std::size_t argCount = std::min(leftArgs.size(), rightArgs.size());
        for (std::size_t index = 0; index < argCount; ++index) {
          collectPairs(
            negatedFormula(leftArgs[index]),
            rightArgs[index],
            depth + 1,
            path + ".ennf_neg_junction[" + std::to_string(index) + "]");
        }
      }
    };
  collectPairs(source, target, 0, "root");

  std::ostringstream pairsOut;
  pairsOut << "(pairs";
  for (const auto& [path, leftText, rightText, kind] : pairs) {
    pairsOut << " (pair (path " << sexprQuote(path) << ")"
             << " (kind " << sexprQuote(kind) << ")"
             << " (source (formula " << leftText << "))"
             << " (target (formula " << rightText << ")))";
  }
  pairsOut << ")";

  result = "(ennf_formula " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + " (source (formula " + sourceFormula + "))"
    + " " + pairsOut.str()
    + " (result (formula " + resultFormula + ")))";
  return true;
}

bool MegalodonChecker::termHasHeadFunctor(Kernel::TermList term, unsigned functor) const
{
  while (term.isApplication()) {
    term = term.lhs();
  }
  return term.isTerm() && !term.term()->isSpecial() && term.term()->functor() == functor;
}

bool MegalodonChecker::findTermWithHeadFunctor(Kernel::TermList term, unsigned functor, Kernel::TermList& found) const
{
  if (term.isVar()) {
    return false;
  }
  if (term.isApplication()) {
    if (termHasHeadFunctor(term, functor)) {
      found = term;
      return true;
    }
    return findTermWithHeadFunctor(term.lhs(), functor, found)
      || findTermWithHeadFunctor(term.rhs(), functor, found);
  }
  Kernel::Term* t = term.term();
  if (t->functor() == functor) {
    found = term;
    return true;
  }
  for (unsigned i = 0; i < t->arity(); ++i) {
    if (findTermWithHeadFunctor(*t->nthArgument(i), functor, found)) {
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::findFormulaTermWithHeadFunctor(Kernel::Formula* formula, unsigned functor, Kernel::TermList& found) const
{
  switch (formula->connective()) {
  case Kernel::LITERAL: {
    Kernel::Literal* literal = formula->literal();
    for (unsigned i = 0; i < literal->arity(); ++i) {
      if (findTermWithHeadFunctor(*literal->nthArgument(i), functor, found)) {
        return true;
      }
    }
    return false;
  }
  case Kernel::BOOL_TERM:
    return findTermWithHeadFunctor(formula->getBooleanTerm(), functor, found);
  case Kernel::NOT:
    return findFormulaTermWithHeadFunctor(formula->uarg(), functor, found);
  case Kernel::IMP:
  case Kernel::IFF:
  case Kernel::XOR:
    return findFormulaTermWithHeadFunctor(formula->left(), functor, found)
      || findFormulaTermWithHeadFunctor(formula->right(), functor, found);
  case Kernel::AND:
  case Kernel::OR: {
    auto iterator = formula->args()->iter();
    while (iterator.hasNext()) {
      if (findFormulaTermWithHeadFunctor(iterator.next(), functor, found)) {
        return true;
      }
    }
    return false;
  }
  case Kernel::FORALL:
  case Kernel::EXISTS:
    return findFormulaTermWithHeadFunctor(formula->qarg(), functor, found);
  default:
    return false;
  }
}

bool MegalodonChecker::variableApplicationCount(Kernel::TermList term, unsigned var, unsigned& count) const
{
  unsigned applications = 0;
  Kernel::TermList head = term;
  while (head.isApplication()) {
    ++applications;
    head = head.lhs();
  }
  if (head.isVar() && head.var() == var) {
    count = applications;
    return true;
  }
  return false;
}

bool MegalodonChecker::findTermVariableApplicationCount(Kernel::TermList term, unsigned var, unsigned& count) const
{
  if (variableApplicationCount(term, var, count)) {
    return true;
  }
  if (term.isVar()) {
    return false;
  }
  if (term.isApplication()) {
    return findTermVariableApplicationCount(term.lhs(), var, count)
      || findTermVariableApplicationCount(term.rhs(), var, count);
  }
  Kernel::Term* t = term.term();
  for (unsigned i = 0; i < t->arity(); ++i) {
    if (findTermVariableApplicationCount(*t->nthArgument(i), var, count)) {
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::findFormulaVariableApplicationCount(Kernel::Formula* formula, unsigned var, unsigned& count) const
{
  switch (formula->connective()) {
  case Kernel::LITERAL: {
    Kernel::Literal* literal = formula->literal();
    for (unsigned i = 0; i < literal->arity(); ++i) {
      if (findTermVariableApplicationCount(*literal->nthArgument(i), var, count)) {
        return true;
      }
    }
    return false;
  }
  case Kernel::BOOL_TERM:
    return findTermVariableApplicationCount(formula->getBooleanTerm(), var, count);
  case Kernel::NOT:
    return findFormulaVariableApplicationCount(formula->uarg(), var, count);
  case Kernel::IMP:
  case Kernel::IFF:
  case Kernel::XOR:
    return findFormulaVariableApplicationCount(formula->left(), var, count)
      || findFormulaVariableApplicationCount(formula->right(), var, count);
  case Kernel::AND:
  case Kernel::OR: {
    auto iterator = formula->args()->iter();
    while (iterator.hasNext()) {
      if (findFormulaVariableApplicationCount(iterator.next(), var, count)) {
        return true;
      }
    }
    return false;
  }
  case Kernel::FORALL:
  case Kernel::EXISTS:
    return findFormulaVariableApplicationCount(formula->qarg(), var, count);
  default:
    return false;
  }
}

bool MegalodonChecker::trimTrailingApplications(Kernel::TermList term, unsigned count, Kernel::TermList& trimmed) const
{
  while (count > 0) {
    if (!term.isApplication()) {
      return false;
    }
    term = term.lhs();
    --count;
  }
  trimmed = term;
  return true;
}

bool MegalodonChecker::skolemWitnessTerm(
  Kernel::Formula* parent,
  Kernel::Formula* result,
  unsigned skolemFunctor,
  unsigned replacedVar,
  Kernel::TermList& witness,
  unsigned& parentApplicationCount) const
{
  Kernel::TermList skolemTerm;
  if (!findFormulaTermWithHeadFunctor(result, skolemFunctor, skolemTerm)) {
    return false;
  }
  if (!findFormulaVariableApplicationCount(parent, replacedVar, parentApplicationCount)) {
    return false;
  }
  return trimTrailingApplications(skolemTerm, parentApplicationCount, witness);
}

bool MegalodonChecker::decomposeApplicationSpine(Kernel::TermList term, Kernel::TermList& head, std::vector<Kernel::TermList>& args) const
{
  args.clear();
  while (term.isApplication()) {
    args.push_back(term.rhs());
    term = term.lhs();
  }
  head = term;
  std::reverse(args.begin(), args.end());
  return true;
}

bool MegalodonChecker::certificateSkolemFormulaStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::SKOLEMIZE) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause() || !_is->hasIntroducedSymbols(unit)) {
    return false;
  }

  std::vector<std::pair<unsigned, std::string>> bindings;
  std::vector<std::string> introductions;
  for (auto symbol : iterTraits(Kernel::InferenceStore::SymbolStack::ConstIterator(_is->getIntroducedSymbols(unit)))) {
    if (symbol.first != Kernel::SymbolType::FUNC) {
      continue;
    }
    long var = _is->variableReplacedByIntroducedSymbol(symbol.second);
    if (var < 0) {
      continue;
    }
    Kernel::TermList skolemTerm;
    std::string skolemTermSexpr;
    if (!findFormulaTermWithHeadFunctor(static_cast<Kernel::FormulaUnit*>(unit)->formula(), symbol.second, skolemTerm)) {
      skolemTermSexpr = "(TMH " + sexprQuote(functionName(symbol.second)) + ")";
    } else {
      unsigned parentApplicationCount = 0;
      if (!findFormulaVariableApplicationCount(static_cast<Kernel::FormulaUnit*>(parent)->formula(), static_cast<unsigned>(var), parentApplicationCount)) {
        return false;
      }
      Kernel::TermList trimmedSkolemTerm;
      if (!trimTrailingApplications(skolemTerm, parentApplicationCount, trimmedSkolemTerm)) {
        skolemTermSexpr = "(TMH " + sexprQuote(functionName(symbol.second)) + ")";
      } else {
        skolemTerm = trimmedSkolemTerm;
        if (!certificateTermSexpr(skolemTerm, skolemTermSexpr)) {
          skolemTermSexpr = "(TMH " + sexprQuote(functionName(symbol.second)) + ")";
        }
      }
    }
    bindings.push_back({static_cast<unsigned>(var), skolemTermSexpr});
    std::string name = functionName(symbol.second);
    std::string introduction = "(symbol (name " + sexprQuote(name) + ")";
    introduction += " (replaced_var " + sexprQuote(variableName(static_cast<unsigned>(var))) + ")";
    std::string declaration = functionDeclaration(symbol.second, name);
    if (!declaration.empty()) {
      introduction += " (declaration " + sexprQuote(declaration) + ")";
    }
    introduction += ")";
    introductions.push_back(introduction);
  }
  if (bindings.empty()) {
    return false;
  }
  std::sort(bindings.begin(), bindings.end(), [](const auto& left, const auto& right) {
    return left.first < right.first;
  });
  std::sort(introductions.begin(), introductions.end());

  std::string subst = "(subst";
  for (const auto& binding : bindings) {
    subst += " (" + sexprQuote(variableName(binding.first)) + " " + binding.second + ")";
  }
  subst += ")";

  std::string introduced = "(introduced";
  for (const auto& introduction : introductions) {
    introduced += " " + introduction;
  }
  introduced += ")";

  std::string sourceFormula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(parent)->formula(), sourceFormula)) {
    sourceFormula.clear();
  }

  std::string resultFormula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultFormula)) {
    result = "(skolem_formula_computed " + sexprQuote("u" + std::to_string(unit->number()))
      + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
      + " " + subst + ")";
    return true;
  }

  result = "(skolem_formula " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + (sourceFormula.empty() ? "" : " (source (formula " + sourceFormula + "))")
    + " " + subst
    + (sourceFormula.empty() ? "" : " " + introduced)
    + " (result (formula " + resultFormula + ")))";
  return true;
}

bool MegalodonChecker::certificateCnfLiteralStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::CLAUSIFY) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  if (unit->asClause()->length() != 1) {
    return false;
  }
  std::string sourceLiteral;
  std::string targetLiteral;
  if (!certificateFormulaNativeLiteralSexpr(static_cast<Kernel::FormulaUnit*>(parent)->formula(), sourceLiteral)
    || !certificateLiteralSexpr((*unit->asClause())[0], targetLiteral)
    || sourceLiteral != targetLiteral) {
    return false;
  }
  std::string clause;
  if (!certificateClauseSexpr(unit->asClause(), clause)) {
    return false;
  }
  result = "(cnf_literal " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + " (result " + clause + "))";
  return true;
}

bool MegalodonChecker::certificateCnfFormulaClauseStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::CLAUSIFY) {
    return false;
  }
  UnitIterator parentIterator = unit->getParents();
  if (!parentIterator.hasNext()) {
    return false;
  }
  Kernel::Unit* parent = parentIterator.next();
  if (parent->isClause()) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return false;
  }
  const auto* clauseExtra = static_cast<const Inferences::CNFClauseInferenceExtra*>(extra);
  std::string clause;
  if (!certificateClauseSexpr(unit->asClause(), clause)) {
    return false;
  }
  result = "(cnf_formula_clause " + sexprQuote("u" + std::to_string(unit->number()))
    + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
    + " (index " + std::to_string(clauseExtra->index) + ")"
    + " (count " + std::to_string(clauseExtra->count) + ")"
    + " (result " + clause + "))";
  return true;
}

bool MegalodonChecker::certificatePredicateDefinitionSymbol(Kernel::Formula* formula, std::string& result)
{
  auto isFalseFormula = [](Kernel::Formula* candidate) {
    return candidate != nullptr && candidate->connective() == Kernel::FALSE;
  };
  auto isFoolConstant = [](Kernel::TermList term, bool value) {
    return term.isTerm()
      && !term.term()->isSpecial()
      && env.signature->isFoolConstantSymbol(value, term.term()->functor());
  };
  auto termHeadSymbol = [&](Kernel::TermList term, std::string& symbol) {
    while (term.isApplication()) {
      term = term.lhs();
    }
    if (!term.isTerm() || term.term()->isSpecial()) {
      return false;
    }
    symbol = functionName(term.term()->functor());
    return true;
  };
  auto atomHeadSymbol = [&](Kernel::Formula* atom, std::string& symbol) {
    if (atom == nullptr) {
      return false;
    }
    if (atom->connective() == Kernel::BOOL_TERM) {
      return termHeadSymbol(atom->getBooleanTerm(), symbol);
    }
    if (atom->connective() != Kernel::LITERAL) {
      return false;
    }
    Kernel::Literal* literal = atom->literal();
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (!positive->isEquality()) {
      symbol = predicateName(positive->functor());
      return true;
    }
    Kernel::TermList left = *positive->nthArgument(0);
    Kernel::TermList right = *positive->nthArgument(1);
    if (isFoolConstant(left, true) || isFoolConstant(left, false)) {
      return termHeadSymbol(right, symbol);
    }
    if (isFoolConstant(right, true) || isFoolConstant(right, false)) {
      return termHeadSymbol(left, symbol);
    }
    return false;
  };
  std::function<bool(Kernel::Formula*, std::string&)> negativeDefiniendumSymbol =
    [&](Kernel::Formula* candidate, std::string& symbol) -> bool {
      if (candidate == nullptr) {
        return false;
      }
      switch (candidate->connective()) {
      case Kernel::FORALL:
        return negativeDefiniendumSymbol(candidate->qarg(), symbol);
      case Kernel::OR: {
        auto args = candidate->args()->iter();
        while (args.hasNext()) {
          if (negativeDefiniendumSymbol(args.next(), symbol)) {
            return true;
          }
        }
        return false;
      }
      case Kernel::IMP:
        return isFalseFormula(candidate->right()) && atomHeadSymbol(candidate->left(), symbol);
      case Kernel::NOT:
        return atomHeadSymbol(candidate->uarg(), symbol);
      case Kernel::LITERAL:
        return candidate->literal()->isNegative() && atomHeadSymbol(candidate, symbol);
      default:
        return false;
      }
    };
  return negativeDefiniendumSymbol(formula, result);
}

bool MegalodonChecker::certificatePredicateDefinitionStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::PREDICATE_DEFINITION) {
    return false;
  }
  if (!_is->hasIntroducedSymbols(unit)) {
    return false;
  }
  auto& symbols = _is->getIntroducedSymbols(unit);
  if (symbols.size() != 1 || symbols.top().first != SymbolType::PRED) {
    return false;
  }
  std::string formula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), formula)) {
    return false;
  }
  std::string symbolName;
  if (!certificatePredicateDefinitionSymbol(static_cast<Kernel::FormulaUnit*>(unit)->formula(), symbolName)) {
    symbolName = predicateName(symbols.top().second);
  }
  result = "(predicate_definition " + sexprQuote("u" + std::to_string(unit->number()))
    + " (symbol " + sexprQuote(symbolName) + ")"
    + " (result (formula " + formula + ")))";
  return true;
}

bool MegalodonChecker::certificatePredicateDefinitionFoldStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::DEFINITION_FOLDING_PRED) {
    return false;
  }
  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  Kernel::Unit* sourceParent = nullptr;
  std::vector<Kernel::Unit*> definitionParents;
  for (Kernel::Unit* parent : parents) {
    if (parent->isClause()) {
      continue;
    }
    if (parent->inference().rule() == Kernel::InferenceRule::PREDICATE_DEFINITION) {
      definitionParents.push_back(parent);
      continue;
    }
    if (sourceParent == nullptr) {
      sourceParent = parent;
    }
  }
  if (sourceParent == nullptr || definitionParents.empty()) {
    return false;
  }
  std::string resultFormula;
  if (!certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(unit)->formula(), resultFormula)) {
    return false;
  }
  if (definitionParents.size() == 1) {
    result = "(predicate_definition_fold " + sexprQuote("u" + std::to_string(unit->number()))
      + " (source " + sexprQuote("u" + std::to_string(sourceParent->number())) + ")"
      + " (definition " + sexprQuote("u" + std::to_string(definitionParents[0]->number())) + ")"
      + " (result (formula " + resultFormula + ")))";
    return true;
  }
  std::reverse(definitionParents.begin(), definitionParents.end());
  std::ostringstream definitions;
  definitions << "(definitions";
  for (Kernel::Unit* definitionParent : definitionParents) {
    definitions << ' ' << sexprQuote("u" + std::to_string(definitionParent->number()));
  }
  definitions << ')';
  result = "(predicate_definition_fold_chain " + sexprQuote("u" + std::to_string(unit->number()))
    + " (source " + sexprQuote("u" + std::to_string(sourceParent->number())) + ") "
    + definitions.str()
    + " (result (formula " + resultFormula + ")))";
  return true;
}

bool MegalodonChecker::certificateDefinitionInputStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::FUNCTION_DEFINITION) {
    return false;
  }
  std::string clause;
  if (!certificateClauseSexpr(unit->asClause(), clause)) {
    return false;
  }
  result = "(definition_input " + sexprQuote("u" + std::to_string(unit->number()))
    + " (result " + clause + "))";
  return true;
}

bool MegalodonChecker::certificateInequalitySplittingNameIntroductionStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION) {
    return false;
  }
  Kernel::Clause* clause = unit->asClause();
  if (clause->length() != 1) {
    return false;
  }
  std::string renderedClause;
  if (!certificateClauseSexpr(clause, renderedClause)) {
    return false;
  }
  result = "(inequality_name_intro " + sexprQuote("u" + std::to_string(unit->number()))
    + " (result " + renderedClause + "))";
  return true;
}

bool MegalodonChecker::certificateInequalitySplittingStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::INEQUALITY_SPLITTING) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.size() < 2 || !parents[0]->isClause()) {
    return false;
  }
  for (std::size_t i = 1; i < parents.size(); ++i) {
    if (!parents[i]->isClause()
      || parents[i]->inference().rule() != Kernel::InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION
      || parents[i]->asClause()->length() != 1) {
      return false;
    }
  }

  auto isFoolConstant = [](Kernel::TermList term, bool value) {
    return term.isTerm()
      && !term.term()->isSpecial()
      && env.signature->isFoolConstantSymbol(value, term.term()->functor());
  };
  auto boolNameLiteralTerm = [&](Kernel::Literal* literal, bool value, Kernel::TermList& namedTerm) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isPositive()
      || Kernel::SortHelper::getEqualityArgumentSort(literal) != Kernel::AtomicSort::boolSort()) {
      return false;
    }
    Kernel::TermList left = *literal->nthArgument(0);
    Kernel::TermList right = *literal->nthArgument(1);
    if (isFoolConstant(left, value)) {
      namedTerm = right;
      return true;
    }
    if (isFoolConstant(right, value)) {
      namedTerm = left;
      return true;
    }
    return false;
  };
  auto applicationHeadAndArg = [](Kernel::TermList term, Kernel::TermList& head, Kernel::TermList& arg) {
    if (!term.isApplication()) {
      return false;
    }
    head = term.lhs();
    arg = term.rhs();
    return true;
  };
  auto replacementInConclusion = [&](Kernel::TermList head, Kernel::TermList argument, Kernel::Literal*& replacement) {
    for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
      Kernel::TermList namedTerm;
      Kernel::TermList candidateHead;
      Kernel::TermList candidateArg;
      if (boolNameLiteralTerm(literal, true, namedTerm)
        && applicationHeadAndArg(namedTerm, candidateHead, candidateArg)
        && candidateHead == head
        && candidateArg == argument) {
        replacement = literal;
        return true;
      }
    }
    return false;
  };

  Kernel::Clause* sourceClause = parents[0]->asClause();
  std::set<Kernel::Literal*> usedSourceLiterals;
  std::set<Kernel::Literal*> usedReplacementLiterals;
  std::vector<std::string> splitItems;
  for (std::size_t parentIndex = 1; parentIndex < parents.size(); ++parentIndex) {
    Kernel::Literal* nameLiteral = (*parents[parentIndex]->asClause())[0];
    Kernel::TermList namedTerm;
    Kernel::TermList nameHead;
    Kernel::TermList splitTerm;
    if (!boolNameLiteralTerm(nameLiteral, false, namedTerm)
      || !applicationHeadAndArg(namedTerm, nameHead, splitTerm)) {
      return false;
    }

    Kernel::Literal* selected = nullptr;
    Kernel::Literal* replacement = nullptr;
    for (Kernel::Literal* sourceLiteral : sourceClause->iterLits()) {
      if (usedSourceLiterals.find(sourceLiteral) != usedSourceLiterals.end()
        || !sourceLiteral->isEquality()
        || sourceLiteral->isPositive()) {
        continue;
      }
      Kernel::TermList left = *sourceLiteral->nthArgument(0);
      Kernel::TermList right = *sourceLiteral->nthArgument(1);
      Kernel::TermList otherSide;
      if (left == splitTerm) {
        otherSide = right;
      } else if (right == splitTerm) {
        otherSide = left;
      } else {
        continue;
      }
      Kernel::Literal* candidateReplacement = nullptr;
      if (!replacementInConclusion(nameHead, otherSide, candidateReplacement)
        || usedReplacementLiterals.find(candidateReplacement) != usedReplacementLiterals.end()) {
        continue;
      }
      selected = sourceLiteral;
      replacement = candidateReplacement;
      break;
    }
    if (selected == nullptr || replacement == nullptr) {
      return false;
    }
    usedSourceLiterals.insert(selected);
    usedReplacementLiterals.insert(replacement);

    std::string selectedSexpr;
    std::string nameLiteralSexpr;
    std::string replacementSexpr;
    if (!certificateLiteralSexpr(selected, selectedSexpr)
      || !certificateLiteralSexpr(nameLiteral, nameLiteralSexpr)
      || !certificateLiteralSexpr(replacement, replacementSexpr)) {
      return false;
    }
    splitItems.push_back(
      "(split (name_parent " + sexprQuote("u" + std::to_string(parents[parentIndex]->number())) + ")"
      + " (source " + selectedSexpr + ")"
      + " (name_literal " + nameLiteralSexpr + ")"
      + " (replacement " + replacementSexpr + "))");
  }

  std::vector<std::string> expectedLiterals;
  for (Kernel::Literal* literal : sourceClause->iterLits()) {
    if (usedSourceLiterals.find(literal) != usedSourceLiterals.end()) {
      continue;
    }
    std::string rendered;
    if (!certificateLiteralSexpr(literal, rendered)) {
      return false;
    }
    expectedLiterals.push_back(rendered);
  }
  for (Kernel::Literal* literal : usedReplacementLiterals) {
    std::string rendered;
    if (!certificateLiteralSexpr(literal, rendered)) {
      return false;
    }
    expectedLiterals.push_back(rendered);
  }
  std::sort(expectedLiterals.begin(), expectedLiterals.end());
  expectedLiterals.erase(std::unique(expectedLiterals.begin(), expectedLiterals.end()), expectedLiterals.end());
  std::vector<std::string> actualLiterals;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actualLiterals)) {
    return false;
  }
  std::sort(actualLiterals.begin(), actualLiterals.end());
  actualLiterals.erase(std::unique(actualLiterals.begin(), actualLiterals.end()), actualLiterals.end());
  if (expectedLiterals != actualLiterals) {
    return false;
  }

  std::string conclusion;
  if (!certificateClauseSexpr(unit->asClause(), conclusion)) {
    return false;
  }
  std::ostringstream splits;
  splits << "(splits";
  for (const std::string& item : splitItems) {
    splits << ' ' << item;
  }
  splits << ')';
  result = "(inequality_split " + sexprQuote("u" + std::to_string(unit->number()))
    + " (source " + sexprQuote("u" + std::to_string(parents[0]->number())) + ") "
    + splits.str()
    + " (result " + conclusion + "))";
  return true;
}

bool MegalodonChecker::certificateExtensionalityResolutionStepsSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::EXTENSIONALITY_RESOLUTION) {
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

  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    return literals;
  };
  auto sameMultiset = [&](const std::vector<std::string>& left, const std::vector<std::string>& right) {
    return normalized(left) == normalized(right);
  };
  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };
  auto applyRenderedSubstitution =
    [&](const std::vector<std::string>& source, const Kernel::Substitution& substitution, std::vector<std::string>& rendered) {
      std::vector<std::tuple<unsigned, std::string, std::string>> replacements;
      Kernel::Substitution substitutionCopy = substitution;
      for (auto [var, term] : iterTraits(substitutionCopy.items())) {
        if (term.isVar() && term.var() == var) {
          continue;
        }
        std::string termSexpr;
        if (!certificateTermSexpr(term, termSexpr)) {
          return false;
        }
        replacements.push_back({var, "(TMH " + sexprQuote(variableName(var)) + ")", termSexpr});
      }
      std::sort(replacements.begin(), replacements.end(), [](const auto& left, const auto& right) {
        return std::get<0>(left) < std::get<0>(right);
      });
      rendered = source;
      for (std::string& literal : rendered) {
        for (std::size_t i = 0; i < replacements.size(); ++i) {
          replaceAll(literal, std::get<1>(replacements[i]), "(TMH " + sexprQuote("__mg_ext_subst_" + std::to_string(i)) + ")");
        }
        for (std::size_t i = 0; i < replacements.size(); ++i) {
          replaceAll(literal, "(TMH " + sexprQuote("__mg_ext_subst_" + std::to_string(i)) + ")", std::get<2>(replacements[i]));
        }
      }
      return true;
    };
  auto swapEqualityLiteralSexpr = [](const std::string& literal, std::string& swapped) {
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto removeFirst = [](std::vector<std::string>& literals, const std::string& literal) {
    auto it = std::find(literals.begin(), literals.end(), literal);
    if (it == literals.end()) {
      return false;
    }
    literals.erase(it);
    return true;
  };
  auto tryBuildSubstitution = [](Kernel::Literal* extLiteral, Kernel::Literal* otherLiteral, bool reverseOther, Kernel::Substitution& substitution) {
    if (extLiteral == nullptr
      || otherLiteral == nullptr
      || !extLiteral->isEquality()
      || !extLiteral->isPositive()
      || !otherLiteral->isEquality()
      || otherLiteral->isPositive()) {
      return false;
    }
    Kernel::TermList extLeft = *extLiteral->nthArgument(0);
    Kernel::TermList extRight = *extLiteral->nthArgument(1);
    if (!extLeft.isVar() || !extRight.isVar()) {
      return false;
    }
    substitution.bind(extLeft.var(), *otherLiteral->nthArgument(reverseOther ? 1 : 0));
    substitution.bind(extRight.var(), *otherLiteral->nthArgument(reverseOther ? 0 : 1));
    return true;
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };

  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }

  struct SymmetryFlip {
    bool extParent;
    std::string literal;
    std::string swapped;
  };

  for (std::size_t extIndex = 0; extIndex < 2; ++extIndex) {
    std::size_t otherIndex = extIndex == 0 ? 1 : 0;
    Kernel::Clause* extParent = parents[extIndex];
    Kernel::Clause* otherParent = parents[otherIndex];
    for (Kernel::Literal* extLiteral : extParent->iterLits()) {
      for (Kernel::Literal* otherLiteral : otherParent->iterLits()) {
        for (bool reverseOther : {false, true}) {
        Kernel::Substitution extSubstitution;
        if (!tryBuildSubstitution(extLiteral, otherLiteral, reverseOther, extSubstitution)) {
          continue;
        }

        std::vector<std::string> rawExt;
        std::vector<std::string> rawPivotExt;
        std::vector<std::string> currentExt;
        std::vector<std::string> currentOther;
        std::string pivotExt;
        std::string pivotOther;
        if (!appendCertificateClauseLiteralsSexpr(extParent, rawExt)
          || !certificateLiteralSexpr(extLiteral, pivotExt)
          || !applyRenderedSubstitution(rawExt, extSubstitution, currentExt)
          || !applyRenderedSubstitution(std::vector<std::string>{pivotExt}, extSubstitution, rawPivotExt)
          || !appendCertificateClauseLiteralsSexpr(otherParent, currentOther)
          || !certificateLiteralSexpr(otherLiteral, pivotOther)) {
          return false;
        }
        pivotExt = rawPivotExt[0];
        int reverseOtherPivotIndex = -1;
        if (reverseOther) {
          std::string swappedPivotOther;
          if (!swapEqualityLiteralSexpr(pivotOther, swappedPivotOther)) {
            continue;
          }
          auto pivotIt = std::find(currentOther.begin(), currentOther.end(), pivotOther);
          if (pivotIt == currentOther.end()) {
            continue;
          }
          reverseOtherPivotIndex = static_cast<int>(pivotIt - currentOther.begin());
          *pivotIt = swappedPivotOther;
          pivotOther = swappedPivotOther;
        }

        std::vector<std::string> expected = currentExt;
        std::vector<std::string> otherRemainder = currentOther;
        if (!removeFirst(expected, pivotExt) || !removeFirst(otherRemainder, pivotOther)) {
          continue;
        }
        expected.insert(expected.end(), otherRemainder.begin(), otherRemainder.end());

        std::vector<SymmetryFlip> candidates;
        for (const std::string& literal : expected) {
          std::string swapped;
          if (swapEqualityLiteralSexpr(literal, swapped) && literal != swapped) {
            bool fromExt = std::find(currentExt.begin(), currentExt.end(), literal) != currentExt.end();
            candidates.push_back({fromExt, literal, swapped});
          }
        }
        std::vector<SymmetryFlip> flips;
        for (std::size_t guard = 0; !sameMultiset(expected, actual) && guard < candidates.size(); ++guard) {
          bool changed = false;
          for (const SymmetryFlip& candidate : candidates) {
            if (std::find(actual.begin(), actual.end(), candidate.swapped) == actual.end()) {
              continue;
            }
            auto it = std::find(expected.begin(), expected.end(), candidate.literal);
            if (it == expected.end()) {
              continue;
            }
            *it = candidate.swapped;
            flips.push_back(candidate);
            changed = true;
            break;
          }
          if (!changed) {
            break;
          }
        }
        if (!sameMultiset(expected, actual)) {
          continue;
        }

        const std::string stepBase = "u" + std::to_string(unit->number());
        std::string extParentId = "u" + std::to_string(extParent->number());
        std::string otherParentId = "u" + std::to_string(otherParent->number());
        std::vector<std::string> steps;
        std::string substitution;
        if (!certificateSubstitutionSexpr(extSubstitution, substitution)) {
          return false;
        }
        if (substitution != "(subst)") {
          const std::string substituteId = stepBase + "_subst_ext";
          steps.push_back(
            "(substitute " + sexprQuote(substituteId)
            + " (parent " + sexprQuote(extParentId) + ") "
            + substitution
            + " (result " + clauseSexprFromLiterals(currentExt) + "))");
          extParentId = substituteId;
        }
        if (reverseOtherPivotIndex >= 0) {
          const std::string symmetryId = stepBase + "_symmetry_other_pivot";
          steps.push_back(
            "(equality_symmetry " + sexprQuote(symmetryId)
            + " (parent " + sexprQuote(otherParentId) + ")"
            + " (literal " + std::to_string(reverseOtherPivotIndex) + ")"
            + " (result " + clauseSexprFromLiterals(currentOther) + "))");
          otherParentId = symmetryId;
        }

        std::size_t extSymmetryIndex = 0;
        std::size_t otherSymmetryIndex = 0;
        for (const SymmetryFlip& flip : flips) {
          std::vector<std::string>& clause = flip.extParent ? currentExt : currentOther;
          auto it = std::find(clause.begin(), clause.end(), flip.literal);
          if (it == clause.end()) {
            return false;
          }
          unsigned literalIndex = static_cast<unsigned>(it - clause.begin());
          *it = flip.swapped;
          const std::string symmetryId =
            stepBase + (flip.extParent ? "_symmetry_ext" : "_symmetry_other")
            + std::to_string(flip.extParent ? extSymmetryIndex++ : otherSymmetryIndex++);
          std::string& parentId = flip.extParent ? extParentId : otherParentId;
          steps.push_back(
            "(equality_symmetry " + sexprQuote(symmetryId)
            + " (parent " + sexprQuote(parentId) + ")"
            + " (literal " + std::to_string(literalIndex) + ")"
            + " (result " + clauseSexprFromLiterals(clause) + "))");
          parentId = symmetryId;
        }

        auto extPivotIt = std::find(currentExt.begin(), currentExt.end(), pivotExt);
        auto otherPivotIt = std::find(currentOther.begin(), currentOther.end(), pivotOther);
        if (extPivotIt == currentExt.end() || otherPivotIt == currentOther.end()) {
          return false;
        }
        steps.push_back(
          "(resolve " + sexprQuote(stepBase)
          + " (parents " + sexprQuote(extParentId) + " " + sexprQuote(otherParentId) + ")"
          + " (pivot " + std::to_string(extPivotIt - currentExt.begin())
          + " " + std::to_string(otherPivotIt - currentOther.begin()) + ")"
          + " (result " + clauseSexprFromLiterals(actual) + "))");

        std::ostringstream out;
        for (std::size_t i = 0; i < steps.size(); ++i) {
          if (i != 0) {
            out << "\n  ";
          }
          out << steps[i];
        }
        result = out.str();
        return true;
        }
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateDefinitionRewriteStepsSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::DEFINITION_UNFOLDING) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.size() < 2 || !parents[0]->isClause()) {
    return false;
  }
  for (std::size_t i = 1; i < parents.size(); ++i) {
    if (!parents[i]->isClause()) {
      return false;
    }
  }

  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto clauseSexprFromLiterals =
    [&](const std::vector<Kernel::Literal*>& literals, Kernel::Clause* splitSource) {
      std::ostringstream out;
      out << "(clause";
      for (Kernel::Literal* literal : literals) {
        std::string rendered;
        if (!certificateLiteralSexpr(literal, rendered)) {
          return std::string();
        }
        out << ' ' << rendered;
      }
      std::vector<std::string> splitLiterals;
      if (!appendCertificateSplitLiteralsSexpr(splitSource, splitLiterals)) {
        return std::string();
      }
      for (const std::string& splitLiteral : splitLiterals) {
        out << ' ' << splitLiteral;
      }
      out << ')';
      return out.str();
    };
  auto clauseLiteralsSexpr =
    [&](const std::vector<Kernel::Literal*>& literals, Kernel::Clause* splitSource, std::vector<std::string>& rendered) {
      rendered.clear();
      for (Kernel::Literal* literal : literals) {
        std::string literalSexpr;
        if (!certificateLiteralSexpr(literal, literalSexpr)) {
          return false;
        }
        rendered.push_back(literalSexpr);
      }
      return appendCertificateSplitLiteralsSexpr(splitSource, rendered);
    };
  auto matchTerm =
    [&](auto&& self,
        Kernel::TermList pattern,
        Kernel::TermList target,
        std::map<unsigned, Kernel::TermList>& bindings) -> bool {
      if (pattern.isVar()) {
        auto existing = bindings.find(pattern.var());
        if (existing == bindings.end()) {
          bindings.emplace(pattern.var(), target);
          return true;
        }
        return existing->second == target;
      }
      if (pattern.isApplication() || target.isApplication()) {
        return pattern.isApplication()
          && target.isApplication()
          && self(self, pattern.lhs(), target.lhs(), bindings)
          && self(self, pattern.rhs(), target.rhs(), bindings);
      }
      if (!pattern.isTerm() || !target.isTerm()) {
        return pattern == target;
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned index = 0; index < patternTerm->arity(); ++index) {
        if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), bindings)) {
          return false;
        }
      }
      return true;
    };
  auto instantiateTerm =
    [&](auto&& self,
        Kernel::TermList pattern,
        const std::map<unsigned, Kernel::TermList>& bindings,
        Kernel::TermList& instantiated) -> bool {
      if (pattern.isVar()) {
        auto found = bindings.find(pattern.var());
        instantiated = found == bindings.end() ? pattern : found->second;
        return true;
      }
      if (pattern.isApplication()) {
        Kernel::TermList lhs;
        Kernel::TermList rhs;
        if (!self(self, pattern.lhs(), bindings, lhs)
          || !self(self, pattern.rhs(), bindings, rhs)) {
          return false;
        }
        return safeHolApplication(
          *pattern.term()->nthArgument(0),
          *pattern.term()->nthArgument(1),
          lhs,
          rhs,
          instantiated);
      }
      if (!pattern.isTerm()) {
        instantiated = pattern;
        return true;
      }
      Kernel::Term* patternTerm = pattern.term();
      Stack<Kernel::TermList> args;
      for (unsigned i = 0; i < patternTerm->arity(); ++i) {
        Kernel::TermList arg;
        if (!self(self, *patternTerm->nthArgument(i), bindings, arg)) {
          return false;
        }
        args.push(arg);
      }
      instantiated = patternTerm->isSort()
        ? Kernel::TermList(Kernel::AtomicSort::create(static_cast<Kernel::AtomicSort*>(patternTerm), args.begin()))
        : Kernel::TermList(Kernel::Term::create(patternTerm, args.begin()));
      return true;
    };
  struct DefinitionMatch {
    std::map<unsigned, Kernel::TermList> bindings;
  };
  auto collectMatches =
    [&](auto&& self,
        Kernel::TermList term,
        Kernel::TermList pattern,
        std::vector<DefinitionMatch>& matches) -> void {
      std::map<unsigned, Kernel::TermList> bindings;
      if (matchTerm(matchTerm, pattern, term, bindings)) {
        matches.push_back({bindings});
      }
      if (term.isVar()) {
        return;
      }
      if (term.isApplication()) {
        self(self, term.lhs(), pattern, matches);
        self(self, term.rhs(), pattern, matches);
        return;
      }
      Kernel::Term* termPtr = term.term();
      for (unsigned i = 0; i < termPtr->numTermArguments(); ++i) {
        self(self, termPtr->termArg(i), pattern, matches);
      }
    };
  auto substitutionSexprFromBindings =
    [&](const std::map<unsigned, Kernel::TermList>& bindings, std::string& rendered, bool& nonIdentity) {
      std::vector<std::pair<unsigned, std::string>> items;
      nonIdentity = false;
      for (const auto& binding : bindings) {
        if (binding.second.isVar() && binding.second.var() == binding.first) {
          continue;
        }
        std::string termSexpr;
        if (!certificateTermSexpr(binding.second, termSexpr)) {
          return false;
        }
        nonIdentity = true;
        items.push_back({binding.first, "(" + sexprQuote(variableName(binding.first)) + " " + termSexpr + ")"});
      }
      std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
        return left.first < right.first;
      });
      std::ostringstream out;
      out << "(subst";
      for (const auto& item : items) {
        out << ' ' << item.second;
      }
      out << ')';
      rendered = out.str();
      return true;
    };
  auto substitutedDefinitionClauseSexpr =
    [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::string& rendered) {
      std::ostringstream out;
      out << "(clause";
      for (Kernel::Literal* literal : clause->iterLits()) {
        std::string literalSexpr;
        if (literal->isEquality()) {
          std::string lhs;
          std::string rhs;
          Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(0), substitution);
          Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(1), substitution);
          if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
            return false;
          }
          literalSexpr = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
            + "(AP (AP (TMH \"=\") " + lhs + ") " + rhs + "))";
        } else {
          Kernel::Literal* substitutedLiteral = Kernel::SubstHelper::apply(literal, substitution);
          if (!certificateLiteralSexpr(substitutedLiteral, literalSexpr)) {
            return false;
          }
        }
        out << ' ' << literalSexpr;
      }
      std::vector<std::string> splitLiterals;
      if (!appendCertificateSplitLiteralsSexpr(clause, splitLiterals)) {
        return false;
      }
      for (const std::string& splitLiteral : splitLiterals) {
        out << ' ' << splitLiteral;
      }
      out << ')';
      rendered = out.str();
      return true;
    };

  Kernel::Clause* source = parents[0]->asClause();
  std::vector<Kernel::Literal*> currentClause;
  for (Kernel::Literal* literal : source->iterLits()) {
    currentClause.push_back(literal);
  }
  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }

  const std::string unitId = "u" + std::to_string(unit->number());
  std::string currentParentId = "u" + std::to_string(source->number());
  std::vector<std::string> steps;

  for (std::size_t parentIndex = 1; parentIndex < parents.size(); ++parentIndex) {
    Kernel::Clause* definitionParent = parents[parentIndex]->asClause();
    if (definitionParent->length() != 1) {
      return false;
    }
    Kernel::Literal* definitionEquality = (*definitionParent)[0];
    if (!definitionEquality->isEquality() || !definitionEquality->isPositive()) {
      return false;
    }

    bool foundRewrite = false;
    for (unsigned direction = 0; direction < 2 && !foundRewrite; ++direction) {
      Kernel::TermList patternFrom = *definitionEquality->nthArgument(direction == 0 ? 0 : 1);
      Kernel::TermList patternTo = *definitionEquality->nthArgument(direction == 0 ? 1 : 0);
      for (std::size_t literalIndex = 0; literalIndex < currentClause.size() && !foundRewrite; ++literalIndex) {
        Kernel::Literal* currentLiteral = currentClause[literalIndex];
        std::vector<DefinitionMatch> matches;
        for (unsigned argumentIndex = 0; argumentIndex < currentLiteral->arity(); ++argumentIndex) {
          collectMatches(collectMatches, *currentLiteral->nthArgument(argumentIndex), patternFrom, matches);
        }
        for (const DefinitionMatch& match : matches) {
          Kernel::TermList from;
          Kernel::TermList to;
          if (!instantiateTerm(instantiateTerm, patternFrom, match.bindings, from)
            || !instantiateTerm(instantiateTerm, patternTo, match.bindings, to)) {
            return false;
          }
          Kernel::Literal* rewrittenLiteral = nullptr;
          std::vector<unsigned> nativePosition;
          if (!certificateRewriteLiteralAtMegalodonPosition(currentLiteral, from, to, nativePosition, rewrittenLiteral)) {
            continue;
          }
          std::vector<Kernel::Literal*> nextClause = currentClause;
          nextClause[literalIndex] = rewrittenLiteral;
          std::vector<std::string> nextRendered;
          if (!clauseLiteralsSexpr(nextClause, source, nextRendered)) {
            return false;
          }
          const bool isLast = parentIndex + 1 == parents.size();
          if (isLast && !sameMultiset(nextRendered, actual)) {
            continue;
          }

          std::string definitionParentId = "u" + std::to_string(definitionParent->number());
          std::string definitionSubst;
          bool nonIdentityDefinitionSubstitution = false;
          if (!substitutionSexprFromBindings(match.bindings, definitionSubst, nonIdentityDefinitionSubstitution)) {
            return false;
          }
          if (nonIdentityDefinitionSubstitution) {
            Kernel::Substitution substitution;
            for (const auto& binding : match.bindings) {
              substitution.rebind(binding.first, binding.second);
            }
            std::string substitutedDefinition;
            if (!substitutedDefinitionClauseSexpr(definitionParent, substitution, substitutedDefinition)) {
              return false;
            }
            definitionParentId = unitId + "_def_subst" + std::to_string(parentIndex - 1);
            steps.push_back(
              "(substitute " + sexprQuote(definitionParentId)
              + " (parent " + sexprQuote("u" + std::to_string(definitionParent->number())) + ") "
              + definitionSubst
              + " (result " + substitutedDefinition + "))");
          }

          std::string fromSexpr;
          std::string toSexpr;
          if (!certificateTermSexpr(from, fromSexpr) || !certificateTermSexpr(to, toSexpr)) {
            return false;
          }
          const std::string stepId = isLast ? unitId : unitId + "_def_rewrite" + std::to_string(parentIndex - 1);
          std::string resultClause;
          if (isLast) {
            if (!certificateClauseSexpr(unit->asClause(), resultClause)) {
              return false;
            }
          } else {
            resultClause = clauseSexprFromLiterals(nextClause, source);
          }
          if (resultClause.empty()) {
            return false;
          }
          steps.push_back(
            "(paramodulate " + sexprQuote(stepId)
            + " (equality " + sexprQuote(definitionParentId) + " 0)"
            + " (target " + sexprQuote(currentParentId) + " " + std::to_string(literalIndex) + ") "
            + certificatePositionSexpr(nativePosition)
            + " (from " + fromSexpr + ")"
            + " (to " + toSexpr + ")"
            + " (result " + resultClause + "))");

          currentClause = nextClause;
          currentParentId = stepId;
          foundRewrite = true;
          break;
        }
      }
    }
    if (!foundRewrite) {
      return false;
    }
  }

  std::ostringstream out;
  for (std::size_t i = 0; i < steps.size(); ++i) {
    if (i != 0) {
      out << "\n  ";
    }
    out << steps[i];
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateDefinitionFoldingStepsSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::DEFINITION_FOLDING_TWEE) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return false;
  }
  const auto* foldingExtra = static_cast<const TweeDefinitionFoldingExtra*>(extra);
  if (foldingExtra->steps.empty()) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.size() != foldingExtra->steps.size() + 1 || parents.empty() || !parents[0]->isClause()) {
    return false;
  }
  for (std::size_t i = 1; i < parents.size(); ++i) {
    if (!parents[i]->isClause()) {
      return false;
    }
  }

  auto emitDefinitionRewriteChain = [&]() {
    auto foldingPositionToNative = [](const std::vector<unsigned>& position) {
      std::vector<unsigned> native;
      if (position.empty()) {
        return native;
      }
      if (position[0] == 0) {
        native.push_back(0);
        native.push_back(1);
      } else if (position[0] == 1) {
        native.push_back(1);
      } else {
        native.push_back(position[0]);
      }
      for (std::size_t index = 1; index < position.size(); ++index) {
        if (position[index] == 2) {
          native.push_back(0);
        } else if (position[index] == 3) {
          native.push_back(1);
        } else {
          native.push_back(position[index]);
        }
      }
      return native;
    };
    std::string resultClause;
    if (!certificateClauseSexpr(unit->asClause(), resultClause)) {
      return false;
    }
    std::ostringstream rewrites;
    rewrites << "(rewrites";
    for (std::size_t stepIndex = 0; stepIndex < foldingExtra->steps.size(); ++stepIndex) {
      const auto& step = foldingExtra->steps[stepIndex];
      const std::size_t definitionParentIndex = parents.size() - 1 - stepIndex;
      std::string fromSexpr;
      std::string toSexpr;
      if (!certificateTermSexpr(step.from, fromSexpr) || !certificateTermSexpr(step.to, toSexpr)) {
        return false;
      }
      rewrites
        << " (rewrite"
        << " (definition " << sexprQuote("u" + std::to_string(parents[definitionParentIndex]->number())) << " 0)"
        << " (target_literal " << step.literal << ") "
        << certificatePositionSexpr(foldingPositionToNative(step.position))
        << " (from " << fromSexpr << ")"
        << " (to " << toSexpr << "))";
    }
    rewrites << ')';
    result =
      "(definition_rewrite_chain " + sexprQuote("u" + std::to_string(unit->number()))
      + " (parent " + sexprQuote("u" + std::to_string(parents[0]->number())) + ") "
      + rewrites.str()
      + " (result " + resultClause + "))";
    return true;
  };

  auto firstPositiveEqualityIndex = [](Kernel::Clause* clause, unsigned& index) {
    for (unsigned i = 0; i < clause->length(); ++i) {
      Kernel::Literal* literal = (*clause)[i];
      if (literal->isEquality() && literal->isPositive()) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto clauseSexprFromLiterals = [&](const std::vector<Kernel::Literal*>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (Kernel::Literal* literal : literals) {
      std::string rendered;
      if (!certificateLiteralSexpr(literal, rendered)) {
        return std::string();
      }
      out << ' ' << rendered;
    }
    out << ')';
    return out.str();
  };
  auto substitutionSexprFromBindings =
    [&](const std::map<unsigned, Kernel::TermList>& bindings, std::string& rendered, bool& nonIdentity) {
      std::vector<std::pair<unsigned, std::string>> items;
      nonIdentity = false;
      for (const auto& binding : bindings) {
        if (binding.second.isVar() && binding.second.var() == binding.first) {
          continue;
        }
        std::string termSexpr;
        if (!certificateTermSexpr(binding.second, termSexpr)) {
          return false;
        }
        nonIdentity = true;
        items.push_back({binding.first, "(" + sexprQuote(variableName(binding.first)) + " " + termSexpr + ")"});
      }
      std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
        return left.first < right.first;
      });
      std::ostringstream out;
      out << "(subst";
      for (const auto& item : items) {
        out << ' ' << item.second;
      }
      out << ')';
      rendered = out.str();
      return true;
    };
  auto substitutedClauseSexpr =
    [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::string& rendered) {
      std::ostringstream out;
      out << "(clause";
      for (Kernel::Literal* literal : clause->iterLits()) {
        Kernel::Literal* substitutedLiteral = Kernel::SubstHelper::apply(literal, substitution);
        std::string literalSexpr;
        if (!certificateLiteralSexpr(substitutedLiteral, literalSexpr)) {
          return false;
        }
        out << ' ' << literalSexpr;
      }
      out << ')';
      rendered = out.str();
      return true;
    };
  auto matchTerm =
    [&](auto&& self,
        Kernel::TermList pattern,
        Kernel::TermList target,
        std::map<unsigned, Kernel::TermList>& bindings) -> bool {
      if (pattern.isVar()) {
        auto existing = bindings.find(pattern.var());
        if (existing == bindings.end()) {
          bindings.emplace(pattern.var(), target);
          return true;
        }
        return existing->second == target;
      }
      if (pattern.isApplication() || target.isApplication()) {
        return pattern.isApplication()
          && target.isApplication()
          && self(self, pattern.lhs(), target.lhs(), bindings)
          && self(self, pattern.rhs(), target.rhs(), bindings);
      }
      if (!pattern.isTerm() || !target.isTerm()) {
        return pattern == target;
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned index = 0; index < patternTerm->arity(); ++index) {
        if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), bindings)) {
          return false;
        }
      }
      return true;
    };
  auto definitionEqualitySubstitution =
    [&](Kernel::Literal* equality, Kernel::TermList from, Kernel::TermList to, std::map<unsigned, Kernel::TermList>& bindings) {
      if (equality == nullptr || !equality->isEquality() || !equality->isPositive()) {
        return false;
      }
      std::map<unsigned, Kernel::TermList> trial;
      if (matchTerm(matchTerm, *equality->nthArgument(0), from, trial)
        && matchTerm(matchTerm, *equality->nthArgument(1), to, trial)) {
        bindings = std::move(trial);
        return true;
      }
      trial.clear();
      if (matchTerm(matchTerm, *equality->nthArgument(1), from, trial)
        && matchTerm(matchTerm, *equality->nthArgument(0), to, trial)) {
        bindings = std::move(trial);
        return true;
      }
      return false;
    };

  std::vector<Kernel::Literal*> currentClause;
  for (Kernel::Literal* literal : parents[0]->asClause()->iterLits()) {
    currentClause.push_back(literal);
  }
  std::string currentParentId = "u" + std::to_string(parents[0]->number());
  const std::string unitId = "u" + std::to_string(unit->number());
  std::vector<std::string> steps;

  for (std::size_t stepIndex = 0; stepIndex < foldingExtra->steps.size(); ++stepIndex) {
    const auto& step = foldingExtra->steps[stepIndex];
    if (step.literal >= currentClause.size()) {
      return emitDefinitionRewriteChain();
    }
    const std::size_t definitionParentIndex = parents.size() - 1 - stepIndex;
    Kernel::Clause* definitionParent = parents[definitionParentIndex]->asClause();
    unsigned equalityIndex = 0;
    Kernel::Literal* definitionEquality = nullptr;
    if (firstPositiveEqualityIndex(definitionParent, equalityIndex)) {
      definitionEquality = (*definitionParent)[equalityIndex];
    }

    Kernel::Literal* rewrittenLiteral = nullptr;
    std::vector<unsigned> nativePosition;
    Kernel::TermList from = step.from;
    Kernel::TermList to = step.to;
    if (!certificateRewriteLiteralAtMegalodonPosition(currentClause[step.literal], from, to, nativePosition, rewrittenLiteral)) {
      from = step.to;
      to = step.from;
      if (!certificateRewriteLiteralAtMegalodonPosition(currentClause[step.literal], from, to, nativePosition, rewrittenLiteral)) {
        return emitDefinitionRewriteChain();
      }
    }

    std::vector<Kernel::Literal*> nextClause = currentClause;
    nextClause[step.literal] = rewrittenLiteral;

    std::string fromSexpr;
    std::string toSexpr;
    std::string resultClause;
    const bool isLast = stepIndex + 1 == foldingExtra->steps.size();
    if (!certificateTermSexpr(from, fromSexpr) || !certificateTermSexpr(to, toSexpr)) {
      return emitDefinitionRewriteChain();
    }
    if (isLast) {
      if (!certificateClauseSexpr(unit->asClause(), resultClause)) {
        return emitDefinitionRewriteChain();
      }
    } else {
      resultClause = clauseSexprFromLiterals(nextClause);
      if (resultClause.empty()) {
        return emitDefinitionRewriteChain();
      }
    }

    std::string definitionParentId = "u" + std::to_string(parents[definitionParentIndex]->number());
    std::map<unsigned, Kernel::TermList> definitionBindings;
    if (definitionEquality != nullptr
      && !definitionEqualitySubstitution(definitionEquality, from, to, definitionBindings)) {
      definitionBindings.clear();
    }
    std::string definitionSubst;
    bool nonIdentityDefinitionSubstitution = false;
    if (!substitutionSexprFromBindings(definitionBindings, definitionSubst, nonIdentityDefinitionSubstitution)) {
      return emitDefinitionRewriteChain();
    }
    if (nonIdentityDefinitionSubstitution) {
      Kernel::Substitution substitution;
      for (const auto& binding : definitionBindings) {
        substitution.rebind(binding.first, binding.second);
      }
      std::string substitutedDefinitionClause;
      if (!substitutedClauseSexpr(definitionParent, substitution, substitutedDefinitionClause)) {
        return emitDefinitionRewriteChain();
      }
      definitionParentId = unitId + "_def_subst" + std::to_string(stepIndex);
      steps.push_back(
        "(substitute " + sexprQuote(definitionParentId)
        + " (parent " + sexprQuote("u" + std::to_string(parents[definitionParentIndex]->number())) + ") "
        + definitionSubst
        + " (result " + substitutedDefinitionClause + "))");
    }

    const std::string stepId = isLast ? unitId : unitId + "_paramodulate" + std::to_string(stepIndex);
    steps.push_back(
      "(paramodulate " + sexprQuote(stepId)
      + " (equality " + sexprQuote(definitionParentId) + " " + std::to_string(equalityIndex) + ")"
      + " (target " + sexprQuote(currentParentId) + " " + std::to_string(step.literal) + ") "
      + certificatePositionSexpr(nativePosition)
      + " (from " + fromSexpr + ")"
      + " (to " + toSexpr + ")"
      + " (result " + resultClause + "))");

    currentClause = nextClause;
    currentParentId = stepId;
  }

  std::ostringstream out;
  for (std::size_t i = 0; i < steps.size(); ++i) {
    if (i != 0) {
      out << "\n  ";
    }
    out << steps[i];
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateFoolExhaustivenessStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE) {
    return false;
  }
  std::string clause;
  if (!certificateClauseSexpr(unit->asClause(), clause)) {
    return false;
  }
  result = "(fool_exhaustiveness " + sexprQuote("u" + std::to_string(unit->number()))
    + " (result " + clause + "))";
  return true;
}

bool MegalodonChecker::certificateFoolDistinctnessStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::FOOL_AXIOM_TRUE_NEQ_FALSE) {
    return false;
  }
  std::string clause;
  if (!certificateClauseSexpr(unit->asClause(), clause)) {
    return false;
  }
  result = "(fool_distinctness " + sexprQuote("u" + std::to_string(unit->number()))
    + " (result " + clause + "))";
  return true;
}

bool MegalodonChecker::certificateUnitResultingResolutionStepsSexpr(
  Kernel::Unit* unit,
  std::string& result,
  bool recordSyntheticMetadata,
  std::vector<MegalodonKernelSyntax::PrimitiveStep>* primitiveSteps)
{
  auto fail = [&](const char* reason) {
    if (std::getenv("MEGALODON_CERT_DEBUG") && std::string(reason) != "not urr clause") {
      std::cerr << "megalodon native URR certificate failed for u" << unit->number() << ": " << reason << std::endl;
    }
    return false;
  };
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::UNIT_RESULTING_RESOLUTION) {
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
  for (const auto& trace : urr->steps) {
    if (trace.selected == nullptr
      || trace.selectedSubstituted == nullptr
      || trace.unitParent == nullptr
      || trace.unitSubstituted == nullptr
      || trace.unitParent->length() != 1) {
      return fail("bad trace entry");
    }
  }

  auto dereference = [](Kernel::TermList term, Kernel::Substitution& substitution) {
    Kernel::TermList current = term;
    Kernel::TermList binding;
    while (current.isVar() && substitution.findBinding(current.var(), binding) && binding != current) {
      current = binding;
    }
    return current;
  };
  auto matchTerm = [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, Kernel::Substitution& substitution) -> bool {
    if (pattern.isVar()) {
      Kernel::TermList existing;
      if (!substitution.findBinding(pattern.var(), existing)) {
        substitution.bindUnbound(pattern.var(), target);
        return true;
      }
      existing = dereference(existing, substitution);
      if (existing == target) {
        return true;
      }
      if (existing.isVar()) {
        substitution.rebind(pattern.var(), target);
        return true;
      }
      return false;
    }
    if (pattern.isApplication() || target.isApplication()) {
      return pattern.isApplication()
        && target.isApplication()
        && self(self, pattern.lhs(), target.lhs(), substitution)
        && self(self, pattern.rhs(), target.rhs(), substitution);
    }
    if (!pattern.isTerm()
      || !target.isTerm()
      || pattern.term()->functor() != target.term()->functor()
      || pattern.term()->arity() != target.term()->arity()) {
      return false;
    }
    for (unsigned i = 0; i < pattern.term()->arity(); ++i) {
      if (!self(self, *pattern.term()->nthArgument(i), *target.term()->nthArgument(i), substitution)) {
        return false;
      }
    }
    return true;
  };
  auto cloneSubstitution = [](const Kernel::Substitution& source) {
    Kernel::Substitution copy;
    Kernel::Substitution sourceCopy = source;
    for (auto [var, term] : iterTraits(sourceCopy.items())) {
      copy.bindUnbound(var, term);
    }
    return copy;
  };
  auto matchLiteral = [&](Kernel::Literal* pattern, Kernel::Literal* target, Kernel::Substitution& substitution) {
    if (pattern == nullptr
      || target == nullptr
      || !Kernel::Literal::headersMatch(pattern, target, false)
      || pattern->arity() != target->arity()) {
      return false;
    }
    auto tryOrientation = [&](bool reverseTarget) {
      Kernel::Substitution attempt = cloneSubstitution(substitution);
      for (unsigned i = 0; i < pattern->arity(); ++i) {
        unsigned targetIndex = reverseTarget ? pattern->arity() - 1 - i : i;
        if (!matchTerm(matchTerm, *pattern->nthArgument(i), *target->nthArgument(targetIndex), attempt)) {
          return false;
        }
      }
      substitution = cloneSubstitution(attempt);
      return true;
    };
    if (pattern->isEquality() && pattern->arity() == 2 && tryOrientation(true)) {
      return true;
    }
    return tryOrientation(false);
  };
  auto substitutionSexpr = [&](const Kernel::Substitution& substitution, std::string& rendered, bool& nonIdentity) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    nonIdentity = false;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termSexpr;
      if (!certificateTermSexpr(term, termSexpr)) {
        return false;
      }
      nonIdentity = true;
      items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : items) {
      out << ' ' << item.second;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto renderedLiterals = [&](const std::vector<Kernel::Literal*>& literals, std::vector<std::string>& rendered) {
    rendered.clear();
    for (Kernel::Literal* literal : literals) {
      std::string literalSexpr;
      if (!certificateLiteralSexpr(literal, literalSexpr)) {
        return false;
      }
      rendered.push_back(literalSexpr);
    }
    return true;
  };
  std::vector<std::string> syntheticMetadata;
  auto addSyntheticVariableSorts = [&](const std::string& stepId, const std::vector<Kernel::Literal*>& literals) {
    if (!recordSyntheticMetadata) {
      return;
    }
    Lib::DHMap<unsigned, Kernel::TermList> varSorts;
    for (Kernel::Literal* literal : literals) {
      Kernel::SortHelper::collectVariableSorts(literal, varSorts);
    }
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
    std::ostringstream metadata;
    metadata << "(step_variable_sorts " << sexprQuote(stepId) << " (";
    for (std::size_t i = 0; i < rendered.size(); ++i) {
      if (i != 0) {
        metadata << ' ';
      }
      metadata << sexprQuote(rendered[i].second);
    }
    metadata << "))";
    syntheticMetadata.push_back(metadata.str());
  };
  const std::string unitId = "u" + std::to_string(unit->number());
  auto addSyntheticInstantiationMetadata =
    [&](const std::string& stepId,
        const std::string& parentId,
        const std::vector<std::string>& parentLiterals,
        const std::string& subst,
        const std::vector<std::string>& resultLiterals) {
      if (!recordSyntheticMetadata) {
        return;
      }
      std::string renderedMetadata;
      if (certificateInstantiationKernelMetadataSexpr(
            stepId,
            parentId,
            parentLiterals,
            subst,
            resultLiterals,
            renderedMetadata)) {
        syntheticMetadata.push_back(renderedMetadata);
      }
    };
  auto traceMacroSexpr = [&]() {
    std::string clause;
    if (!certificateClauseSexpr(unit->asClause(), clause)) {
      return fail("urr macro final clause render failed");
    }
    std::vector<std::string> splitLiterals;
    auto appendUniqueSplitLiterals = [&](Kernel::Clause* clause) {
      std::vector<std::string> rendered;
      if (!appendCertificateSplitLiteralsSexpr(clause, rendered)) {
        return false;
      }
      for (const std::string& literal : rendered) {
        if (std::find(splitLiterals.begin(), splitLiterals.end(), literal) == splitLiterals.end()) {
          splitLiterals.push_back(literal);
        }
      }
      return true;
    };
    if (!appendUniqueSplitLiterals(urr->mainParent)) {
      return fail("urr macro main split render failed");
    }
    std::ostringstream out;
    out << "(unit_resulting_resolution " << sexprQuote(unitId)
        << " (main " << sexprQuote("u" + std::to_string(urr->mainParent->number())) << ")"
        << " (trace";
    for (const auto& trace : urr->steps) {
      std::string selected;
      std::string selectedSubstituted;
      std::string unitSubstituted;
      std::vector<std::string> remaining;
      if (!certificateLiteralSexpr(trace.selected, selected)
        || !certificateLiteralSexpr(trace.selectedSubstituted, selectedSubstituted)
        || !certificateLiteralSexpr(trace.unitSubstituted, unitSubstituted)
        || !renderedLiterals(trace.remainingAfter, remaining)
        || !appendUniqueSplitLiterals(trace.unitParent)) {
        return fail("urr macro trace render failed");
      }
      remaining.insert(remaining.end(), splitLiterals.begin(), splitLiterals.end());
      out << " (step"
          << " (unit " << sexprQuote("u" + std::to_string(trace.unitParent->number())) << ")"
          << " (selected " << selected << ")"
          << " (selected_substituted " << selectedSubstituted << ")"
          << " (unit_substituted " << unitSubstituted << ")"
          << " (remaining " << certificateClauseSexprFromRenderedLiterals(remaining) << "))";
    }
    out << ") (result " << clause << "))";
    result = out.str();
    return true;
  };
  auto complementLiteralSexpr = [](const std::string& literal, std::string& complement) {
    if (literal.rfind("(pos ", 0) == 0) {
      complement = "(neg " + literal.substr(5);
      return true;
    }
    if (literal.rfind("(neg ", 0) == 0) {
      complement = "(pos " + literal.substr(5);
      return true;
    }
    return false;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    const std::string typedPosPrefix =
      "(pos (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    const std::string typedNegPrefix =
      "(neg (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    std::string prefix;
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else if (literal.rfind(typedPosPrefix, 0) == 0 || literal.rfind(typedNegPrefix, 0) == 0) {
      const std::string typedPrefix =
        literal.rfind(typedPosPrefix, 0) == 0 ? typedPosPrefix : typedNegPrefix;
      std::size_t typeStart = typedPrefix.size();
      std::size_t typeEnd = std::string::npos;
      if (!termEnd(typeStart, typeEnd)
        || typeEnd + 2 >= literal.size()
        || literal[typeEnd] != ')'
        || literal[typeEnd + 1] != ' ') {
        return false;
      }
      prefix = literal.substr(0, typeEnd + 2);
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };
  auto applyRenderedSubstitution =
    [&](const std::vector<std::string>& source, const Kernel::Substitution& substitution, std::vector<std::string>& rendered) {
      std::vector<std::tuple<unsigned, std::string, std::string>> replacements;
      Kernel::Substitution substitutionCopy = substitution;
      for (auto [var, term] : iterTraits(substitutionCopy.items())) {
        if (term.isVar() && term.var() == var) {
          continue;
        }
        std::string termSexpr;
        if (!certificateTermSexpr(term, termSexpr)) {
          return false;
        }
        replacements.push_back({var, "(TMH " + sexprQuote(variableName(var)) + ")", termSexpr});
      }
      std::sort(replacements.begin(), replacements.end(), [](const auto& left, const auto& right) {
        return std::get<0>(left) < std::get<0>(right);
      });
      rendered = source;
      for (std::string& literal : rendered) {
        for (std::size_t i = 0; i < replacements.size(); ++i) {
          replaceAll(literal, std::get<1>(replacements[i]), "(TMH " + sexprQuote("__mg_subst_" + std::to_string(i)) + ")");
        }
        for (std::size_t i = 0; i < replacements.size(); ++i) {
          replaceAll(literal, "(TMH " + sexprQuote("__mg_subst_" + std::to_string(i)) + ")", std::get<2>(replacements[i]));
        }
      }
      return true;
    };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    return literals;
  };
  auto canonicalizedTraceRemainder = [&](const std::vector<std::string>& literals) {
    std::map<std::string, std::string> variableNames;
    auto canonicalizeVampireVariables = [&](const std::string& literal) {
      std::string rendered;
      for (std::size_t i = 0; i < literal.size();) {
        const std::string prefix = "(TMH \"X";
        if (literal.compare(i, prefix.size(), prefix) == 0) {
          std::size_t end = i + prefix.size();
          while (end < literal.size() && literal[end] >= '0' && literal[end] <= '9') {
            ++end;
          }
          if (end > i + prefix.size()
            && end + 1 < literal.size()
            && literal[end] == '"'
            && literal[end + 1] == ')') {
            std::string name = literal.substr(i + 6, end - (i + 6));
            auto inserted = variableNames.emplace(
              name,
              "__mg_trace_var_" + std::to_string(variableNames.size()));
            rendered += "(TMH \"" + inserted.first->second + "\")";
            i = end + 2;
            continue;
          }
        }
        rendered.push_back(literal[i]);
        ++i;
      }
      return rendered;
    };
    std::vector<std::string> canonical;
    for (const std::string& literal : literals) {
      std::string oriented = literal;
      std::string swapped;
      if (swappedEqualityLiteral(literal, swapped) && swapped < oriented) {
        oriented = swapped;
      }
      canonical.push_back(canonicalizeVampireVariables(oriented));
    }
    std::sort(canonical.begin(), canonical.end());
    return canonical;
  };
  auto literalMultiplicity =
    [](const std::vector<std::string>& literals, const std::string& literal) {
      return static_cast<unsigned>(std::count(literals.begin(), literals.end(), literal));
    };
  auto swapEqualityLiteral = [&](Kernel::Literal* literal) -> Kernel::Literal* {
    if (literal == nullptr || !literal->isEquality()) {
      return nullptr;
    }
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    return Kernel::Literal::createEquality(
      literal->isPositive(),
      *positive->nthArgument(1),
      *positive->nthArgument(0),
      Kernel::SortHelper::getEqualityArgumentSort(positive));
  };
  auto applyLiteralPreservingEquality = [](Kernel::Literal* literal, const Kernel::Substitution& substitution) {
    if (literal == nullptr || !literal->isEquality()) {
      return Kernel::SubstHelper::apply(literal, substitution);
    }
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    Kernel::TermList lhs = Kernel::SubstHelper::apply(*literal->nthArgument(0), substitution);
    Kernel::TermList rhs = Kernel::SubstHelper::apply(*literal->nthArgument(1), substitution);
    return Kernel::Literal::createEquality(
      literal->isPositive(),
      lhs,
      rhs,
      Kernel::SortHelper::getEqualityArgumentSort(positive));
  };
  auto samePolarityAndAtom = [&](Kernel::Literal* left, Kernel::Literal* right) {
    if (left == nullptr || right == nullptr || left->isPositive() != right->isPositive()) {
      return false;
    }
    std::string leftRendered;
    std::string rightRendered;
    return certificateLiteralSexpr(left, leftRendered)
      && certificateLiteralSexpr(right, rightRendered)
      && leftRendered == rightRendered;
  };

  std::vector<Kernel::Literal*> currentLiterals;
  for (Kernel::Literal* literal : urr->mainParent->iterLits()) {
    currentLiterals.push_back(literal);
  }
  std::vector<std::string> currentRendered;
  if (!appendCertificateClauseLiteralsSexpr(urr->mainParent, currentRendered)) {
    return false;
  }
  std::string currentParentId = "u" + std::to_string(urr->mainParent->number());
  std::vector<MegalodonKernelSyntax::PrimitiveStep> localPrimitiveSteps;
  auto addPrimitiveStep =
    [&](const std::string& rule,
        const std::string& stepId,
        const std::vector<std::string>& parentIds,
        const std::string& resultClause,
        const std::vector<std::pair<std::string, std::string>>& fields,
        const std::string& rendered) {
      localPrimitiveSteps.push_back(
        MegalodonKernelSyntax::primitiveClauseStep(
          rule,
          stepId,
          parentIds,
          resultClause,
          fields,
          rendered));
    };
  std::string previousTraceSelectedLiteralSexpr;

  for (std::size_t traceIndex = 0; traceIndex < urr->steps.size(); ++traceIndex) {
    const auto& trace = urr->steps[traceIndex];
    Kernel::Substitution currentSubstitution;
    int selectedIndex = -1;
    std::string traceSelectedLiteralSexpr;
    if (!certificateLiteralSexpr(trace.selected, traceSelectedLiteralSexpr)) {
      return fail("trace selected literal render failed");
    }
    const bool repeatedTraceSelection =
      traceIndex > 0 && traceSelectedLiteralSexpr == previousTraceSelectedLiteralSexpr;
    const bool bareVariableEqualitySelection =
      trace.selected->isEquality()
      && (trace.selected->nthArgument(0)->isVar() || trace.selected->nthArgument(1)->isVar());
    unsigned selectionPasses = (repeatedTraceSelection || bareVariableEqualitySelection) ? 1 : 2;
    for (unsigned pass = 0; pass < selectionPasses && selectedIndex < 0; ++pass) {
      for (std::size_t offset = 0; offset < currentLiterals.size(); ++offset) {
        std::size_t i = repeatedTraceSelection ? currentLiterals.size() - 1 - offset : offset;
        if (selectionPasses == 2 && pass == 0) {
          std::string currentLiteralSexpr;
          if (!certificateLiteralSexpr(currentLiterals[i], currentLiteralSexpr)
            || currentLiteralSexpr != traceSelectedLiteralSexpr) {
            continue;
          }
        }
        Kernel::Substitution attempt;
        if (matchLiteral(currentLiterals[i], trace.selectedSubstituted, attempt)) {
          currentSubstitution = cloneSubstitution(attempt);
          selectedIndex = static_cast<int>(i);
          break;
        }
      }
    }
    if (selectedIndex < 0) {
      for (std::size_t i = 0; i < currentLiterals.size(); ++i) {
        std::string currentLiteralSexpr;
        Kernel::Substitution attempt;
        if (certificateLiteralSexpr(currentLiterals[i], currentLiteralSexpr)
          && currentLiteralSexpr == traceSelectedLiteralSexpr
          && matchLiteral(trace.selected, trace.selectedSubstituted, attempt)) {
          currentSubstitution = cloneSubstitution(attempt);
          selectedIndex = static_cast<int>(i);
          break;
        }
      }
    }
    if (!trace.remainingAfter.empty() || currentLiterals.size() == 1) {
      std::vector<std::string> expectedRemaining;
      if (!renderedLiterals(trace.remainingAfter, expectedRemaining)) {
        return fail("trace remaining render failed");
      }
      const std::vector<std::string> normalizedExpectedRemaining = normalized(expectedRemaining);
      const std::vector<std::string> canonicalExpectedRemaining = canonicalizedTraceRemainder(expectedRemaining);
      for (std::size_t i = 0; i < currentLiterals.size(); ++i) {
        Kernel::Substitution attempt;
        if (!matchLiteral(currentLiterals[i], trace.selectedSubstituted, attempt)) {
          continue;
        }
        std::vector<Kernel::Literal*> substituted;
        for (Kernel::Literal* literal : currentLiterals) {
          substituted.push_back(applyLiteralPreservingEquality(literal, attempt));
        }
        std::vector<std::string> remaining;
        for (std::size_t j = 0; j < substituted.size(); ++j) {
          if (i == j) {
            continue;
          }
          std::string literalSexpr;
          if (!certificateLiteralSexpr(substituted[j], literalSexpr)) {
            return fail("candidate remaining render failed");
          }
          remaining.push_back(literalSexpr);
        }
        if (normalized(remaining) == normalizedExpectedRemaining
          || canonicalizedTraceRemainder(remaining) == canonicalExpectedRemaining) {
          currentSubstitution = cloneSubstitution(attempt);
          selectedIndex = static_cast<int>(i);
          break;
        }
      }
    }
    if (selectedIndex < 0) {
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << "megalodon native URR trace " << traceIndex
                  << " selected for u" << unit->number()
                  << ": " << traceSelectedLiteralSexpr << std::endl;
        std::string traceSelectedSubstitutedSexpr;
        if (certificateLiteralSexpr(trace.selectedSubstituted, traceSelectedSubstitutedSexpr)) {
          std::cerr << "megalodon native URR trace " << traceIndex
                    << " selected substituted for u" << unit->number()
                    << ": " << traceSelectedSubstitutedSexpr << std::endl;
        }
        std::cerr << "megalodon native URR current for u" << unit->number()
                  << ": " << certificateClauseSexprFromRenderedLiterals(currentRendered) << std::endl;
      }
      if (traceMacroSexpr()) {
        return true;
      }
      return fail("current substitution match failed");
    }
    previousTraceSelectedLiteralSexpr = traceSelectedLiteralSexpr;

    std::string subst;
    bool nonIdentity = false;
    if (!substitutionSexpr(currentSubstitution, subst, nonIdentity)) {
      return fail("current substitution render failed");
    }
    if (nonIdentity) {
      std::vector<Kernel::Literal*> substituted;
      for (Kernel::Literal* literal : currentLiterals) {
        substituted.push_back(applyLiteralPreservingEquality(literal, currentSubstitution));
      }
      std::vector<std::string> substitutedRendered;
      if (!applyRenderedSubstitution(currentRendered, currentSubstitution, substitutedRendered)) {
        return fail("current substituted clause render failed");
      }
      const std::string substituteId = unitId + "_current_subst" + std::to_string(traceIndex);
      const std::string substituteResultClause =
        certificateClauseSexprFromRenderedLiterals(substitutedRendered);
      addPrimitiveStep(
        "substitute",
        substituteId,
        {currentParentId},
        substituteResultClause,
        {{"substitution", subst}},
        "(substitute " + sexprQuote(substituteId)
        + " (parent " + sexprQuote(currentParentId) + ") "
        + subst
        + " (result " + substituteResultClause + "))");
      addSyntheticInstantiationMetadata(
        substituteId,
        currentParentId,
        currentRendered,
        subst,
        substitutedRendered);
      addSyntheticVariableSorts(substituteId, substituted);
      currentLiterals = substituted;
      currentRendered = substitutedRendered;
      currentParentId = substituteId;
    }

    Kernel::Literal* selectedLiteral = currentLiterals[selectedIndex];
    if (!samePolarityAndAtom(selectedLiteral, trace.selectedSubstituted)) {
      Kernel::Literal* swapped = swapEqualityLiteral(selectedLiteral);
      if (!samePolarityAndAtom(swapped, trace.selectedSubstituted)) {
        return fail("selected substituted literal mismatch");
      }
      std::vector<Kernel::Literal*> symmetryClause = currentLiterals;
      symmetryClause[selectedIndex] = swapped;
      std::string swappedRendered;
      if (!certificateLiteralSexpr(swapped, swappedRendered)) {
        return fail("selected symmetry render failed");
      }
      std::vector<std::string> symmetryRendered = currentRendered;
      symmetryRendered[selectedIndex] = swappedRendered;
      const std::string symmetryId = unitId + "_current_symmetry" + std::to_string(traceIndex);
      const std::string symmetryResultClause =
        certificateClauseSexprFromRenderedLiterals(symmetryRendered);
      addPrimitiveStep(
        "equality_symmetry",
        symmetryId,
        {currentParentId},
        symmetryResultClause,
        {{"literal", std::to_string(selectedIndex)}},
        "(equality_symmetry " + sexprQuote(symmetryId)
        + " (parent " + sexprQuote(currentParentId) + ")"
        + " (literal " + std::to_string(selectedIndex) + ")"
        + " (result " + symmetryResultClause + "))");
      addSyntheticVariableSorts(symmetryId, symmetryClause);
      currentLiterals = symmetryClause;
      currentRendered = symmetryRendered;
      currentParentId = symmetryId;
      selectedLiteral = currentLiterals[selectedIndex];
    }

    Kernel::Clause* unitParent = trace.unitParent;
    Kernel::Literal* unitLiteral = (*unitParent)[0];
    Kernel::Substitution unitSubstitution;
    if (!matchLiteral(unitLiteral, trace.unitSubstituted, unitSubstitution)) {
      return fail("unit substitution match failed");
    }
    if (!substitutionSexpr(unitSubstitution, subst, nonIdentity)) {
      return fail("unit substitution render failed");
    }
    std::vector<Kernel::Literal*> unitLiterals = { applyLiteralPreservingEquality(unitLiteral, unitSubstitution) };
    std::vector<std::string> unitRendered;
    if (nonIdentity) {
      std::vector<std::string> unitSourceRendered;
      if (!renderedLiterals(std::vector<Kernel::Literal*>{unitLiteral}, unitSourceRendered)
        || !applyRenderedSubstitution(unitSourceRendered, unitSubstitution, unitRendered)) {
        return fail("unit substituted clause render failed");
      }
      if (!appendCertificateSplitLiteralsSexpr(unitParent, unitRendered)) {
        return fail("unit split literal render failed");
      }
    } else {
      if (!appendCertificateClauseLiteralsSexpr(unitParent, unitRendered)) {
        return fail("unit clause render failed");
      }
    }
    std::string unitParentId = "u" + std::to_string(unitParent->number());
    if (nonIdentity) {
      const std::string substituteId = unitId + "_unit_subst" + std::to_string(traceIndex);
      std::string substituteStep;
      if (!certificateSubstituteStepSexpr(
            substituteId,
            unitParentId,
            unitParent,
            unitSubstitution,
            substituteStep)) {
        return fail("unit substitute step render failed");
      }
      addPrimitiveStep(
        "substitute",
        substituteId,
        {unitParentId},
        certificateClauseSexprFromRenderedLiterals(unitRendered),
        {{"substitution", subst}},
        substituteStep);
      addSyntheticVariableSorts(substituteId, unitLiterals);
      unitParentId = substituteId;
    }

    auto selectedComplementMatchesUnit = [&]() {
      std::string complement;
      return !unitRendered.empty()
        && complementLiteralSexpr(currentRendered[selectedIndex], complement)
        && complement == unitRendered[0];
    };

    if (!selectedComplementMatchesUnit()) {
      Kernel::Literal* swapped = swapEqualityLiteral(selectedLiteral);
      std::string swappedRendered;
      std::string swappedComplement;
      if (swapped != nullptr
        && !unitRendered.empty()
        && certificateLiteralSexpr(swapped, swappedRendered)
        && complementLiteralSexpr(swappedRendered, swappedComplement)
        && swappedComplement == unitRendered[0]) {
        currentLiterals[selectedIndex] = swapped;
        currentRendered[selectedIndex] = swappedRendered;
        const std::string symmetryId = unitId + "_current_pivot_symmetry" + std::to_string(traceIndex);
        const std::string symmetryResultClause =
          certificateClauseSexprFromRenderedLiterals(currentRendered);
        addPrimitiveStep(
          "equality_symmetry",
          symmetryId,
          {currentParentId},
          symmetryResultClause,
          {{"literal", std::to_string(selectedIndex)}},
          "(equality_symmetry " + sexprQuote(symmetryId)
          + " (parent " + sexprQuote(currentParentId) + ")"
          + " (literal " + std::to_string(selectedIndex) + ")"
          + " (result " + symmetryResultClause + "))");
        addSyntheticVariableSorts(symmetryId, currentLiterals);
        currentParentId = symmetryId;
        selectedLiteral = currentLiterals[selectedIndex];
      }
    }

    if (!selectedComplementMatchesUnit()) {
      Kernel::Literal* swapped = swapEqualityLiteral(unitLiterals[0]);
      std::string selectedComplement;
      std::string swappedRendered;
      if (swapped == nullptr
        || !complementLiteralSexpr(currentRendered[selectedIndex], selectedComplement)
        || !certificateLiteralSexpr(swapped, swappedRendered)
        || selectedComplement != swappedRendered) {
        return fail("unit pivot symmetry mismatch");
      }
      unitLiterals[0] = swapped;
      unitRendered[0] = swappedRendered;
      const std::string symmetryId = unitId + "_unit_symmetry" + std::to_string(traceIndex);
      const std::string symmetryResultClause =
        certificateClauseSexprFromRenderedLiterals(unitRendered);
      addPrimitiveStep(
        "equality_symmetry",
        symmetryId,
        {unitParentId},
        symmetryResultClause,
        {{"literal", "0"}},
        "(equality_symmetry " + sexprQuote(symmetryId)
        + " (parent " + sexprQuote(unitParentId) + ")"
        + " (literal 0)"
        + " (result " + symmetryResultClause + "))");
      addSyntheticVariableSorts(symmetryId, unitLiterals);
      unitParentId = symmetryId;
    }

    std::vector<Kernel::Literal*> nextLiterals = currentLiterals;
    nextLiterals.erase(nextLiterals.begin() + selectedIndex);
    std::vector<std::string> nextRendered = currentRendered;
    nextRendered.erase(nextRendered.begin() + selectedIndex);
    if (!appendCertificateSplitLiteralsSexpr(unitParent, nextRendered)) {
      return fail("post-resolve split append failed");
    }
    const std::string resolveId = unitId + "_resolve" + std::to_string(traceIndex);
    const std::string resolveResultClause =
      certificateClauseSexprFromRenderedLiterals(nextRendered);
    addPrimitiveStep(
      "resolve",
      resolveId,
      {currentParentId, unitParentId},
      resolveResultClause,
      {{"pivot_left", std::to_string(selectedIndex)}, {"pivot_right", "0"}},
      "(resolve " + sexprQuote(resolveId)
      + " (parents " + sexprQuote(currentParentId) + " " + sexprQuote(unitParentId) + ")"
      + " (pivot " + std::to_string(selectedIndex) + " 0)"
      + " (result " + resolveResultClause + "))");
    addSyntheticVariableSorts(resolveId, nextLiterals);
    currentLiterals = nextLiterals;
    currentRendered = nextRendered;
    currentParentId = resolveId;
  }

  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return fail("actual clause render failed");
  }
  std::vector<std::string> current = currentRendered;
  if (normalized(current) != normalized(actual)) {
    Kernel::Substitution finalRenameSubstitution;
    std::vector<bool> usedActual(unit->asClause()->length(), false);
    bool finalRenameMatched = currentLiterals.size() == unit->asClause()->length();
    if (finalRenameMatched) {
      for (Kernel::Literal* currentLiteral : currentLiterals) {
        bool matched = false;
        for (unsigned actualIndex = 0; actualIndex < unit->asClause()->length(); ++actualIndex) {
          if (usedActual[actualIndex]) {
            continue;
          }
          Kernel::Substitution attempt = cloneSubstitution(finalRenameSubstitution);
          if (!matchLiteral(currentLiteral, (*unit->asClause())[actualIndex], attempt)) {
            continue;
          }
          finalRenameSubstitution = cloneSubstitution(attempt);
          usedActual[actualIndex] = true;
          matched = true;
          break;
        }
        if (!matched) {
          finalRenameMatched = false;
          break;
        }
      }
    }
    if (finalRenameMatched) {
      std::string finalRenameSubst;
      bool finalRenameNonIdentity = false;
      if (!substitutionSexpr(finalRenameSubstitution, finalRenameSubst, finalRenameNonIdentity)) {
        return fail("final rename substitution render failed");
      }
      if (finalRenameNonIdentity) {
        std::vector<Kernel::Literal*> renamedLiterals;
        for (Kernel::Literal* literal : currentLiterals) {
          renamedLiterals.push_back(applyLiteralPreservingEquality(literal, finalRenameSubstitution));
        }
        std::vector<std::string> renamedRendered;
        if (!applyRenderedSubstitution(currentRendered, finalRenameSubstitution, renamedRendered)) {
          return fail("final rename clause render failed");
        }
        const std::string renameId = unitId + "_final_rename";
        const std::string renameResultClause =
          certificateClauseSexprFromRenderedLiterals(renamedRendered);
        addPrimitiveStep(
          "substitute",
          renameId,
          {currentParentId},
          renameResultClause,
          {{"substitution", finalRenameSubst}},
          "(substitute " + sexprQuote(renameId)
          + " (parent " + sexprQuote(currentParentId) + ") "
          + finalRenameSubst
          + " (result " + renameResultClause + "))");
        addSyntheticInstantiationMetadata(
          renameId,
          currentParentId,
          currentRendered,
          finalRenameSubst,
          renamedRendered);
        addSyntheticVariableSorts(renameId, renamedLiterals);
        currentLiterals = renamedLiterals;
        currentRendered = renamedRendered;
        current = renamedRendered;
        currentParentId = renameId;
      }
    }
  }
  unsigned finalFactorCount = 0;
  auto factorFinalDuplicate = [&]() {
    for (unsigned left = 0; left < current.size(); ++left) {
      for (unsigned right = left + 1; right < current.size(); ++right) {
        if (current[left] != current[right]
          || literalMultiplicity(current, current[left]) <= literalMultiplicity(actual, current[left])) {
          continue;
        }
        std::vector<std::string> factored = current;
        factored.erase(factored.begin() + right);
        const std::string factorId = unitId + "_final_factor" + std::to_string(finalFactorCount++);
        const std::string factorResultClause =
          certificateClauseSexprFromRenderedLiterals(factored);
        addPrimitiveStep(
          "factor",
          factorId,
          {currentParentId},
          factorResultClause,
          {{"literal_left", std::to_string(left)}, {"literal_right", std::to_string(right)}},
          "(factor " + sexprQuote(factorId)
          + " (parent " + sexprQuote(currentParentId) + ")"
          + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
          + " (result " + factorResultClause + "))");
        if (right < currentLiterals.size()) {
          currentLiterals.erase(currentLiterals.begin() + right);
        }
        addSyntheticVariableSorts(factorId, currentLiterals);
        current = factored;
        currentRendered = factored;
        currentParentId = factorId;
        return true;
      }
    }
    return false;
  };
  while (normalized(current) != normalized(actual) && factorFinalDuplicate()) {
  }
  for (std::size_t guard = 0; normalized(current) != normalized(actual) && guard < current.size(); ++guard) {
    bool changed = false;
    std::string swappedRendered;
    for (std::size_t i = 0; i < current.size(); ++i) {
      if (!swappedEqualityLiteral(current[i], swappedRendered)) {
        continue;
      }
      std::vector<std::string> candidate = currentRendered;
      candidate[i] = swappedRendered;
      if (normalized(candidate) == normalized(actual)) {
        const std::string symmetryId = unitId + "_final_symmetry" + std::to_string(guard);
        const std::string symmetryResultClause =
          certificateClauseSexprFromRenderedLiterals(candidate);
        addPrimitiveStep(
          "equality_symmetry",
          symmetryId,
          {currentParentId},
          symmetryResultClause,
          {{"literal", std::to_string(i)}},
          "(equality_symmetry " + sexprQuote(symmetryId)
          + " (parent " + sexprQuote(currentParentId) + ")"
          + " (literal " + std::to_string(i) + ")"
          + " (result " + symmetryResultClause + "))");
        addSyntheticVariableSorts(symmetryId, currentLiterals);
        current = candidate;
        currentRendered = candidate;
        currentParentId = symmetryId;
        changed = true;
        break;
      }
    }
    if (!changed) {
      break;
    }
    while (normalized(current) != normalized(actual) && factorFinalDuplicate()) {
    }
  }
  if (normalized(current) != normalized(actual)) {
    if (std::getenv("MEGALODON_CERT_DEBUG")) {
      std::cerr << "megalodon native URR current for u" << unit->number()
                << ": " << certificateClauseSexprFromRenderedLiterals(normalized(current)) << std::endl;
      std::cerr << "megalodon native URR actual for u" << unit->number()
                << ": " << certificateClauseSexprFromRenderedLiterals(normalized(actual)) << std::endl;
    }
    if (traceMacroSexpr()) {
      return true;
    }
    return fail("sequential urr replay did not reach conclusion");
  }
  if (currentParentId != unitId) {
    std::string clause;
    if (!certificateClauseSexpr(unit->asClause(), clause)) {
      return fail("final clause render failed");
    }
    addPrimitiveStep(
      "substitute",
      unitId,
      {currentParentId},
      clause,
      {{"substitution", "(subst)"}},
      "(substitute " + sexprQuote(unitId)
      + " (parent " + sexprQuote(currentParentId) + ")"
      + " (subst)"
      + " (result " + clause + "))");
  }

  std::ostringstream out;
  for (std::size_t i = 0; i < localPrimitiveSteps.size(); ++i) {
    if (i != 0) {
      out << "\n  ";
    }
    out << localPrimitiveSteps[i].rendered;
  }
  result = out.str();
  if (primitiveSteps != nullptr) {
    *primitiveSteps = localPrimitiveSteps;
  }
  if (recordSyntheticMetadata) {
    _certificateNativeMetadata.insert(
      _certificateNativeMetadata.end(),
      syntheticMetadata.begin(),
      syntheticMetadata.end());
  }
  return true;
}

bool MegalodonChecker::certificateResolveStepSexpr(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::RESOLUTION
      && rule != Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::FORWARD_LITERAL_REWRITING
    )) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);

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
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto literalMultiplicity =
    [](const std::vector<std::string>& literals, const std::string& literal) {
      return static_cast<unsigned>(std::count(literals.begin(), literals.end(), literal));
    };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    const std::string typedPosPrefix =
      "(pos (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    const std::string typedNegPrefix =
      "(neg (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else if (literal.rfind(typedPosPrefix, 0) == 0 || literal.rfind(typedNegPrefix, 0) == 0) {
      const std::string typedPrefix =
        literal.rfind(typedPosPrefix, 0) == 0 ? typedPosPrefix : typedNegPrefix;
      std::size_t typeStart = typedPrefix.size();
      std::size_t typeEnd = std::string::npos;
      auto termEnd = [&](std::size_t start, std::size_t& end) {
        int depth = 0;
        for (std::size_t i = start; i < literal.size(); ++i) {
          if (literal[i] == '(') {
            ++depth;
          } else if (literal[i] == ')') {
            --depth;
            if (depth == 0) {
              end = i + 1;
              return true;
            }
          }
        }
        return false;
      };
      if (!termEnd(typeStart, typeEnd) || typeEnd + 2 >= literal.size()
        || literal[typeEnd] != ')' || literal[typeEnd + 1] != ' ') {
        return false;
      }
      prefix = literal.substr(0, typeEnd + 2);
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto complementaryLiteralSexpr = [](const std::string& left, const std::string& right) {
    const std::string posPrefix = "(pos ";
    const std::string negPrefix = "(neg ";
    if (left.rfind(posPrefix, 0) == 0 && right.rfind(negPrefix, 0) == 0) {
      return left.substr(posPrefix.size()) == right.substr(negPrefix.size());
    }
    if (left.rfind(negPrefix, 0) == 0 && right.rfind(posPrefix, 0) == 0) {
      return left.substr(negPrefix.size()) == right.substr(posPrefix.size());
    }
    return false;
  };
  auto complementary = [&](Kernel::Literal* left, Kernel::Literal* right) {
    if (left == nullptr || right == nullptr || left->isPositive() == right->isPositive()) {
      return false;
    }
    std::string leftAtom;
    std::string rightAtom;
    return certificateAtomSexpr(left, leftAtom)
      && certificateAtomSexpr(right, rightAtom)
      && leftAtom == rightAtom;
  };
  auto stepForOrientation = [&](Kernel::Literal* leftPivot, Kernel::Literal* rightPivot, std::string& step) {
    if (!containsLiteral(parents[0], leftPivot)
      || !containsLiteral(parents[1], rightPivot)
      || leftPivot == nullptr
      || rightPivot == nullptr
      || leftPivot->isPositive() == rightPivot->isPositive()) {
      return false;
    }
    std::string leftPivotLiteral;
    std::string rightPivotLiteral;
    if (!certificateLiteralSexpr(leftPivot, leftPivotLiteral)
      || !certificateLiteralSexpr(rightPivot, rightPivotLiteral)) {
      return false;
    }
    std::vector<std::string> leftParentLiterals;
    std::vector<std::string> rightParentLiterals;
    if (!appendCertificateClauseLiteralsSexpr(parents[0], leftParentLiterals)
      || !appendCertificateClauseLiteralsSexpr(parents[1], rightParentLiterals)) {
      return false;
    }
    auto renderedLiteralIndex =
      [](const std::vector<std::string>& literals, const std::string& literal, unsigned& index) {
        for (unsigned i = 0; i < literals.size(); ++i) {
          if (literals[i] == literal) {
            index = i;
            return true;
          }
        }
        return false;
      };
    unsigned leftIndex = 0;
    unsigned rightIndex = 0;
    if (!renderedLiteralIndex(leftParentLiterals, leftPivotLiteral, leftIndex)
      || !renderedLiteralIndex(rightParentLiterals, rightPivotLiteral, rightIndex)) {
      return false;
    }
    std::vector<std::string> expected = leftParentLiterals;
    expected.erase(expected.begin() + leftIndex);
    expected.insert(expected.end(), rightParentLiterals.begin(), rightParentLiterals.end());
    expected.erase(expected.begin() + (leftParentLiterals.size() - 1) + rightIndex);
    std::vector<std::string> actual;
    if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
      return false;
    }
    const bool exactResult = sameMultiset(expected, actual);
    if (!exactResult && normalized(expected) != normalized(actual)) {
      return false;
    }
    bool flipLeftPivot = false;
    bool flipRightPivot = false;
    std::string flippedLeftPivotLiteral;
    std::string flippedRightPivotLiteral;
    if (!complementaryLiteralSexpr(leftPivotLiteral, rightPivotLiteral)) {
      if (swappedEqualityLiteral(leftPivotLiteral, flippedLeftPivotLiteral)
        && complementaryLiteralSexpr(flippedLeftPivotLiteral, rightPivotLiteral)) {
        flipLeftPivot = true;
      } else if (swappedEqualityLiteral(rightPivotLiteral, flippedRightPivotLiteral)
        && complementaryLiteralSexpr(leftPivotLiteral, flippedRightPivotLiteral)) {
        flipRightPivot = true;
      } else {
        return false;
      }
    }
    const std::string stepBase = "u" + std::to_string(unit->number());
    const std::string resolveId = exactResult ? stepBase : stepBase + "_resolve";
    std::vector<std::string> steps;
    std::string leftParentId = "u" + std::to_string(parents[0]->number());
    std::string rightParentId = "u" + std::to_string(parents[1]->number());
    auto emitPivotSymmetry =
      [&](Kernel::Clause* parent,
          unsigned pivotIndex,
          const std::string& flippedLiteral,
          const std::string& symmetryId,
          std::string& parentId) {
        std::vector<std::string> parentLiterals;
        if (!appendCertificateClauseLiteralsSexpr(parent, parentLiterals)
          || pivotIndex >= parentLiterals.size()) {
          return false;
        }
        parentLiterals[pivotIndex] = flippedLiteral;
        steps.push_back(
          "(equality_symmetry " + sexprQuote(symmetryId)
          + " (parent " + sexprQuote(parentId) + ")"
          + " (literal " + std::to_string(pivotIndex) + ")"
          + " (result " + clauseSexprFromLiterals(parentLiterals) + "))");
        parentId = symmetryId;
        return true;
      };
    if (flipLeftPivot
      && !emitPivotSymmetry(parents[0], leftIndex, flippedLeftPivotLiteral, stepBase + "_left_symmetry", leftParentId)) {
      return false;
    }
    if (flipRightPivot
      && !emitPivotSymmetry(parents[1], rightIndex, flippedRightPivotLiteral, stepBase + "_right_symmetry", rightParentId)) {
      return false;
    }
    steps.push_back(
      "(resolve " + sexprQuote(resolveId)
      + " (parents " + sexprQuote(leftParentId)
      + " " + sexprQuote(rightParentId) + ")"
      + " (pivot " + std::to_string(leftIndex) + " " + std::to_string(rightIndex) + ")"
      + " (result " + clauseSexprFromLiterals(exactResult ? actual : expected) + "))");
    if (!exactResult) {
      std::vector<std::string> current = expected;
      std::string currentParentId = resolveId;
      unsigned factorCount = 0;
      while (!sameMultiset(current, actual)) {
        bool factored = false;
        for (unsigned left = 0; left < current.size() && !factored; ++left) {
          for (unsigned right = left + 1; right < current.size(); ++right) {
            if (current[left] != current[right]) {
              continue;
            }
            if (literalMultiplicity(current, current[left]) <= literalMultiplicity(actual, current[left])) {
              continue;
            }
            std::vector<std::string> candidate = current;
            candidate.erase(candidate.begin() + right);
            if (normalized(candidate) != normalized(actual)) {
              continue;
            }
            const std::string factorId = stepBase + "_factor" + std::to_string(factorCount++);
            steps.push_back(
              "(factor " + sexprQuote(factorId)
              + " (parent " + sexprQuote(currentParentId) + ")"
              + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
              + " (result " + clauseSexprFromLiterals(candidate) + "))");
            current = candidate;
            currentParentId = factorId;
            factored = true;
            break;
          }
        }
        if (!factored) {
          return false;
        }
      }
      steps.push_back(
        "(substitute " + sexprQuote(stepBase)
        + " (parent " + sexprQuote(currentParentId) + ") (subst)"
        + " (result " + clauseSexprFromLiterals(actual) + "))");
    }
    std::ostringstream out;
    for (std::size_t i = 0; i < steps.size(); ++i) {
      if (i != 0) {
        out << "\n  ";
      }
      out << steps[i];
    }
    step = out.str();
    return true;
  };

  if (extra != nullptr && rule == Kernel::InferenceRule::RESOLUTION) {
    const auto* selected = static_cast<const Inferences::TwoLiteralInferenceExtra*>(extra);
    if (stepForOrientation(selected->selectedLiteral.selectedLiteral, selected->otherLiteral, result)) {
      return true;
    }
    return stepForOrientation(selected->otherLiteral, selected->selectedLiteral.selectedLiteral, result);
  }

  if (extra != nullptr) {
    const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
    Kernel::Literal* selectedLiteral = selected->selectedLiteral;
    for (unsigned parentIndex = 0; parentIndex < 2; ++parentIndex) {
      if (!containsLiteral(parents[parentIndex], selectedLiteral)) {
        continue;
      }
      unsigned otherParentIndex = parentIndex == 0 ? 1 : 0;
      for (unsigned i = 0; i < parents[otherParentIndex]->length(); ++i) {
        Kernel::Literal* candidate = (*parents[otherParentIndex])[i];
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
  }

  for (unsigned leftIndex = 0; leftIndex < parents[0]->length(); ++leftIndex) {
    Kernel::Literal* left = (*parents[0])[leftIndex];
    for (unsigned rightIndex = 0; rightIndex < parents[1]->length(); ++rightIndex) {
      Kernel::Literal* right = (*parents[1])[rightIndex];
      if (!complementary(left, right)) {
        continue;
      }
      if (stepForOrientation(left, right, result)) {
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateSubstitutedResolutionStepsSexpr(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result,
  std::vector<MegalodonKernelSyntax::PrimitiveStep>* primitiveSteps)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::RESOLUTION
      && rule != Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::FORWARD_LITERAL_REWRITING
    )) {
    return false;
  }
  const bool hasReplaySubstitutions = replayInfo != nullptr
    && replayInfo->premises.size() == 2
    && replayInfo->substitutionForBanksSub.size() == 2;
  if (rule == Kernel::InferenceRule::RESOLUTION && !hasReplaySubstitutions) {
    return false;
  }
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr && rule == Kernel::InferenceRule::RESOLUTION) {
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
  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto substitutionSexpr = [&](const Kernel::Substitution& substitution, std::string& rendered, bool& nonIdentity) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    nonIdentity = false;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termSexpr;
      if (!certificateTermSexpr(term, termSexpr)) {
        return false;
      }
      nonIdentity = true;
      items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : items) {
      out << ' ' << item.second;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto substitutedAtomSexpr = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (positive->isEquality()) {
      std::string lhs;
      std::string rhs;
      Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(0), substitution);
      Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(1), substitution);
      if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
        return false;
      }
      return certificateEqualityAtomSexpr(
        Kernel::SortHelper::getEqualityArgumentSort(positive), lhs, rhs, rendered);
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
    return certificateAtomSexpr(substituted, rendered);
  };
  auto substitutedLiteralSexpr = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
    std::string atom;
    if (!substitutedAtomSexpr(literal, substitution, atom)) {
      return false;
    }
    rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ") + atom + ")";
    return true;
  };
  auto substitutedClauseSexpr = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::string& rendered) {
    std::vector<std::string> literals;
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string literalSexpr;
      if (!substitutedLiteralSexpr(literal, substitution, literalSexpr)) {
        return false;
      }
      literals.push_back(literalSexpr);
    }
    if (!appendCertificateSplitLiteralsSexpr(clause, literals)) {
      return false;
    }
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    const std::string posPrefix = "(pos ";
    const std::string negPrefix = "(neg ";
    std::string polarityPrefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      polarityPrefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      polarityPrefix = negPrefix;
    } else {
      return false;
    }
    const std::string atomPrefix = polarityPrefix + "(AP (AP ";
    if (literal.rfind(atomPrefix, 0) != 0) {
      return false;
    }
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t equalityStart = atomPrefix.size();
    std::size_t equalityEnd = std::string::npos;
    if (!termEnd(equalityStart, equalityEnd) || equalityEnd >= literal.size() || literal[equalityEnd] != ' ') {
      return false;
    }
    std::string equalityHead = literal.substr(equalityStart, equalityEnd - equalityStart);
    if (equalityHead != "(TMH \"=\")" && equalityHead.rfind("(TPAP (TMH ", 0) != 0) {
      return false;
    }
    std::size_t leftStart = equalityEnd + 1;
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = atomPrefix + equalityHead + " " + right + ") " + left + "))";
    return true;
  };
  auto canNormalizeBySymmetry =
    [&](std::vector<std::string> current,
        const std::vector<std::string>& target,
        std::vector<unsigned>& flipIndices) {
      flipIndices.clear();
      for (unsigned guard = 0; normalized(current) != target && guard < current.size(); ++guard) {
        bool changed = false;
        for (unsigned i = 0; i < current.size(); ++i) {
          std::string swapped;
          if (!swappedEqualityLiteral(current[i], swapped)) {
            continue;
          }
          std::vector<std::string> candidate = current;
          candidate[i] = swapped;
          if (normalized(candidate) != target
            && std::find(target.begin(), target.end(), swapped) == target.end()) {
            continue;
          }
          current = candidate;
          flipIndices.push_back(i);
          changed = true;
          break;
        }
        if (!changed) {
          break;
        }
      }
      return normalized(current) == target;
    };
  auto appendSubstitutedClauseExcept = [&](std::vector<std::string>& literals, Kernel::Clause* clause, const Kernel::Substitution& substitution, Kernel::Literal* excluded) {
    bool skipped = false;
    for (unsigned i = 0; i < clause->length(); ++i) {
      Kernel::Literal* literal = (*clause)[i];
      if (!skipped && literal == excluded) {
        skipped = true;
        continue;
      }
      std::string rendered;
      if (!substitutedLiteralSexpr(literal, substitution, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    return skipped && appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto matchTerm =
    [&](auto&& self,
        Kernel::TermList pattern,
        Kernel::TermList target,
        std::map<unsigned, Kernel::TermList>& bindings) -> bool {
      if (pattern.isVar()) {
        auto existing = bindings.find(pattern.var());
        if (existing == bindings.end()) {
          bindings.emplace(pattern.var(), target);
          return true;
        }
        return existing->second == target;
      }
      if (!pattern.isTerm() || !target.isTerm()) {
        return pattern == target;
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned index = 0; index < patternTerm->arity(); ++index) {
        if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), bindings)) {
          return false;
        }
      }
      return true;
    };
  auto matchLiteralOriented =
    [&](Kernel::Literal* pattern,
        Kernel::Literal* target,
        bool samePolarity,
        bool reverseEquality,
        std::map<unsigned, Kernel::TermList>& bindings) {
      if ((pattern->polarity() == target->polarity()) != samePolarity) {
        return false;
      }
      if (pattern->isEquality() != target->isEquality()) {
        return false;
      }
      if (pattern->isEquality()) {
        if (!matchTerm(matchTerm,
            Kernel::SortHelper::getEqualityArgumentSort(pattern),
            Kernel::SortHelper::getEqualityArgumentSort(target),
            bindings)) {
          return false;
        }
        Kernel::TermList targetLeft = *target->nthArgument(reverseEquality ? 1 : 0);
        Kernel::TermList targetRight = *target->nthArgument(reverseEquality ? 0 : 1);
        return matchTerm(matchTerm, *pattern->nthArgument(0), targetLeft, bindings)
          && matchTerm(matchTerm, *pattern->nthArgument(1), targetRight, bindings);
      }
      if (pattern->functor() != target->functor()
        || pattern->arity() != target->arity()) {
        return false;
      }
      for (unsigned index = 0; index < pattern->arity(); ++index) {
        if (!matchTerm(matchTerm, *pattern->nthArgument(index), *target->nthArgument(index), bindings)) {
          return false;
        }
      }
      return true;
    };
  auto matchLiteral =
    [&](Kernel::Literal* pattern,
        Kernel::Literal* target,
        bool samePolarity,
        std::map<unsigned, Kernel::TermList>& bindings) {
      std::map<unsigned, Kernel::TermList> trial = bindings;
      if (matchLiteralOriented(pattern, target, samePolarity, false, trial)) {
        bindings = std::move(trial);
        return true;
      }
      if (pattern->isEquality()) {
        trial = bindings;
        if (matchLiteralOriented(pattern, target, samePolarity, true, trial)) {
          bindings = std::move(trial);
          return true;
        }
      }
      return false;
    };
  auto fallbackSideSubstitution =
    [&](Kernel::Clause* sideParent, Kernel::Literal* selectedLiteral, Kernel::Substitution& sideSubstitution) {
      for (unsigned pivotIndex = 0; pivotIndex < sideParent->length(); ++pivotIndex) {
        Kernel::Literal* sidePivot = (*sideParent)[pivotIndex];
        std::map<unsigned, Kernel::TermList> pivotBindings;
        if (!matchLiteral(sidePivot, selectedLiteral, false, pivotBindings)) {
          continue;
        }

        std::function<bool(unsigned, std::map<unsigned, Kernel::TermList>&)> matchRemainder =
          [&](unsigned sideIndex, std::map<unsigned, Kernel::TermList>& bindings) {
            if (sideIndex == sideParent->length()) {
              return true;
            }
            if (sideIndex == pivotIndex) {
              return matchRemainder(sideIndex + 1, bindings);
            }
            Kernel::Literal* sideLiteral = (*sideParent)[sideIndex];
            for (Kernel::Literal* conclusionLiteral : unit->asClause()->iterLits()) {
              std::map<unsigned, Kernel::TermList> trial = bindings;
              if (!matchLiteral(sideLiteral, conclusionLiteral, true, trial)) {
                continue;
              }
              if (matchRemainder(sideIndex + 1, trial)) {
                bindings = std::move(trial);
                return true;
              }
            }
            return false;
          };

        std::map<unsigned, Kernel::TermList> bindings = std::move(pivotBindings);
        if (!matchRemainder(0, bindings)) {
          continue;
        }
        for (const auto& binding : bindings) {
          sideSubstitution.rebind(binding.first, binding.second);
        }
        return true;
      }
      return false;
    };
  auto orientation = [&](Kernel::Literal* leftPivot, std::size_t leftIndex, Kernel::Literal* rightPivot, std::size_t rightIndex, std::string& rendered) {
    if (!containsLiteral(parents[leftIndex], leftPivot)
      || !containsLiteral(parents[rightIndex], rightPivot)) {
      return false;
    }
    Kernel::Literal* leftSubstituted = Kernel::SubstHelper::apply(leftPivot, replayInfo->substitutionForBanksSub[leftIndex]);
    Kernel::Literal* rightSubstituted = Kernel::SubstHelper::apply(rightPivot, replayInfo->substitutionForBanksSub[rightIndex]);
    if (leftSubstituted->isPositive() == rightSubstituted->isPositive()) {
      return false;
    }
    std::string leftAtom;
    std::string rightAtom;
    if (!substitutedAtomSexpr(leftPivot, replayInfo->substitutionForBanksSub[leftIndex], leftAtom)
      || !substitutedAtomSexpr(rightPivot, replayInfo->substitutionForBanksSub[rightIndex], rightAtom)
      || leftAtom != rightAtom) {
      return false;
    }

    std::vector<std::string> expected;
    if (!appendSubstitutedClauseExcept(expected, parents[leftIndex], replayInfo->substitutionForBanksSub[leftIndex], leftPivot)
      || !appendSubstitutedClauseExcept(expected, parents[rightIndex], replayInfo->substitutionForBanksSub[rightIndex], rightPivot)) {
      return false;
    }
    std::sort(expected.begin(), expected.end());
    expected.erase(std::unique(expected.begin(), expected.end()), expected.end());
    std::vector<std::string> actual;
    if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
      return false;
    }
    std::sort(actual.begin(), actual.end());
    actual.erase(std::unique(actual.begin(), actual.end()), actual.end());
    if (expected != actual) {
      return false;
    }

    std::string stepBase = "u" + std::to_string(unit->number());
    std::vector<std::string> steps;
    std::vector<MegalodonKernelSyntax::PrimitiveStep> localPrimitiveSteps;
    std::string parentIds[2];
    for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
      std::string parentId = "u" + std::to_string(parents[parentIndex]->number());
      std::string subst;
      std::string clause;
      bool nonIdentity = false;
      if (!certificateSubstitutionSexprForClause(replayInfo->substitutionForBanksSub[parentIndex], parents[parentIndex], subst)
        || !substitutedClauseSexpr(parents[parentIndex], replayInfo->substitutionForBanksSub[parentIndex], clause)) {
        return false;
      }
      nonIdentity = subst != "(subst)";
      if (nonIdentity) {
        std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
        std::string substituteStep;
        if (!certificateSubstituteStepSexpr(
              substituteId,
              parentId,
              parents[parentIndex],
              replayInfo->substitutionForBanksSub[parentIndex],
              substituteStep)) {
          return false;
        }
        steps.push_back(substituteStep);
        localPrimitiveSteps.push_back(
          MegalodonKernelSyntax::primitiveClauseStep(
            "substitute",
            substituteId,
            {parentId},
            clause,
            {{"substitution", subst}},
            substituteStep));
        parentId = substituteId;
      }
      parentIds[parentIndex] = parentId;
    }

    unsigned leftPivotIndex = 0;
    unsigned rightPivotIndex = 0;
    std::string conclusion;
    if (!literalIndex(parents[leftIndex], leftPivot, leftPivotIndex)
      || !literalIndex(parents[rightIndex], rightPivot, rightPivotIndex)
      || !certificateClauseSexpr(unit->asClause(), conclusion)) {
      return false;
    }
    steps.push_back(
      "(resolve " + sexprQuote(stepBase)
      + " (parents " + sexprQuote(parentIds[leftIndex]) + " " + sexprQuote(parentIds[rightIndex]) + ")"
      + " (pivot " + std::to_string(leftPivotIndex) + " " + std::to_string(rightPivotIndex) + ")"
      + " (result " + conclusion + "))");
    localPrimitiveSteps.push_back(
      MegalodonKernelSyntax::primitiveClauseStep(
        "resolve",
        stepBase,
        {parentIds[leftIndex], parentIds[rightIndex]},
        conclusion,
        {{"pivot_left", std::to_string(leftPivotIndex)}, {"pivot_right", std::to_string(rightPivotIndex)}},
        steps.back()));

    std::ostringstream out;
    for (std::size_t i = 0; i < steps.size(); ++i) {
      if (i != 0) {
        out << "\n  ";
      }
      out << steps[i];
    }
    rendered = out.str();
    if (primitiveSteps != nullptr) {
      *primitiveSteps = localPrimitiveSteps;
    }
    return true;
  };

  if (hasReplaySubstitutions && extra != nullptr) {
    if (rule == Kernel::InferenceRule::RESOLUTION) {
      const auto* selected = static_cast<const Inferences::TwoLiteralInferenceExtra*>(extra);
      if (orientation(selected->selectedLiteral.selectedLiteral, 0, selected->otherLiteral, 1, result)) {
        return true;
      }
      return orientation(selected->otherLiteral, 1, selected->selectedLiteral.selectedLiteral, 0, result);
    }

    const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
    Kernel::Literal* selectedLiteral = selected->selectedLiteral;
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
  }

  if (rule == Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
    || rule == Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION
    || rule == Kernel::InferenceRule::FORWARD_LITERAL_REWRITING) {
    struct ResolutionPivotCandidate {
      std::size_t mainParentIndex;
      unsigned selectedIndex;
      Kernel::Literal* selectedLiteral;
    };
    std::vector<ResolutionPivotCandidate> pivotCandidates;
    if (extra != nullptr) {
      const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
      for (std::size_t mainParentIndex = 0; mainParentIndex < 2; ++mainParentIndex) {
        unsigned selectedIndex = 0;
        if (!literalIndex(parents[mainParentIndex], selected->selectedLiteral, selectedIndex)) {
          continue;
        }
        pivotCandidates.push_back({mainParentIndex, selectedIndex, selected->selectedLiteral});
      }
    }
    for (std::size_t mainParentIndex = 0; mainParentIndex < 2; ++mainParentIndex) {
      for (unsigned selectedIndex = 0; selectedIndex < parents[mainParentIndex]->length(); ++selectedIndex) {
        Kernel::Literal* selectedLiteral = (*parents[mainParentIndex])[selectedIndex];
        bool alreadyQueued = false;
        for (const ResolutionPivotCandidate& candidate : pivotCandidates) {
          if (candidate.mainParentIndex == mainParentIndex
            && candidate.selectedLiteral == selectedLiteral) {
            alreadyQueued = true;
            break;
          }
        }
        if (!alreadyQueued) {
          pivotCandidates.push_back({mainParentIndex, selectedIndex, selectedLiteral});
        }
      }
    }
    for (const ResolutionPivotCandidate& pivotCandidate : pivotCandidates) {
      std::size_t mainParentIndex = pivotCandidate.mainParentIndex;
      unsigned selectedIndex = pivotCandidate.selectedIndex;
      Kernel::Literal* selectedLiteral = pivotCandidate.selectedLiteral;
      std::size_t sideParentIndex = mainParentIndex == 0 ? 1 : 0;
      SATSubsumption::SATSubsumptionAndResolution satSR;
      Kernel::Substitution sideSubstitution;
      bool foundSideSubstitution = fallbackSideSubstitution(
        parents[sideParentIndex],
        selectedLiteral,
        sideSubstitution);
      if (!foundSideSubstitution
        && satSR.checkSubsumptionResolutionWithLiteral(
          parents[sideParentIndex],
          parents[mainParentIndex],
          selectedIndex)) {
        sideSubstitution = satSR.getBindingsForSubsumptionResolutionWithLiteral();
        foundSideSubstitution = true;
      }
      if (!foundSideSubstitution) {
        continue;
      }

      for (unsigned sideIndex = 0; sideIndex < parents[sideParentIndex]->length(); ++sideIndex) {
        Kernel::Literal* sideLiteral = (*parents[sideParentIndex])[sideIndex];
        Kernel::Literal* sideSubstituted = Kernel::SubstHelper::apply(sideLiteral, sideSubstitution);
        if (selectedLiteral->isPositive() == sideSubstituted->isPositive()) {
          continue;
        }
        std::string selectedAtom;
        std::string sideAtom;
        bool needsSideSymmetry = false;
        std::string swappedSideAtom;
        std::string swappedSideLiteral;
        if (!certificateAtomSexpr(selectedLiteral, selectedAtom)
          || !substitutedAtomSexpr(sideLiteral, sideSubstitution, sideAtom)) {
          continue;
        }
        if (selectedAtom != sideAtom) {
          if (!sideLiteral->isEquality()) {
            continue;
          }
          std::string lhs;
          std::string rhs;
          Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*sideLiteral->nthArgument(1), sideSubstitution);
          Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*sideLiteral->nthArgument(0), sideSubstitution);
          if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
            continue;
          }
          swappedSideAtom = "(AP (AP (TMH \"=\") " + lhs + ") " + rhs + ")";
          if (selectedAtom != swappedSideAtom) {
            continue;
          }
          needsSideSymmetry = true;
        }

        std::vector<std::string> expected;
        bool skippedSelected = false;
        for (unsigned i = 0; i < parents[mainParentIndex]->length(); ++i) {
          Kernel::Literal* literal = (*parents[mainParentIndex])[i];
          if (!skippedSelected && literal == selectedLiteral) {
            skippedSelected = true;
            continue;
          }
          std::string rendered;
          if (!certificateLiteralSexpr(literal, rendered)) {
            expected.clear();
            break;
          }
          expected.push_back(rendered);
        }
        if (!skippedSelected
          || (expected.empty() && parents[mainParentIndex]->length() > 1)
          || !appendCertificateSplitLiteralsSexpr(parents[mainParentIndex], expected)
          || !appendSubstitutedClauseExcept(expected, parents[sideParentIndex], sideSubstitution, sideLiteral)) {
          continue;
        }
        std::vector<std::string> resolvedClause = expected;
        expected = normalized(expected);

        std::vector<std::string> actualRaw;
        if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actualRaw)) {
          return false;
        }
        std::vector<std::string> actual = normalized(actualRaw);
        std::vector<unsigned> symmetryFlipIndices;
        const bool needsSymmetryNormalization = expected != actual
          && canNormalizeBySymmetry(resolvedClause, actual, symmetryFlipIndices);
        if (expected != actual && !needsSymmetryNormalization) {
          continue;
        }

        std::string sideSubst;
        std::string sideClause;
        std::vector<std::string> sideClauseLiterals;
        bool sideNonIdentity = false;
        std::string conclusion;
        if (!substitutionSexpr(sideSubstitution, sideSubst, sideNonIdentity)
          || !certificateClauseSexpr(unit->asClause(), conclusion)) {
          return false;
        }
        for (Kernel::Literal* literal : parents[sideParentIndex]->iterLits()) {
          std::string rendered;
          if (!substitutedLiteralSexpr(literal, sideSubstitution, rendered)) {
            return false;
          }
          sideClauseLiterals.push_back(rendered);
        }
        if (!appendCertificateSplitLiteralsSexpr(parents[sideParentIndex], sideClauseLiterals)) {
          return false;
        }
        sideClause = clauseSexprFromLiterals(sideClauseLiterals);
        if (needsSideSymmetry
          && (sideIndex >= sideClauseLiterals.size()
            || !swappedEqualityLiteral(sideClauseLiterals[sideIndex], swappedSideLiteral))) {
          continue;
        }
        std::string stepBase = "u" + std::to_string(unit->number());
        std::vector<std::string> steps;
        std::vector<MegalodonKernelSyntax::PrimitiveStep> localPrimitiveSteps;
        std::string sideParentId = "u" + std::to_string(parents[sideParentIndex]->number());
        if (sideNonIdentity) {
          sideParentId = stepBase + "_side_subst";
          std::string sideSubstituteStep;
          if (!certificateSubstituteStepSexpr(
                sideParentId,
                "u" + std::to_string(parents[sideParentIndex]->number()),
                parents[sideParentIndex],
                sideSubstitution,
                sideSubstituteStep)) {
            return false;
          }
          steps.push_back(sideSubstituteStep);
          localPrimitiveSteps.push_back(
            MegalodonKernelSyntax::primitiveClauseStep(
              "substitute",
              sideParentId,
              {"u" + std::to_string(parents[sideParentIndex]->number())},
              sideClause,
              {{"substitution", sideSubst}},
              sideSubstituteStep));
        }
        if (needsSideSymmetry) {
          std::vector<std::string> sideSymmetryLiterals = sideClauseLiterals;
          sideSymmetryLiterals[sideIndex] = swappedSideLiteral;
          const std::string sideSymmetryId = stepBase + "_side_symmetry0";
          const std::string sideSymmetryClause = clauseSexprFromLiterals(sideSymmetryLiterals);
          const std::string sideSymmetryStep =
            "(equality_symmetry " + sexprQuote(sideSymmetryId)
            + " (parent " + sexprQuote(sideParentId) + ")"
            + " (literal " + std::to_string(sideIndex) + ")"
            + " (result " + sideSymmetryClause + "))";
          steps.push_back(
            sideSymmetryStep);
          localPrimitiveSteps.push_back(
            MegalodonKernelSyntax::primitiveClauseStep(
              "equality_symmetry",
              sideSymmetryId,
              {sideParentId},
              sideSymmetryClause,
              {{"literal", std::to_string(sideIndex)}},
              sideSymmetryStep));
          sideParentId = sideSymmetryId;
        }
        std::string parentIds[2];
        parentIds[mainParentIndex] = "u" + std::to_string(parents[mainParentIndex]->number());
        parentIds[sideParentIndex] = sideParentId;
        const bool needsPostResolutionNormalization = !sameMultiset(resolvedClause, actualRaw);
        std::string resolveId = needsPostResolutionNormalization ? stepBase + "_resolve" : stepBase;
        std::vector<std::string> resolveResult = needsPostResolutionNormalization ? resolvedClause : actualRaw;
        const std::string resolveResultClause = clauseSexprFromLiterals(resolveResult);
        const std::string resolveStep =
          "(resolve " + sexprQuote(resolveId)
          + " (parents " + sexprQuote(parentIds[mainParentIndex])
          + " " + sexprQuote(parentIds[sideParentIndex]) + ")"
          + " (pivot " + std::to_string(selectedIndex) + " " + std::to_string(sideIndex) + ")"
          + " (result " + resolveResultClause + "))";
        steps.push_back(
          resolveStep);
        localPrimitiveSteps.push_back(
          MegalodonKernelSyntax::primitiveClauseStep(
            "resolve",
            resolveId,
            {parentIds[mainParentIndex], parentIds[sideParentIndex]},
            resolveResultClause,
            {{"pivot_left", std::to_string(selectedIndex)}, {"pivot_right", std::to_string(sideIndex)}},
            resolveStep));
        if (needsPostResolutionNormalization) {
          std::vector<std::string> currentClause = resolvedClause;
          std::string currentParentId = resolveId;
          unsigned symmetryCount = 0;
          for (unsigned guard = 0; normalized(currentClause) != actual && guard < currentClause.size(); ++guard) {
            bool changed = false;
            for (unsigned literalToFlip = 0; literalToFlip < currentClause.size(); ++literalToFlip) {
              std::string swapped;
              if (!swappedEqualityLiteral(currentClause[literalToFlip], swapped)) {
                continue;
              }
              std::vector<std::string> candidate = currentClause;
              candidate[literalToFlip] = swapped;
              if (normalized(candidate) != actual
                && std::find(actual.begin(), actual.end(), swapped) == actual.end()) {
                continue;
              }
              const std::string symmetryId = stepBase + "_symmetry" + std::to_string(symmetryCount++);
              const std::string symmetryClause = clauseSexprFromLiterals(candidate);
              const std::string symmetryStep =
                "(equality_symmetry " + sexprQuote(symmetryId)
                + " (parent " + sexprQuote(currentParentId) + ")"
                + " (literal " + std::to_string(literalToFlip) + ")"
                + " (result " + symmetryClause + "))";
              steps.push_back(
                symmetryStep);
              localPrimitiveSteps.push_back(
                MegalodonKernelSyntax::primitiveClauseStep(
                  "equality_symmetry",
                  symmetryId,
                  {currentParentId},
                  symmetryClause,
                  {{"literal", std::to_string(literalToFlip)}},
                  symmetryStep));
              currentClause = candidate;
              currentParentId = symmetryId;
              changed = true;
              break;
            }
            if (!changed) {
              break;
            }
          }
          if (normalized(currentClause) != actual) {
            continue;
          }
          unsigned factorCount = 0;
          while (!sameMultiset(currentClause, actual)) {
            bool factored = false;
            for (unsigned left = 0; left < currentClause.size() && !factored; ++left) {
              for (unsigned right = left + 1; right < currentClause.size(); ++right) {
                if (currentClause[left] != currentClause[right]) {
                  continue;
                }
                std::vector<std::string> candidate = currentClause;
                candidate.erase(candidate.begin() + right);
                if (normalized(candidate) != actual) {
                  continue;
                }
                const std::string factorId = stepBase + "_factor" + std::to_string(factorCount++);
                const std::string factorClause = clauseSexprFromLiterals(candidate);
                const std::string factorStep =
                  "(factor " + sexprQuote(factorId)
                  + " (parent " + sexprQuote(currentParentId) + ")"
                  + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
                  + " (result " + factorClause + "))";
                steps.push_back(
                  factorStep);
                localPrimitiveSteps.push_back(
                  MegalodonKernelSyntax::primitiveClauseStep(
                    "factor",
                    factorId,
                    {currentParentId},
                    factorClause,
                    {{"literal_left", std::to_string(left)}, {"literal_right", std::to_string(right)}},
                    factorStep));
                currentClause = candidate;
                currentParentId = factorId;
                factored = true;
                break;
              }
            }
            if (!factored) {
              break;
            }
          }
          if (!sameMultiset(currentClause, actual)) {
            continue;
          }
          const std::string finalStep =
            "(substitute " + sexprQuote(stepBase)
            + " (parent " + sexprQuote(currentParentId) + ") (subst)"
            + " (result " + conclusion + "))";
          steps.push_back(
            finalStep);
          localPrimitiveSteps.push_back(
            MegalodonKernelSyntax::primitiveClauseStep(
              "substitute",
              stepBase,
              {currentParentId},
              conclusion,
              {{"substitution", "(subst)"}},
              finalStep));
        }

        std::ostringstream out;
        for (std::size_t i = 0; i < steps.size(); ++i) {
          if (i != 0) {
            out << "\n  ";
          }
          out << steps[i];
        }
        result = out.str();
        if (primitiveSteps != nullptr) {
          *primitiveSteps = localPrimitiveSteps;
        }
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateSatSubsumptionResolutionStepSexpr(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (rule != Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
      && rule != Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION)) {
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

  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto isVampireVariableName = [](const std::string& name) {
    if (name.size() < 2 || name[0] != 'X') {
      return false;
    }
    for (std::size_t i = 1; i < name.size(); ++i) {
      if (name[i] < '0' || name[i] > '9') {
        return false;
      }
    }
    return true;
  };
  auto collectSexprVariables = [&](const std::vector<std::string>& clause) {
    std::vector<std::string> variables;
    const std::string marker = "(TMH \"";
    for (const std::string& literal : clause) {
      std::size_t pos = 0;
      while ((pos = literal.find(marker, pos)) != std::string::npos) {
        pos += marker.size();
        std::size_t end = literal.find("\")", pos);
        if (end == std::string::npos) {
          break;
        }
        std::string name = literal.substr(pos, end - pos);
        if (isVampireVariableName(name)) {
          variables.push_back(name);
        }
        pos = end + 2;
      }
    }
    std::sort(variables.begin(), variables.end());
    variables.erase(std::unique(variables.begin(), variables.end()), variables.end());
    return variables;
  };
  std::map<std::string, std::string> knownVariableSorts;
  auto rememberVariableSorts = [&](Kernel::Literal* literal) {
    Lib::DHMap<unsigned, Kernel::TermList> varSorts;
    Kernel::SortHelper::collectVariableSorts(literal, varSorts);
    Lib::DHMap<unsigned, Kernel::TermList>::Iterator it(varSorts);
    while (it.hasNext()) {
      unsigned var;
      Kernel::TermList sort;
      it.next(var, sort);
      std::string sortText;
      if (sortToMegalodon(sort, sortText)) {
        knownVariableSorts[variableName(var)] = sortText;
      }
    }
  };
  for (Kernel::Clause* parent : parents) {
    for (Kernel::Literal* literal : parent->iterLits()) {
      rememberVariableSorts(literal);
    }
  }
  for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
    rememberVariableSorts(literal);
  }
  std::set<std::string> emittedSyntheticVariableSorts;
  auto syntheticVariableSortsMetadata =
    [&](const std::string& id, const std::vector<std::string>& clause) {
      if (!emittedSyntheticVariableSorts.insert(id).second) {
        return std::string();
      }
      std::vector<std::string> variables = collectSexprVariables(clause);
      if (variables.empty()) {
        return std::string();
      }
      std::ostringstream metadata;
      bool any = false;
      metadata << "(step_variable_sorts " << sexprQuote(id) << " (";
      for (const std::string& variable : variables) {
        auto sort = knownVariableSorts.find(variable);
        if (sort == knownVariableSorts.end()) {
          continue;
        }
        if (any) {
          metadata << ' ';
        }
        metadata << sexprQuote(variable + ":" + sort->second);
        any = true;
      }
      metadata << "))";
      return any ? metadata.str() : std::string();
    };
  auto substitutedAtomSexpr =
    [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, bool swapEquality, std::string& rendered) {
      Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
      if (positive->isEquality()) {
        const unsigned leftIndex = swapEquality ? 1 : 0;
        const unsigned rightIndex = swapEquality ? 0 : 1;
        std::string lhs;
        std::string rhs;
        if (!certificateTermSexpr(Kernel::SubstHelper::apply(*positive->nthArgument(leftIndex), substitution), lhs)
          || !certificateTermSexpr(Kernel::SubstHelper::apply(*positive->nthArgument(rightIndex), substitution), rhs)) {
          return false;
        }
        return certificateEqualityAtomSexpr(
          Kernel::SortHelper::getEqualityArgumentSort(positive), lhs, rhs, rendered);
      }
      Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
      return certificateAtomSexpr(substituted, rendered);
  };
  auto swapEqualityLiteral = [&](Kernel::Literal* literal) -> Kernel::Literal* {
    if (literal == nullptr || !literal->isEquality()) {
      return nullptr;
    }
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    return Kernel::Literal::createEquality(
      literal->isPositive(),
      *positive->nthArgument(1),
      *positive->nthArgument(0),
      Kernel::SortHelper::getEqualityArgumentSort(positive));
  };
  auto complementaryUnderSubstitution =
    [&](Kernel::Literal* selected,
        Kernel::Literal* side,
        const Kernel::Substitution& sideSubstitution,
        bool& needsSideSymmetry) {
      needsSideSymmetry = false;
      Kernel::Literal* sideSubstituted = nullptr;
      if (!safeApplySubstitution(side, sideSubstitution, sideSubstituted)) {
        return false;
      }
      if (selected->isPositive() == sideSubstituted->isPositive()) {
        return false;
      }
      std::string selectedAtom;
      std::string sideAtom;
      if (!certificateAtomSexpr(selected, selectedAtom)
        || !substitutedAtomSexpr(side, sideSubstitution, false, sideAtom)) {
        return false;
      }
      if (selectedAtom == sideAtom) {
        return true;
      }
      if (!side->isEquality()) {
        return false;
      }
      std::string swappedSideAtom;
      if (substitutedAtomSexpr(side, sideSubstitution, true, swappedSideAtom)
        && selectedAtom == swappedSideAtom) {
        needsSideSymmetry = true;
        return true;
      }
      return false;
  };

  for (std::size_t mainParentIndex = 0; mainParentIndex < 2; ++mainParentIndex) {
    Kernel::Clause* mainParent = parents[mainParentIndex];
    const std::size_t sideParentIndex = mainParentIndex == 0 ? 1 : 0;
    Kernel::Clause* sideParent = parents[sideParentIndex];
    for (unsigned selectedIndex = 0; selectedIndex < mainParent->length(); ++selectedIndex) {
      Kernel::Literal* selectedLiteral = (*mainParent)[selectedIndex];
      if (proofSelectedLiteral != nullptr && selectedLiteral != proofSelectedLiteral) {
        continue;
      }

      SATSubsumption::SATSubsumptionAndResolution satSR;
      if (!satSR.checkSubsumptionResolutionWithLiteral(sideParent, mainParent, selectedIndex)) {
        continue;
      }
      Kernel::Substitution sideSubstitution = satSR.getBindingsForSubsumptionResolutionWithLiteral();

      std::vector<std::string> expected;
      for (unsigned i = 0; i < mainParent->length(); ++i) {
        if (i == selectedIndex) {
          continue;
        }
        std::string rendered;
        if (!certificateLiteralSexpr((*mainParent)[i], rendered)) {
          return false;
        }
        expected.push_back(rendered);
      }
      if (!appendCertificateSplitLiteralsSexpr(mainParent, expected)) {
        return false;
      }
      std::vector<std::string> actual;
      if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
        return false;
      }
      if (!sameMultiset(expected, actual) && normalized(expected) != normalized(actual)) {
        continue;
      }

      for (unsigned sideLiteralIndex = 0; sideLiteralIndex < sideParent->length(); ++sideLiteralIndex) {
        Kernel::Literal* sideLiteral = (*sideParent)[sideLiteralIndex];
        bool needsSideSymmetry = false;
        if (!complementaryUnderSubstitution(selectedLiteral, sideLiteral, sideSubstitution, needsSideSymmetry)) {
          continue;
        }
        std::string sideSubstitutionSexpr;
        std::string resultClauseSexpr;
        if (!certificateSubstitutionSexpr(sideSubstitution, sideSubstitutionSexpr)
          || !certificateClauseSexpr(unit->asClause(), resultClauseSexpr)) {
          return false;
        }
        const std::string stepBase = "u" + std::to_string(unit->number());
        const std::string mainParentId = "u" + std::to_string(mainParent->number());
        const std::string sideParentId = "u" + std::to_string(sideParent->number());
        auto clauseFromLiterals = [](const std::vector<std::string>& literals) {
          std::ostringstream out;
          out << "(clause";
          for (const std::string& literal : literals) {
            out << ' ' << literal;
          }
          out << ')';
          return out.str();
        };
        std::vector<std::string> mainClauseLiterals;
        std::vector<std::string> sideClauseLiterals;
        if (!appendCertificateClauseLiteralsSexpr(mainParent, mainClauseLiterals)
          || !appendCertificateClauseLiteralsSexpr(sideParent, sideClauseLiterals)
          || selectedIndex >= mainClauseLiterals.size()
          || sideLiteralIndex >= sideClauseLiterals.size()) {
          return false;
        }
        for (Kernel::Literal* literal : sideParent->iterLits()) {
          Kernel::Literal* substituted = nullptr;
          if (!safeApplySubstitution(literal, sideSubstitution, substituted)) {
            return false;
          }
          rememberVariableSorts(substituted);
        }
        std::string primitivePrefix;
        std::string resolveSideParentId = sideParentId;
        auto applyRenderedSubstitutionToLiterals = [&](std::vector<std::string>& literals) {
          if (sideSubstitutionSexpr == "(subst)") {
            return true;
          }
          auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
            if (from.empty()) {
              return;
            }
            std::size_t pos = 0;
            while ((pos = text.find(from, pos)) != std::string::npos) {
              text.replace(pos, from.size(), to);
              pos += to.size();
            }
          };
          std::vector<std::tuple<unsigned, std::string, std::string>> replacements;
          const std::set<unsigned> variables = certificateClauseVariables(sideParent);
          Kernel::Substitution sideSubstitutionCopy = sideSubstitution;
          for (auto [var, term] : iterTraits(sideSubstitutionCopy.items())) {
            if (variables.find(var) == variables.end()) {
              continue;
            }
            if (term.isVar() && term.var() == var) {
              continue;
            }
            std::string termSexpr;
            if (!certificateTermSexpr(term, termSexpr)) {
              return false;
            }
            replacements.push_back({var, "(TMH " + sexprQuote(variableName(var)) + ")", termSexpr});
          }
          std::sort(replacements.begin(), replacements.end(), [](const auto& left, const auto& right) {
            return std::get<0>(left) < std::get<0>(right);
          });
          for (std::string& literal : literals) {
            for (std::size_t i = 0; i < replacements.size(); ++i) {
              replaceAll(literal, std::get<1>(replacements[i]), "(TMH " + sexprQuote("__mg_subst_" + std::to_string(i)) + ")");
            }
            for (std::size_t i = 0; i < replacements.size(); ++i) {
              replaceAll(literal, "(TMH " + sexprQuote("__mg_subst_" + std::to_string(i)) + ")", std::get<2>(replacements[i]));
            }
          }
          return true;
        };
        if (sideSubstitutionSexpr != "(subst)") {
          resolveSideParentId = stepBase + "_side_subst";
          std::string sideSubstituteStep;
          if (!certificateSubstituteStepSexpr(
                resolveSideParentId,
                sideParentId,
                sideParent,
                sideSubstitution,
                sideSubstituteStep)) {
            return false;
          }
          primitivePrefix += sideSubstituteStep;
          primitivePrefix += "\n  ";
        }
        if (!applyRenderedSubstitutionToLiterals(sideClauseLiterals)) {
          return false;
        }
        std::vector<std::string> actualLiterals;
        if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actualLiterals)) {
          return false;
        }
        unsigned sideSymmetryCount = 0;
        auto emitSideSymmetry = [&](unsigned literalIndex, Kernel::Literal* substitutedLiteral) {
          Kernel::Literal* swappedSide = swapEqualityLiteral(substitutedLiteral);
          std::string swappedSideSexpr;
          if (swappedSide == nullptr || !certificateLiteralSexpr(swappedSide, swappedSideSexpr)) {
            return false;
          }
          if (literalIndex >= sideClauseLiterals.size()) {
            return false;
          }
          if (sideClauseLiterals[literalIndex] == swappedSideSexpr) {
            return true;
          }
          sideClauseLiterals[literalIndex] = swappedSideSexpr;
          rememberVariableSorts(swappedSide);
          const std::string sideSymmetryId = stepBase + "_side_symmetry" + std::to_string(sideSymmetryCount++);
          std::string metadata = syntheticVariableSortsMetadata(sideSymmetryId, sideClauseLiterals);
          if (!metadata.empty()) {
            primitivePrefix += metadata;
            primitivePrefix += "\n  ";
          }
          primitivePrefix +=
            "(equality_symmetry " + sexprQuote(sideSymmetryId)
            + " (parent " + sexprQuote(resolveSideParentId) + ")"
            + " (literal " + std::to_string(literalIndex) + ")"
            + " (result " + clauseFromLiterals(sideClauseLiterals) + "))\n  ";
          resolveSideParentId = sideSymmetryId;
          return true;
        };
        if (needsSideSymmetry) {
          Kernel::Literal* sideSubstituted = nullptr;
          if (!safeApplySubstitution(sideLiteral, sideSubstitution, sideSubstituted)) {
            return false;
          }
          if (!emitSideSymmetry(sideLiteralIndex, sideSubstituted)) {
            return false;
          }
        }
        for (unsigned i = 0; i < sideParent->length() && i < sideClauseLiterals.size(); ++i) {
          if (i == sideLiteralIndex || !(*sideParent)[i]->isEquality()) {
            continue;
          }
          if (std::find(actualLiterals.begin(), actualLiterals.end(), sideClauseLiterals[i]) != actualLiterals.end()
            || std::find(mainClauseLiterals.begin(), mainClauseLiterals.end(), sideClauseLiterals[i]) != mainClauseLiterals.end()) {
            continue;
          }
          Kernel::Literal* sideSubstituted = nullptr;
          if (!safeApplySubstitution((*sideParent)[i], sideSubstitution, sideSubstituted)) {
            return false;
          }
          Kernel::Literal* swappedSide = swapEqualityLiteral(sideSubstituted);
          std::string swappedSideSexpr;
          if (swappedSide == nullptr || !certificateLiteralSexpr(swappedSide, swappedSideSexpr)) {
            continue;
          }
          if (std::find(actualLiterals.begin(), actualLiterals.end(), swappedSideSexpr) != actualLiterals.end()
            || std::find(mainClauseLiterals.begin(), mainClauseLiterals.end(), swappedSideSexpr) != mainClauseLiterals.end()) {
            if (!emitSideSymmetry(i, sideSubstituted)) {
              return false;
            }
          }
        }
        std::vector<std::string> resolveLiterals = mainClauseLiterals;
        resolveLiterals.erase(resolveLiterals.begin() + selectedIndex);
        for (std::size_t i = 0; i < sideClauseLiterals.size(); ++i) {
          if (i != sideLiteralIndex) {
            resolveLiterals.push_back(sideClauseLiterals[i]);
          }
        }
        if (normalized(resolveLiterals) != normalized(actualLiterals)) {
          return false;
        }
        const std::string resolveId = stepBase + "_resolve_0";
        std::string resolveMetadata = syntheticVariableSortsMetadata(resolveId, resolveLiterals);
        if (!resolveMetadata.empty()) {
          primitivePrefix += resolveMetadata;
          primitivePrefix += "\n  ";
        }
        primitivePrefix +=
          "(resolve " + sexprQuote(resolveId)
          + " (parents " + sexprQuote(mainParentId)
          + " " + sexprQuote(resolveSideParentId) + ")"
          + " (pivot " + std::to_string(selectedIndex) + " "
          + std::to_string(sideLiteralIndex) + ")"
          + " (result " + clauseFromLiterals(resolveLiterals) + "))\n  ";
        std::vector<std::string> currentLiterals = resolveLiterals;
        std::string currentParentId = resolveId;
        unsigned factorCount = 0;
        while (!sameMultiset(currentLiterals, actualLiterals)) {
          bool factored = false;
          for (unsigned left = 0; left < currentLiterals.size() && !factored; ++left) {
            for (unsigned right = left + 1; right < currentLiterals.size(); ++right) {
              if (currentLiterals[left] != currentLiterals[right]) {
                continue;
              }
              std::vector<std::string> candidate = currentLiterals;
              candidate.erase(candidate.begin() + right);
              if (normalized(candidate) != normalized(actualLiterals)) {
                continue;
              }
              const std::string factorId = stepBase + "_factor" + std::to_string(factorCount++);
              std::string factorMetadata = syntheticVariableSortsMetadata(factorId, candidate);
              if (!factorMetadata.empty()) {
                primitivePrefix += factorMetadata;
                primitivePrefix += "\n  ";
              }
              primitivePrefix +=
                "(factor " + sexprQuote(factorId)
                + " (parent " + sexprQuote(currentParentId) + ")"
                + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
                + " (result " + clauseFromLiterals(candidate) + "))\n  ";
              currentLiterals = candidate;
              currentParentId = factorId;
              factored = true;
              break;
            }
          }
          if (!factored) {
            return false;
          }
        }
        result =
          primitivePrefix
          + "(substitute " + sexprQuote(stepBase)
          + " (parent " + sexprQuote(currentParentId) + ")"
          + " (subst)"
          + " (result " + resultClauseSexpr + "))";
        return true;
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateFactorStepSexpr(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (rule != Kernel::InferenceRule::FACTORING
      && rule != Kernel::InferenceRule::REMOVE_DUPLICATE_LITERALS)) {
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

  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };

  std::vector<std::string> current;
  for (unsigned i = 0; i < parent->length(); ++i) {
    std::string rendered;
    if (!certificateLiteralSexpr((*parent)[i], rendered)) {
      return false;
    }
    current.push_back(rendered);
  }
  if (!appendCertificateSplitLiteralsSexpr(parent, current)) {
    return false;
  }
  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }
  const std::vector<std::string> actualNormalized = normalized(actual);
  if (normalized(current) != actualNormalized
    || current.size() <= actual.size()) {
    return false;
  }

  const std::string stepBase = "u" + std::to_string(unit->number());
  std::string currentParentId = "u" + std::to_string(parent->number());
  std::vector<std::string> steps;
  unsigned factorCount = 0;
  while (!sameMultiset(current, actual)) {
    bool factored = false;
    for (unsigned left = 0; left < current.size() && !factored; ++left) {
      for (unsigned right = left + 1; right < current.size(); ++right) {
        if (current[left] != current[right]) {
          continue;
        }
        std::vector<std::string> candidate = current;
        candidate.erase(candidate.begin() + right);
        if (normalized(candidate) != actualNormalized) {
          continue;
        }
        const bool finalFactor = sameMultiset(candidate, actual);
        const std::string factorId = finalFactor ? stepBase : stepBase + "_factor" + std::to_string(factorCount++);
        steps.push_back(
          "(factor " + sexprQuote(factorId)
          + " (parent " + sexprQuote(currentParentId) + ")"
          + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
          + " (result " + clauseSexprFromLiterals(finalFactor ? actual : candidate) + "))");
        current = finalFactor ? actual : candidate;
        currentParentId = factorId;
        factored = true;
        break;
      }
    }
    if (!factored) {
      return false;
    }
  }
  std::ostringstream out;
  for (std::size_t i = 0; i < steps.size(); ++i) {
    if (i != 0) {
      out << "\n  ";
    }
    out << steps[i];
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateTrivialInequalityRemovalStepsSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL) {
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

  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto normalize = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto isTruthConstant = [](const std::string& rendered, const std::string& name) {
    return rendered == "(TMH \"" + name + "\")";
  };
  auto isNegativeReflexiveEquality = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isNegative()) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    return certificateTermSexpr(*literal->nthArgument(0), lhs)
      && certificateTermSexpr(*literal->nthArgument(1), rhs)
      && lhs == rhs;
  };
  auto isPositiveTruthConflict = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isPositive()) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!certificateTermSexpr(*literal->nthArgument(0), lhs)
      || !certificateTermSexpr(*literal->nthArgument(1), rhs)) {
      return false;
    }
    return (isTruthConstant(lhs, "f__true") && isTruthConstant(rhs, "f__false"))
      || (isTruthConstant(lhs, "f__false") && isTruthConstant(rhs, "f__true"));
  };

  std::vector<std::string> current;
  if (!appendCertificateClauseLiteralsSexpr(parent, current)) {
    return false;
  }
  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }
  if (sameMultiset(current, actual)) {
    return false;
  }

  struct Removal {
    std::string rule;
    std::string literal;
  };
  std::vector<Removal> removals;
  for (Kernel::Literal* literal : parent->iterLits()) {
    std::string rendered;
    if (!certificateLiteralSexpr(literal, rendered)) {
      return false;
    }
    if (std::find(current.begin(), current.end(), rendered) == current.end()
      || std::find(actual.begin(), actual.end(), rendered) != actual.end()) {
      continue;
    }
    if (isNegativeReflexiveEquality(literal)) {
      removals.push_back({"equality_resolution", rendered});
    } else if (isPositiveTruthConflict(literal)) {
      removals.push_back({"truth_conflict", rendered});
    } else {
      return false;
    }
  }
  if (removals.empty()) {
    return false;
  }

  const std::string stepBase = "u" + std::to_string(unit->number());
  std::string currentParentId = "u" + std::to_string(parent->number());
  std::vector<std::string> steps;
  for (std::size_t i = 0; i < removals.size(); ++i) {
    const Removal& removal = removals[i];
    auto literalIt = std::find(current.begin(), current.end(), removal.literal);
    if (literalIt == current.end()) {
      return false;
    }
    const std::size_t literalIndex = static_cast<std::size_t>(literalIt - current.begin());
    std::vector<std::string> next = current;
    next.erase(next.begin() + literalIndex);
    const bool finalRemoval = i + 1 == removals.size();
    if (finalRemoval && !sameMultiset(next, actual)) {
      return false;
    }
    const std::vector<std::string>& resultLiterals = finalRemoval ? actual : next;
    const std::string stepId = i + 1 == removals.size()
      ? stepBase
      : stepBase + "_trivial" + std::to_string(i);
    steps.push_back(
      "(" + removal.rule + " " + sexprQuote(stepId)
      + " (parent " + sexprQuote(currentParentId) + ")"
      + " (literal " + std::to_string(literalIndex) + ")"
      + " (result " + clauseSexprFromLiterals(resultLiterals) + "))");
    current = resultLiterals;
    currentParentId = stepId;
  }

  if (normalize(current) != normalize(actual) || !sameMultiset(current, actual)) {
    return false;
  }

  std::ostringstream out;
  for (std::size_t i = 0; i < steps.size(); ++i) {
    if (i != 0) {
      out << "\n  ";
    }
    out << steps[i];
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateEqualityResolutionStepSexpr(
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

  Kernel::Substitution emptySubstitution;
  const Kernel::Substitution* selectedSubstitution = &emptySubstitution;
  if (replayInfo != nullptr
    && replayInfo->premises.size() == 1
    && replayInfo->substitutionForBanksSub.size() == 1) {
    selectedSubstitution = &replayInfo->substitutionForBanksSub[0];
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

  auto substitutionSexpr = [&](const Kernel::Substitution& substitution, std::string& rendered, bool& nonIdentity) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    nonIdentity = false;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termSexpr;
      if (!certificateTermSexpr(term, termSexpr)) {
        return false;
      }
      nonIdentity = true;
      items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : items) {
      out << ' ' << item.second;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto substitutedLiteralSexpr =
    [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
      Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
      if (positive->isEquality()) {
        std::string lhs;
        std::string rhs;
        Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(0), substitution);
        Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(1), substitution);
        if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
          return false;
        }
        std::string atom;
        Kernel::TermList sort =
          Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(literal), substitution);
        if (!certificateEqualityAtomSexpr(sort, lhs, rhs, atom)) {
          return false;
        }
        rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
          + atom + ")";
        return true;
      }
      Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
      return certificateLiteralSexpr(substituted, rendered);
    };
  auto substitutedParentLiterals =
    [&](const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
      for (Kernel::Literal* literal : parent->iterLits()) {
        std::string rendered;
        if (!substitutedLiteralSexpr(literal, substitution, rendered)) {
          return false;
        }
        literals.push_back(rendered);
      }
      return appendCertificateSplitLiteralsSexpr(parent, literals);
    };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    const std::string typedPosPrefix =
      "(pos (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    const std::string typedNegPrefix =
      "(neg (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else if (literal.rfind(typedPosPrefix, 0) == 0 || literal.rfind(typedNegPrefix, 0) == 0) {
      const std::string typedPrefix =
        literal.rfind(typedPosPrefix, 0) == 0 ? typedPosPrefix : typedNegPrefix;
      std::size_t typeStart = typedPrefix.size();
      std::size_t typeEnd = std::string::npos;
      auto termEnd = [&](std::size_t start, std::size_t& end) {
        int depth = 0;
        for (std::size_t i = start; i < literal.size(); ++i) {
          if (literal[i] == '(') {
            ++depth;
          } else if (literal[i] == ')') {
            --depth;
            if (depth == 0) {
              end = i + 1;
              return true;
            }
          }
        }
        return false;
      };
      if (!termEnd(typeStart, typeEnd) || typeEnd + 2 >= literal.size()
        || literal[typeEnd] != ')' || literal[typeEnd + 1] != ' ') {
        return false;
      }
      prefix = literal.substr(0, typeEnd + 2);
    } else {
      return false;
    }
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftStart = prefix.size();
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto emitEqualitySymmetrySteps =
    [&](std::vector<std::string>& steps,
        std::vector<std::string>& current,
        std::string& currentParentId,
        const std::vector<std::string>& actual,
        const std::string& unitId) {
      for (unsigned guard = 0; !sameMultiset(current, actual) && guard < current.size(); ++guard) {
        bool changed = false;
        for (unsigned i = 0; i < current.size(); ++i) {
          std::string swapped;
          if (!swappedEqualityLiteral(current[i], swapped)) {
            continue;
          }
          std::vector<std::string> candidate = current;
          candidate[i] = swapped;
          if (!sameMultiset(candidate, actual)
            && std::find(actual.begin(), actual.end(), swapped) == actual.end()) {
            continue;
          }
          const bool finalSymmetry = sameMultiset(candidate, actual);
          const std::string symmetryId = finalSymmetry
            ? unitId
            : unitId + "_sym" + std::to_string(guard);
          steps.push_back(
            "(equality_symmetry " + sexprQuote(symmetryId)
            + " (parent " + sexprQuote(currentParentId) + ")"
            + " (literal " + std::to_string(i) + ")"
            + " (result " + clauseSexprFromLiterals(finalSymmetry ? actual : candidate) + "))");
          current = finalSymmetry ? actual : candidate;
          currentParentId = symmetryId;
          changed = true;
          break;
        }
        if (!changed) {
          return false;
        }
      }
      return sameMultiset(current, actual);
    };
  std::string subst;
  bool nonIdentitySubstitution = false;
  if (!substitutionSexpr(*selectedSubstitution, subst, nonIdentitySubstitution)) {
    return false;
  }
  std::vector<Kernel::Literal*> activeParentLiterals;
  for (Kernel::Literal* literal : parent->iterLits()) {
    activeParentLiterals.push_back(
      nonIdentitySubstitution ? Kernel::SubstHelper::apply(literal, *selectedSubstitution) : literal);
  }
  const std::string unitId = "u" + std::to_string(unit->number());
  std::string activeParentId = "u" + std::to_string(parent->number());
  std::string substitutionStep;
  if (nonIdentitySubstitution) {
    std::vector<std::string> substitutedLiterals;
    if (!substitutedParentLiterals(*selectedSubstitution, substitutedLiterals)) {
      return false;
    }
    activeParentId = unitId + "_subst";
    substitutionStep =
      "(substitute " + sexprQuote(activeParentId)
      + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ") "
      + subst
      + " (result " + clauseSexprFromLiterals(substitutedLiterals) + "))";
  }

  auto tryLiteralIndex = [&](unsigned literalIndex, std::string& step) {
    if (literalIndex >= activeParentLiterals.size()) {
      return false;
    }
    Kernel::Literal* literal = activeParentLiterals[literalIndex];
    if (literal == nullptr || !literal->isEquality() || !literal->isNegative()) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!certificateTermSexpr(*literal->nthArgument(0), lhs)
      || !certificateTermSexpr(*literal->nthArgument(1), rhs)) {
      return false;
    }

    std::vector<std::string> substitutedParent;
    if (!substitutedParentLiterals(*selectedSubstitution, substitutedParent)) {
      return false;
    }
    std::vector<std::string> expected;
    for (unsigned i = 0; i < substitutedParent.size(); ++i) {
      if (i == literalIndex) {
        continue;
      }
      expected.push_back(substitutedParent[i]);
    }
    std::vector<std::string> actual;
    if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
      return false;
    }

    if (lhs != rhs) {
      std::vector<std::string> remainingActual = actual;
      for (const std::string& literal : expected) {
        auto found = std::find(remainingActual.begin(), remainingActual.end(), literal);
        if (found == remainingActual.end()) {
          return false;
        }
        remainingActual.erase(found);
      }
      if (remainingActual.empty()) {
        return false;
      }
      std::string selectedLiteral;
      if (!substitutedLiteralSexpr(literal, *selectedSubstitution, selectedLiteral)) {
        return false;
      }
      std::vector<std::string> steps;
      if (!substitutionStep.empty()) {
        steps.push_back(substitutionStep);
      }
      std::ostringstream constraints;
      constraints << "(constraints";
      for (const std::string& constraint : remainingActual) {
        constraints << ' ' << constraint;
      }
      constraints << ')';
      steps.push_back(
        "(equality_resolution_constraints " + sexprQuote(unitId)
        + " (parent " + sexprQuote(activeParentId) + ")"
        + " (literal " + std::to_string(literalIndex) + ")"
        + " (selected " + selectedLiteral + ")"
        + ' ' + constraints.str()
        + " (result " + clauseSexprFromLiterals(actual) + "))");
      std::ostringstream out;
      for (std::size_t i = 0; i < steps.size(); ++i) {
        if (i != 0) {
          out << "\n  ";
        }
        out << steps[i];
      }
      step = out.str();
      return true;
    }

    if (!sameMultiset(expected, actual)) {
      std::vector<std::string> current = expected;
      std::vector<std::string> probeSteps;
      std::string probeParentId = unitId + "_eqres";
      if (!emitEqualitySymmetrySteps(probeSteps, current, probeParentId, actual, unitId)) {
        return false;
      }
    }

    std::vector<std::string> steps;
    if (!substitutionStep.empty()) {
      steps.push_back(substitutionStep);
    }
    const bool directResult = sameMultiset(expected, actual);
    const std::string equalityResolutionId = directResult ? unitId : unitId + "_eqres";
    steps.push_back(
      "(equality_resolution " + sexprQuote(equalityResolutionId)
      + " (parent " + sexprQuote(activeParentId) + ")"
      + " (literal " + std::to_string(literalIndex) + ")"
      + " (result " + clauseSexprFromLiterals(directResult ? actual : expected) + "))");
    if (!directResult) {
      std::vector<std::string> current = expected;
      std::string currentParentId = equalityResolutionId;
      if (!emitEqualitySymmetrySteps(steps, current, currentParentId, actual, unitId)) {
        return false;
      }
    }
    if (steps.empty()) {
      return false;
    }

    std::ostringstream out;
    for (std::size_t i = 0; i < steps.size(); ++i) {
      if (i != 0) {
        out << "\n  ";
      }
      out << steps[i];
    }
    step = out.str();
    return true;
  };

  if (rule == Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL) {
    for (unsigned i = 0; i < activeParentLiterals.size(); ++i) {
      if (tryLiteralIndex(i, result)) {
        return true;
      }
    }
    return false;
  }

  const auto* extra = env.proofExtra.find(unit);
  if (extra != nullptr) {
    const auto* selected = static_cast<const Inferences::LiteralInferenceExtra*>(extra);
    for (unsigned i = 0; i < parent->length(); ++i) {
      if ((*parent)[i] == selected->selectedLiteral) {
        if (tryLiteralIndex(i, result)) {
          return true;
        }
        break;
      }
    }
  }
  for (unsigned i = 0; i < activeParentLiterals.size(); ++i) {
    if (tryLiteralIndex(i, result)) {
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::certificateEqualityFactoringStepSexpr(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  auto fail = [&](const char* reason) {
    if (std::getenv("MEGALODON_CERT_DEBUG")
      && unit->isClause()
      && unit->inference().rule() == Kernel::InferenceRule::EQUALITY_FACTORING) {
      std::cerr << "megalodon native equality factoring failed for u"
                << unit->number() << ": " << reason << std::endl;
    }
    return false;
  };
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::EQUALITY_FACTORING
    || replayInfo == nullptr
    || replayInfo->premises.size() != 1
    || replayInfo->substitutionForBanksSub.size() != 1) {
    return fail("bad replay precondition");
  }
  const auto* extra = env.proofExtra.find(unit);
  const auto* rewrite = extra == nullptr
    ? nullptr
    : static_cast<const Inferences::TwoLiteralRewriteInferenceExtra*>(extra);

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 1 || parents[0] != replayInfo->premises[0]) {
    return fail("parent mismatch");
  }

  Kernel::Clause* parent = parents[0];
  const Kernel::Substitution& substitution = replayInfo->substitutionForBanksSub[0];
  Kernel::Literal* selected = rewrite->selected.selectedLiteral.selectedLiteral;
  Kernel::Literal* other = rewrite->selected.otherLiteral;
  if (selected == nullptr || other == nullptr
    || !selected->isEquality() || !other->isEquality()
    || !selected->isPositive() || !other->isPositive()) {
    return fail("selected/other literal shape");
  }

  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  unsigned selectedIndex = 0;
  unsigned otherIndex = 0;
  if (!literalIndex(parent, selected, selectedIndex)
    || !literalIndex(parent, other, otherIndex)
    || selectedIndex == otherIndex) {
    return fail("selected/other literal index");
  }

  auto substitutionSexpr = [&](std::string& rendered) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termSexpr;
      if (!certificateTermSexpr(term, termSexpr)) {
        return false;
      }
      items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : items) {
      out << ' ' << item.second;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto substitutedLiteralSexpr = [&](Kernel::Literal* literal, std::string& rendered) {
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (positive->isEquality()) {
      std::string lhs;
      std::string rhs;
      Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(0), substitution);
      Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*positive->nthArgument(1), substitution);
      if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
        return false;
      }
      Kernel::TermList equalitySort =
        Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(positive), substitution);
      std::string atom;
      if (!certificateEqualityAtomSexpr(equalitySort, lhs, rhs, atom)) {
        return false;
      }
      rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
        + atom + ")";
      return true;
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
    return certificateLiteralSexpr(substituted, rendered);
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto constraintsSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(constraints";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto subtractMultiset = [](std::vector<std::string> minuend, const std::vector<std::string>& subtrahend, std::vector<std::string>& difference) {
    for (const std::string& item : subtrahend) {
      auto it = std::find(minuend.begin(), minuend.end(), item);
      if (it == minuend.end()) {
        return false;
      }
      minuend.erase(it);
    }
    difference = minuend;
    return true;
  };
  auto isNegativeEqualityLiteral = [](const std::string& literal) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    return literal.rfind("(neg (AP (AP (TMH \"=\") ", 0) == 0
      || literal.rfind(std::string("(neg (AP (AP (TPAP (TMH \"") + megalodonEqualityHash + "\") ", 0) == 0;
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    const std::string posPrefix = "(pos ";
    const std::string negPrefix = "(neg ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else {
      return false;
    }
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    const std::string apPrefix = "(AP (AP ";
    if (literal.compare(prefix.size(), apPrefix.size(), apPrefix) != 0) {
      return false;
    }
    std::size_t equalityStart = prefix.size() + apPrefix.size();
    std::size_t equalityEnd = std::string::npos;
    if (!termEnd(equalityStart, equalityEnd) || equalityEnd >= literal.size() || literal[equalityEnd] != ' ') {
      return false;
    }
    std::string equalityHead = literal.substr(equalityStart, equalityEnd - equalityStart);
    std::size_t leftStart = equalityEnd + 1;
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd) || leftEnd + 2 >= literal.size() || literal[leftEnd] != ')' || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd) || rightEnd + 2 != literal.size() || literal[rightEnd] != ')' || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + apPrefix + equalityHead + " " + right + ") " + left + "))";
    return true;
  };

  std::vector<std::string> expected;
  std::vector<std::pair<std::string, std::string>> symmetryCandidates;
  for (unsigned i = 0; i < parent->length(); ++i) {
    if ((*parent)[i] == selected) {
      continue;
    }
    std::string rendered;
    if (!substitutedLiteralSexpr((*parent)[i], rendered)) {
      return fail("render substituted parent literal");
    }
    expected.push_back(rendered);
    if ((*parent)[i]->isEquality()) {
      std::string swapped;
      if (swappedEqualityLiteral(rendered, swapped) && rendered != swapped) {
        symmetryCandidates.push_back({rendered, swapped});
      }
    }
  }
  if (!appendCertificateSplitLiteralsSexpr(parent, expected)) {
    return fail("render split literals");
  }
  const std::vector<std::string> baseExpected = expected;

  Kernel::TermList selectedLeft = Kernel::SubstHelper::apply(*selected->nthArgument(0), substitution);
  Kernel::TermList selectedRight = Kernel::SubstHelper::apply(*selected->nthArgument(1), substitution);
  Kernel::TermList otherLeft = Kernel::SubstHelper::apply(*other->nthArgument(0), substitution);
  Kernel::TermList otherRight = Kernel::SubstHelper::apply(*other->nthArgument(1), substitution);
  Kernel::TermList introducedLeft;
  Kernel::TermList introducedRight;
  Kernel::TermList explicitSelectedLhs;
  Kernel::TermList explicitOtherRhs;
  Kernel::TermList selectedRecorded = rewrite->rewrite.lhs;
  Kernel::TermList otherRecorded = rewrite->rewrite.rewritten;
  bool selectedRecordedIsLeft = selectedRecorded == *selected->nthArgument(0);
  bool selectedRecordedIsRight = selectedRecorded == *selected->nthArgument(1);
  bool otherRecordedIsLeft = otherRecorded == *other->nthArgument(0);
  bool otherRecordedIsRight = otherRecorded == *other->nthArgument(1);
  bool foundFactoringSides = false;
  if ((selectedRecordedIsLeft || selectedRecordedIsRight)
    && (otherRecordedIsLeft || otherRecordedIsRight)) {
    Kernel::TermList selectedShared = Kernel::SubstHelper::apply(selectedRecorded, substitution);
    Kernel::TermList selectedOther = Kernel::SubstHelper::apply(
      selectedRecordedIsLeft ? *selected->nthArgument(1) : *selected->nthArgument(0),
      substitution);
    Kernel::TermList otherShared = Kernel::SubstHelper::apply(
      otherRecordedIsLeft ? *other->nthArgument(1) : *other->nthArgument(0),
      substitution);
    Kernel::TermList otherOther = Kernel::SubstHelper::apply(otherRecorded, substitution);
    if (selectedShared == otherShared) {
      introducedLeft = selectedOther;
      introducedRight = otherOther;
      explicitSelectedLhs = selectedShared;
      explicitOtherRhs = otherOther;
      foundFactoringSides = true;
    }
  }
  if (!foundFactoringSides && selectedRight == otherRight) {
    introducedLeft = selectedLeft;
    introducedRight = otherLeft;
    explicitSelectedLhs = selectedRight;
    explicitOtherRhs = otherLeft;
    foundFactoringSides = true;
  } else if (!foundFactoringSides && selectedRight == otherLeft) {
    introducedLeft = selectedLeft;
    introducedRight = otherRight;
    explicitSelectedLhs = selectedRight;
    explicitOtherRhs = otherRight;
    foundFactoringSides = true;
  } else if (!foundFactoringSides && selectedLeft == otherRight) {
    introducedLeft = selectedRight;
    introducedRight = otherLeft;
    explicitSelectedLhs = selectedLeft;
    explicitOtherRhs = otherLeft;
    foundFactoringSides = true;
  } else if (!foundFactoringSides && selectedLeft == otherLeft) {
    introducedLeft = selectedRight;
    introducedRight = otherRight;
    explicitSelectedLhs = selectedLeft;
    explicitOtherRhs = otherRight;
    foundFactoringSides = true;
  }
  if (!foundFactoringSides) {
    return fail("factoring sides not found");
  }
  std::string selectedLhsSexpr;
  std::string otherRhsSexpr;
  if (!certificateTermSexpr(explicitSelectedLhs, selectedLhsSexpr)
    || !certificateTermSexpr(explicitOtherRhs, otherRhsSexpr)) {
    return fail("render explicit factoring side terms");
  }
  Kernel::TermList equalityArgumentSort = Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(selected), substitution);
  Kernel::Literal* introduced = Kernel::Literal::createEquality(false, introducedLeft, introducedRight, equalityArgumentSort);
  std::string introducedSexpr;
  if (!certificateLiteralSexpr(introduced, introducedSexpr)) {
    return fail("render introduced equality");
  }
  expected.push_back(introducedSexpr);
  std::string swappedIntroducedSexpr;
  if (swappedEqualityLiteral(introducedSexpr, swappedIntroducedSexpr)
    && introducedSexpr != swappedIntroducedSexpr) {
    symmetryCandidates.push_back({introducedSexpr, swappedIntroducedSexpr});
  }

  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return fail("render actual clause");
  }
  const std::vector<std::string> actualNormalized = normalized(actual);
  auto canNormalizeBySymmetry =
    [&](std::vector<std::pair<std::string, std::string>>& flips) {
      std::vector<std::string> current = expected;
      flips.clear();
      for (std::size_t guard = 0;
           normalized(current) != actualNormalized && guard < symmetryCandidates.size();
           ++guard) {
        bool changed = false;
        for (const auto& candidate : symmetryCandidates) {
          if (std::find(actualNormalized.begin(), actualNormalized.end(), candidate.second) == actualNormalized.end()) {
            continue;
          }
          auto currentIt = std::find(current.begin(), current.end(), candidate.first);
          if (currentIt == current.end()) {
            continue;
          }
          *currentIt = candidate.second;
          flips.push_back(candidate);
          changed = true;
          break;
        }
        if (!changed) {
          break;
        }
      }
      return normalized(current) == actualNormalized;
  };
  std::vector<std::pair<std::string, std::string>> finalSymmetryFlips;
  const bool simpleFactoringMatches = normalized(expected) == actualNormalized
    || canNormalizeBySymmetry(finalSymmetryFlips);

  std::string subst;
  if (!substitutionSexpr(subst)) {
    return fail("render substitution");
  }
  const std::string stepBase = "u" + std::to_string(unit->number());
  std::vector<std::string> steps;
  if (simpleFactoringMatches) {
    steps.push_back(
      "(equality_factoring " + sexprQuote(stepBase)
      + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
      + " (selected " + std::to_string(selectedIndex) + ")"
      + " (other " + std::to_string(otherIndex) + ") "
      + "(selected_lhs " + selectedLhsSexpr + ") "
      + "(other_rhs " + otherRhsSexpr + ") "
      + subst
      + " (result " + clauseSexprFromLiterals(actual) + "))");
  } else {
    std::vector<std::string> constraints;
    if (!subtractMultiset(actual, baseExpected, constraints) || constraints.empty()) {
      return fail("expected clause does not normalize to actual");
    }
    if (!std::all_of(constraints.begin(), constraints.end(), isNegativeEqualityLiteral)) {
      return fail("equality factoring residual contains a non-negative-equality constraint");
    }
    steps.push_back(
      "(equality_factoring_constraints " + sexprQuote(stepBase)
      + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
      + " (selected " + std::to_string(selectedIndex) + ")"
      + " (other " + std::to_string(otherIndex) + ") "
      + "(selected_lhs " + selectedLhsSexpr + ") "
      + "(other_rhs " + otherRhsSexpr + ") "
      + subst
      + " " + constraintsSexprFromLiterals(constraints)
      + " (result " + clauseSexprFromLiterals(actual) + "))");
  }

  std::ostringstream out;
  for (std::size_t i = 0; i < steps.size(); ++i) {
    if (i != 0) {
      out << "\n  ";
    }
    out << steps[i];
  }
  result = out.str();
  return true;
}

bool MegalodonChecker::certificateTruthConflictStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL) {
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

  auto isTruthConstant = [](const std::string& rendered, const std::string& name) {
    return rendered == "(TMH \"" + name + "\")";
  };
  auto isPositiveTruthConflict = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isPositive()) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!certificateTermSexpr(*literal->nthArgument(0), lhs)
      || !certificateTermSexpr(*literal->nthArgument(1), rhs)) {
      return false;
    }
    return (isTruthConstant(lhs, "f__true") && isTruthConstant(rhs, "f__false"))
      || (isTruthConstant(lhs, "f__false") && isTruthConstant(rhs, "f__true"));
  };
  auto tryLiteral = [&](Kernel::Literal* selectedLiteral, std::string& step) {
    if (!isPositiveTruthConflict(selectedLiteral)) {
      return false;
    }

    unsigned literalIndex = 0;
    bool found = false;
    std::vector<std::string> expected;
    for (unsigned i = 0; i < parent->length(); ++i) {
      Kernel::Literal* literal = (*parent)[i];
      if (!found && literal == selectedLiteral) {
        literalIndex = i;
        found = true;
        continue;
      }
      std::string rendered;
      if (!certificateLiteralSexpr(literal, rendered)) {
        return false;
      }
      expected.push_back(rendered);
    }
    if (!found || !appendCertificateSplitLiteralsSexpr(parent, expected)) {
      return false;
    }

    std::vector<std::string> actual;
    if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
      return false;
    }
    std::sort(expected.begin(), expected.end());
    std::sort(actual.begin(), actual.end());
    if (expected != actual) {
      return false;
    }

    std::string clause;
    if (!certificateClauseSexpr(unit->asClause(), clause)) {
      return false;
    }
    step = "(truth_conflict " + sexprQuote("u" + std::to_string(unit->number()))
      + " (parent " + sexprQuote("u" + std::to_string(parent->number())) + ")"
      + " (literal " + std::to_string(literalIndex) + ")"
      + " (result " + clause + "))";
    return true;
  };

  for (Kernel::Literal* literal : parent->iterLits()) {
    if (tryLiteral(literal, result)) {
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::certificateParamodulateStepSexpr(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation*,
  std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FORWARD_DEMODULATION
      && rule != Kernel::InferenceRule::BACKWARD_DEMODULATION
      && rule != Kernel::InferenceRule::SUPERPOSITION
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

  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
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
      if (!certificateLiteralSexpr(literal, rendered)) {
        return false;
      }
      literals.push_back(rendered);
    }
    return excludedOne && appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto literalMultiplicity =
    [](const std::vector<std::string>& literals, const std::string& literal) {
      return static_cast<unsigned>(std::count(literals.begin(), literals.end(), literal));
    };
  auto removeAt = [](const std::vector<std::string>& literals, unsigned index) {
    std::vector<std::string> result;
    result.reserve(literals.size() == 0 ? 0 : literals.size() - 1);
    for (unsigned i = 0; i < literals.size(); ++i) {
      if (i != index) {
        result.push_back(literals[i]);
      }
    }
    return result;
  };
  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }
  const std::vector<std::string> actualNormalized = normalized(actual);

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
      std::string fromSexpr;
      std::string toSexpr;
      if (!certificateTermSexpr(from, fromSexpr) || !certificateTermSexpr(to, toSexpr)) {
        continue;
      }
      for (Kernel::Literal* target : targetParent->iterLits()) {
        for (unsigned direction = 0; direction < 2; ++direction) {
          Kernel::TermList selectedFrom = direction == 0 ? from : to;
          Kernel::TermList selectedTo = direction == 0 ? to : from;
          std::string selectedFromSexpr;
          std::string selectedToSexpr;
          std::vector<unsigned> nativePosition;
          std::string rewrittenTarget;
          if (!certificateTermSexpr(selectedFrom, selectedFromSexpr)
            || !certificateTermSexpr(selectedTo, selectedToSexpr)
            || !certificateRewriteLiteralAtMegalodonPosition(target, selectedFrom, selectedTo, nativePosition, rewrittenTarget)) {
            continue;
          }
          std::vector<std::string> expected;
          if (!appendClauseExcept(expected, equalityParent, equality)
            || !appendClauseExcept(expected, targetParent, target)) {
            continue;
          }
          expected.push_back(rewrittenTarget);
          bool needsDuplicateFactors = false;
          if (!sameMultiset(expected, actual)) {
            if (normalized(expected) != actualNormalized) {
              continue;
            }
            needsDuplicateFactors = true;
          }

          std::vector<std::string> steps;
          std::vector<std::string> paramodulationResult = needsDuplicateFactors ? expected : actual;
          std::string paramodulationStepId = needsDuplicateFactors
            ? "u" + std::to_string(unit->number()) + "_paramodulate"
            : "u" + std::to_string(unit->number());
          std::string currentParentId = paramodulationStepId;
          std::vector<std::string> currentClause = paramodulationResult;
          if (needsDuplicateFactors) {
            unsigned factorCount = 0;
            bool changed = true;
            while (changed) {
              changed = false;
              for (unsigned left = 0; left < currentClause.size() && !changed; ++left) {
                for (unsigned right = left + 1; right < currentClause.size(); ++right) {
                  if (currentClause[left] != currentClause[right]) {
                    continue;
                  }
                  if (literalMultiplicity(currentClause, currentClause[left]) <= literalMultiplicity(actual, currentClause[left])) {
                    continue;
                  }
                  std::vector<std::string> factored = removeAt(currentClause, right);
                  const std::string factorId = "u" + std::to_string(unit->number()) + "_factor" + std::to_string(factorCount++);
                  steps.push_back(
                    "(factor " + sexprQuote(factorId)
                    + " (parent " + sexprQuote(currentParentId) + ")"
                    + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
                    + " (result " + clauseSexprFromLiterals(factored) + "))");
                  currentClause = factored;
                  currentParentId = factorId;
                  changed = true;
                  break;
                }
              }
            }
            if (!sameMultiset(currentClause, actual)) {
              continue;
            }
          }

          if (needsDuplicateFactors) {
            steps.push_back(
              "(substitute " + sexprQuote("u" + std::to_string(unit->number()))
              + " (parent " + sexprQuote(currentParentId) + ") (subst)"
              + " (result " + clauseSexprFromLiterals(actual) + "))");
          }

          if (!needsDuplicateFactors && !sameMultiset(paramodulationResult, actual)) {
            continue;
          }

          unsigned equalityIndex = 0;
          unsigned targetIndex = 0;
          if (!literalIndex(equalityParent, equality, equalityIndex)
            || !literalIndex(targetParent, target, targetIndex)) {
            continue;
          }
          std::string paramodulate =
            "(paramodulate " + sexprQuote(paramodulationStepId)
            + " (equality " + sexprQuote("u" + std::to_string(equalityParent->number())) + " " + std::to_string(equalityIndex) + ")"
            + " (target " + sexprQuote("u" + std::to_string(targetParent->number())) + " " + std::to_string(targetIndex) + ") "
            + certificatePositionSexpr(nativePosition)
            + " (from " + selectedFromSexpr + ")"
            + " (to " + selectedToSexpr + ")"
            + " (result " + clauseSexprFromLiterals(paramodulationResult) + "))";
          std::ostringstream out;
          out << paramodulate;
          for (const std::string& step : steps) {
            out << "\n  " << step;
          }
          result = out.str();
          return true;
        }
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateForwardSubsumptionDemodulationStepsSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::FORWARD_SUBSUMPTION_DEMODULATION) {
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

  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto multisetContains = [](const std::vector<std::string>& candidate, const std::vector<std::string>& target) {
    std::map<std::string, int> counts;
    for (const std::string& literal : candidate) {
      ++counts[literal];
    }
    for (const std::string& literal : target) {
      auto found = counts.find(literal);
      if (found == counts.end() || found->second == 0) {
        return false;
      }
      --found->second;
    }
    return true;
  };
  auto substitutionSexpr = [&](const Kernel::Substitution& substitution, std::string& rendered, bool& nonIdentity) {
    std::vector<std::pair<unsigned, std::string>> items;
    Kernel::Substitution substitutionCopy = substitution;
    nonIdentity = false;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termSexpr;
      if (!certificateTermSexpr(term, termSexpr)) {
        return false;
      }
      nonIdentity = true;
      items.push_back({var, "(" + sexprQuote(variableName(var)) + " " + termSexpr + ")"});
    }
    std::sort(items.begin(), items.end(), [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : items) {
      out << ' ' << item.second;
    }
    out << ')';
    rendered = out.str();
    return true;
  };
  auto substitutedLiteralSexpr =
    [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
      if (literal->isEquality()) {
        std::string lhs;
        std::string rhs;
        Kernel::TermList lhsTerm;
        Kernel::TermList rhsTerm;
        if (!safeApplySubstitution(*literal->nthArgument(0), substitution, lhsTerm)
          || !safeApplySubstitution(*literal->nthArgument(1), substitution, rhsTerm)) {
          return false;
        }
        if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
          return false;
        }
        std::string atom;
        Kernel::TermList sort =
          Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(literal), substitution);
        if (!certificateEqualityAtomSexpr(sort, lhs, rhs, atom)) {
          return false;
        }
        rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
          + atom + ")";
        return true;
      }
      Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
      return certificateLiteralSexpr(substituted, rendered);
  };
  auto substitutedClauseLiterals =
    [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
      literals.clear();
      for (Kernel::Literal* literal : clause->iterLits()) {
        std::string rendered;
        if (!substitutedLiteralSexpr(literal, substitution, rendered)) {
          return false;
        }
        literals.push_back(rendered);
      }
      return appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto appendSubstitutedClauseExcept =
    [&](std::vector<std::string>& literals,
        Kernel::Clause* clause,
        const Kernel::Substitution& substitution,
        Kernel::Literal* excluded) {
      bool skipped = false;
      for (Kernel::Literal* literal : clause->iterLits()) {
        if (!skipped && literal == excluded) {
          skipped = true;
          continue;
        }
        std::string rendered;
        if (!substitutedLiteralSexpr(literal, substitution, rendered)) {
          return false;
        }
        literals.push_back(rendered);
      }
      return skipped && appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto matchTerm =
    [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, Kernel::Substitution& substitution) -> bool {
      if (pattern.isVar()) {
        Kernel::TermList existing;
        if (!substitution.findBinding(pattern.var(), existing)) {
          substitution.bindUnbound(pattern.var(), target);
          return true;
        }
        return existing == target;
      }
      if (pattern.isApplication() || target.isApplication()) {
        return pattern.isApplication()
          && target.isApplication()
          && self(self, pattern.lhs(), target.lhs(), substitution)
          && self(self, pattern.rhs(), target.rhs(), substitution);
      }
      if (!pattern.isTerm() || !target.isTerm()) {
        return pattern == target;
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned i = 0; i < patternTerm->arity(); ++i) {
        if (!self(self, *patternTerm->nthArgument(i), *targetTerm->nthArgument(i), substitution)) {
          return false;
        }
      }
      return true;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    const std::string typedPosPrefix =
      "(pos (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    const std::string typedNegPrefix =
      "(neg (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else if (literal.rfind(typedPosPrefix, 0) == 0 || literal.rfind(typedNegPrefix, 0) == 0) {
      const std::string typedPrefix =
        literal.rfind(typedPosPrefix, 0) == 0 ? typedPosPrefix : typedNegPrefix;
      std::size_t typeStart = typedPrefix.size();
      std::size_t typeEnd = std::string::npos;
      auto termEnd = [&](std::size_t start, std::size_t& end) {
        int depth = 0;
        for (std::size_t i = start; i < literal.size(); ++i) {
          if (literal[i] == '(') {
            ++depth;
          } else if (literal[i] == ')') {
            --depth;
            if (depth == 0) {
              end = i + 1;
              return true;
            }
          }
        }
        return false;
      };
      if (!termEnd(typeStart, typeEnd) || typeEnd + 2 >= literal.size()
        || literal[typeEnd] != ')' || literal[typeEnd + 1] != ' ') {
        return false;
      }
      prefix = literal.substr(0, typeEnd + 2);
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto factorDuplicateLiteralsToActual =
    [&](const std::vector<std::string>& start,
        const std::vector<std::string>& actual,
        std::vector<std::pair<unsigned, unsigned>>& factors,
        std::vector<std::vector<std::string>>& factorResults) {
      factors.clear();
      factorResults.clear();
      std::vector<std::string> current = start;
      while (!sameMultiset(current, actual)) {
        if (current.size() <= actual.size()) {
          return false;
        }
        bool progressed = false;
        for (unsigned i = 0; i < current.size() && !progressed; ++i) {
          for (unsigned j = i + 1; j < current.size(); ++j) {
            if (current[i] != current[j]) {
              continue;
            }
            std::vector<std::string> next = current;
            next.erase(next.begin() + j);
            if (!multisetContains(next, actual)) {
              continue;
            }
            factors.push_back({i, j});
            factorResults.push_back(next);
            current = next;
            progressed = true;
            break;
          }
        }
        if (!progressed) {
          return false;
        }
      }
      if (!factorResults.empty()) {
        factorResults.back() = actual;
      }
      return true;
  };
  auto finishCandidate =
    [&](const std::vector<std::string>& paramClause,
        const std::string& rewrittenTarget,
        const std::vector<std::string>& actual,
        std::vector<std::string>& currentClause,
        bool& needsSymmetry,
        std::vector<std::pair<unsigned, unsigned>>& factors,
        std::vector<std::vector<std::string>>& factorResults) {
      auto tryCandidate = [&](const std::vector<std::string>& candidate, bool symmetry) {
        if (sameMultiset(candidate, actual)) {
          currentClause = candidate;
          needsSymmetry = symmetry;
          factors.clear();
          factorResults.clear();
          return true;
        }
        std::vector<std::pair<unsigned, unsigned>> candidateFactors;
        std::vector<std::vector<std::string>> candidateFactorResults;
        if (!factorDuplicateLiteralsToActual(candidate, actual, candidateFactors, candidateFactorResults)) {
          return false;
        }
        currentClause = candidate;
        needsSymmetry = symmetry;
        factors = candidateFactors;
        factorResults = candidateFactorResults;
        return true;
      };
      if (tryCandidate(paramClause, false)) {
        return true;
      }
      std::string swapped;
      if (!swappedEqualityLiteral(rewrittenTarget, swapped)) {
        return false;
      }
      std::vector<std::string> symmetryClause = paramClause;
      auto rewritten = std::find(symmetryClause.begin(), symmetryClause.end(), rewrittenTarget);
      if (rewritten == symmetryClause.end()) {
        return false;
      }
      *rewritten = swapped;
      return tryCandidate(symmetryClause, true);
  };

  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }
  const std::string stepBase = "u" + std::to_string(unit->number());

  for (std::size_t sideParentIndex = 0; sideParentIndex < 2; ++sideParentIndex) {
    const std::size_t mainParentIndex = sideParentIndex == 0 ? 1 : 0;
    Kernel::Clause* sideParent = parents[sideParentIndex];
    Kernel::Clause* mainParent = parents[mainParentIndex];
    for (Kernel::Literal* equalityLiteral : sideParent->iterLits()) {
      if (!equalityLiteral->isEquality() || !equalityLiteral->isPositive()) {
        continue;
      }
      unsigned equalityIndex = 0;
      if (!literalIndex(sideParent, equalityLiteral, equalityIndex)) {
        return false;
      }
      for (unsigned direction = 0; direction < 2; ++direction) {
        Kernel::TermList fromPattern = *equalityLiteral->nthArgument(direction == 0 ? 0 : 1);
        Kernel::TermList toPattern = *equalityLiteral->nthArgument(direction == 0 ? 1 : 0);
        for (Kernel::Literal* targetLiteral : mainParent->iterLits()) {
          for (unsigned subtermSide = 0; subtermSide < (targetLiteral->isEquality() ? 2u : targetLiteral->arity()); ++subtermSide) {
            Kernel::Literal* positiveTarget = targetLiteral->isPositive()
              ? targetLiteral
              : Kernel::Literal::complementaryLiteral(targetLiteral);
            Kernel::TermList targetTerm = *positiveTarget->nthArgument(subtermSide);
            Kernel::Substitution sideSubstitution;
            if (!matchTerm(matchTerm, fromPattern, targetTerm, sideSubstitution)) {
              continue;
            }
            Kernel::TermList redex = Kernel::SubstHelper::apply(fromPattern, sideSubstitution);
            Kernel::TermList replacement = Kernel::SubstHelper::apply(toPattern, sideSubstitution);
            std::vector<unsigned> nativePosition;
            std::string rewrittenTarget;
            Kernel::Literal* rewrittenLiteral = nullptr;
            if (!certificateRewriteLiteralAtMegalodonPosition(
                  targetLiteral,
                  redex,
                  replacement,
                  nativePosition,
                  rewrittenLiteral)
              || !certificateLiteralSexpr(rewrittenLiteral, rewrittenTarget)) {
              continue;
            }
            unsigned targetIndex = 0;
            if (!literalIndex(mainParent, targetLiteral, targetIndex)) {
              return false;
            }

            std::vector<std::string> paramClause;
            Kernel::Substitution emptySubstitution;
            if (!appendSubstitutedClauseExcept(paramClause, sideParent, sideSubstitution, equalityLiteral)
              || !appendSubstitutedClauseExcept(paramClause, mainParent, emptySubstitution, targetLiteral)) {
              continue;
            }
            paramClause.push_back(rewrittenTarget);

            bool needsConclusionSymmetry = false;
            std::vector<std::pair<unsigned, unsigned>> conclusionFactors;
            std::vector<std::vector<std::string>> conclusionFactorResults;
            std::vector<std::string> paramodulationResult;
            if (!finishCandidate(
                  paramClause,
                  rewrittenTarget,
                  actual,
                  paramodulationResult,
                  needsConclusionSymmetry,
                  conclusionFactors,
                  conclusionFactorResults)) {
              continue;
            }

            std::vector<std::string> steps;
            bool nonIdentity = false;
            std::string sideSubst;
            std::vector<std::string> sideSubstituted;
            if (!substitutionSexpr(sideSubstitution, sideSubst, nonIdentity)
              || !substitutedClauseLiterals(sideParent, sideSubstitution, sideSubstituted)) {
              return false;
            }
            std::string sideParentId = "u" + std::to_string(sideParent->number());
            if (nonIdentity) {
              sideParentId = stepBase + "_side_subst";
              std::string sideSubstituteStep;
              if (!certificateSubstituteStepSexpr(
                    sideParentId,
                    "u" + std::to_string(sideParent->number()),
                    sideParent,
                    sideSubstitution,
                    sideSubstituteStep)) {
                return false;
              }
              steps.push_back(sideSubstituteStep);
            }

            std::string fromSexpr;
            std::string toSexpr;
            if (!certificateTermSexpr(redex, fromSexpr)
              || !certificateTermSexpr(replacement, toSexpr)) {
              return false;
            }
            const bool hasConclusionSteps = needsConclusionSymmetry || !conclusionFactors.empty();
            const std::string paramodulationStepId = hasConclusionSteps ? stepBase + "_paramodulate" : stepBase;
            steps.push_back(
              "(paramodulate " + sexprQuote(paramodulationStepId)
              + " (equality " + sexprQuote(sideParentId) + " " + std::to_string(equalityIndex) + ")"
              + " (target " + sexprQuote("u" + std::to_string(mainParent->number())) + " " + std::to_string(targetIndex) + ") "
              + certificatePositionSexpr(nativePosition)
              + " (from " + fromSexpr + ")"
              + " (to " + toSexpr + ")"
              + " (result " + clauseSexprFromLiterals(needsConclusionSymmetry ? paramClause : paramodulationResult) + "))");

            std::string conclusionParentId = paramodulationStepId;
            if (needsConclusionSymmetry) {
              auto rewritten = std::find(paramClause.begin(), paramClause.end(), rewrittenTarget);
              if (rewritten == paramClause.end()) {
                return false;
              }
              const std::string symmetryStepId = conclusionFactors.empty() ? stepBase : stepBase + "_symmetry_result";
              steps.push_back(
                "(equality_symmetry " + sexprQuote(symmetryStepId)
                + " (parent " + sexprQuote(paramodulationStepId) + ")"
                + " (literal " + std::to_string(rewritten - paramClause.begin()) + ")"
                + " (result " + clauseSexprFromLiterals(paramodulationResult) + "))");
              conclusionParentId = symmetryStepId;
            }

            for (std::size_t factorIndex = 0; factorIndex < conclusionFactors.size(); ++factorIndex) {
              const std::string factorId = factorIndex + 1 == conclusionFactors.size()
                ? stepBase
                : stepBase + "_factor" + std::to_string(factorIndex);
              steps.push_back(
                "(factor " + sexprQuote(factorId)
                + " (parent " + sexprQuote(conclusionParentId) + ")"
                + " (literals " + std::to_string(conclusionFactors[factorIndex].first)
                + " " + std::to_string(conclusionFactors[factorIndex].second) + ")"
                + " (result " + clauseSexprFromLiterals(conclusionFactorResults[factorIndex]) + "))");
              conclusionParentId = factorId;
            }

            std::ostringstream out;
            for (std::size_t i = 0; i < steps.size(); ++i) {
              if (i != 0) {
                out << "\n  ";
              }
              out << steps[i];
            }
            result = out.str();
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateDemodulationStepsSexpr(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (rule != Kernel::InferenceRule::FORWARD_DEMODULATION
      && rule != Kernel::InferenceRule::BACKWARD_DEMODULATION)) {
    return false;
  }

  const auto* extra = env.proofExtra.find(unit);
  const auto* rewriteExtra = extra == nullptr
    ? nullptr
    : static_cast<const Inferences::RewriteInferenceExtra*>(extra);
  bool hasReplayRewrite = replayInfo != nullptr && replayInfo->hasDemodulationRewrite;
  bool hasProofExtraRewrite = rewriteExtra != nullptr && rewriteExtra->hasReplacement;
  std::size_t replaySubstitutionCount = replayInfo == nullptr
    ? 0
    : replayInfo->substitutionForBanksSub.size();
  if ((!hasReplayRewrite && !hasProofExtraRewrite) || replaySubstitutionCount > 2) {
    return false;
  }

  std::vector<Kernel::Clause*> actualParents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      actualParents.push_back(parent->asClause());
    }
  }
  bool useActualParents = !hasReplayRewrite && actualParents.size() == 2;
  std::vector<Kernel::Clause*> premises = useActualParents
    ? actualParents
    : (replayInfo == nullptr ? std::vector<Kernel::Clause*>() : replayInfo->premises);
  if (premises.size() != 2) {
    return false;
  }

  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto substitutedClauseLiterals = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
    literals.clear();
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string rendered;
      if (literal->isEquality()) {
        std::string lhs;
        std::string rhs;
        Kernel::TermList lhsTerm;
        Kernel::TermList rhsTerm;
        if (!safeApplySubstitution(*literal->nthArgument(0), substitution, lhsTerm)
          || !safeApplySubstitution(*literal->nthArgument(1), substitution, rhsTerm)) {
          return false;
        }
        if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
          return false;
        }
        rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
          + "(AP (AP (TMH \"=\") " + lhs + ") " + rhs + "))";
      } else {
        Kernel::Literal* substituted = nullptr;
        if (!safeApplySubstitution(literal, substitution, substituted)) {
          return false;
        }
        if (!certificateLiteralSexpr(substituted, rendered)) {
          return false;
        }
      }
      literals.push_back(rendered);
    }
    return appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto appendSubstitutedClauseExcept =
    [&](std::vector<std::string>& literals,
        Kernel::Clause* clause,
        const Kernel::Substitution& substitution,
        Kernel::Literal* excluded) {
      bool skipped = false;
      for (unsigned i = 0; i < clause->length(); ++i) {
        Kernel::Literal* literal = (*clause)[i];
        if (!skipped && literal == excluded) {
          skipped = true;
          continue;
        }
        std::string rendered;
        if (literal->isEquality()) {
          std::string lhs;
          std::string rhs;
          Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(0), substitution);
          Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(1), substitution);
          if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
            return false;
          }
          std::string atom;
          Kernel::TermList sort =
            Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(literal), substitution);
          if (!certificateEqualityAtomSexpr(sort, lhs, rhs, atom)) {
            return false;
          }
          rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
            + atom + ")";
        } else {
          Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
          if (!certificateLiteralSexpr(substituted, rendered)) {
            return false;
          }
        }
        literals.push_back(rendered);
      }
      return skipped && appendCertificateSplitLiteralsSexpr(clause, literals);
    };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    static const std::string megalodonEqualityHash =
      "5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a";
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    const std::string typedPosPrefix =
      "(pos (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    const std::string typedNegPrefix =
      "(neg (AP (AP (TPAP (TMH " + sexprQuote(megalodonEqualityHash) + ") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else if (literal.rfind(typedPosPrefix, 0) == 0 || literal.rfind(typedNegPrefix, 0) == 0) {
      const std::string typedPrefix =
        literal.rfind(typedPosPrefix, 0) == 0 ? typedPosPrefix : typedNegPrefix;
      std::size_t typeStart = typedPrefix.size();
      std::size_t typeEnd = std::string::npos;
      auto termEnd = [&](std::size_t start, std::size_t& end) {
        int depth = 0;
        for (std::size_t i = start; i < literal.size(); ++i) {
          if (literal[i] == '(') {
            ++depth;
          } else if (literal[i] == ')') {
            --depth;
            if (depth == 0) {
              end = i + 1;
              return true;
            }
          }
        }
        return false;
      };
      if (!termEnd(typeStart, typeEnd) || typeEnd + 2 >= literal.size()
        || literal[typeEnd] != ')' || literal[typeEnd + 1] != ' ') {
        return false;
      }
      prefix = literal.substr(0, typeEnd + 2);
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto substitutedClauseReplacingOneLiteral =
    [&](Kernel::Clause* clause,
        const Kernel::Substitution& substitution,
        Kernel::Literal* excluded,
        const std::string& replacement,
        std::vector<std::string>& literals) {
      literals.clear();
      bool skipped = false;
      for (unsigned i = 0; i < clause->length(); ++i) {
        Kernel::Literal* literal = (*clause)[i];
        if (!skipped && literal == excluded) {
          skipped = true;
          literals.push_back(replacement);
          continue;
        }
        std::string rendered;
        if (literal->isEquality()) {
          std::string lhs;
          std::string rhs;
          Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(0), substitution);
          Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(1), substitution);
          if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
            return false;
          }
          std::string atom;
          Kernel::TermList sort =
            Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(literal), substitution);
          if (!certificateEqualityAtomSexpr(sort, lhs, rhs, atom)) {
            return false;
          }
          rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
            + atom + ")";
        } else {
          Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, substitution);
          if (!certificateLiteralSexpr(substituted, rendered)) {
            return false;
          }
        }
        literals.push_back(rendered);
      }
      return skipped && appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto positiveEqualityLiteralSexpr =
    [&](Kernel::TermList lhsTerm, Kernel::TermList rhsTerm, Kernel::TermList sort, std::string& rendered) {
      std::string lhs;
      std::string rhs;
      if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
        return false;
      }
      std::string atom;
      if (!certificateEqualityAtomSexpr(sort, lhs, rhs, atom)) {
        return false;
      }
      rendered = "(pos " + atom + ")";
      return true;
  };
  auto substitutedLiteralSexpr =
    [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
      if (literal->isEquality()) {
        std::string lhs;
        std::string rhs;
        Kernel::TermList lhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(0), substitution);
        Kernel::TermList rhsTerm = Kernel::SubstHelper::apply(*literal->nthArgument(1), substitution);
        if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
          return false;
        }
        std::string atom;
        Kernel::TermList sort =
          Kernel::SubstHelper::apply(Kernel::SortHelper::getEqualityArgumentSort(literal), substitution);
        if (!certificateEqualityAtomSexpr(sort, lhs, rhs, atom)) {
          return false;
        }
        rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
          + atom + ")";
        return true;
      }
      Kernel::Literal* substituted = nullptr;
      if (!safeApplySubstitution(literal, substitution, substituted)) {
        return false;
      }
      return certificateLiteralSexpr(substituted, rendered);
  };
  auto matchTermForDemodulation =
    [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, Kernel::Substitution& substitution) -> bool {
      if (pattern.isVar()) {
        Kernel::TermList existing;
        if (!substitution.findBinding(pattern.var(), existing)) {
          substitution.bindUnbound(pattern.var(), target);
          return true;
        }
        return existing == target;
      }
      if (pattern.isApplication() || target.isApplication()) {
        return pattern.isApplication()
          && target.isApplication()
          && self(self, pattern.lhs(), target.lhs(), substitution)
          && self(self, pattern.rhs(), target.rhs(), substitution);
      }
      if (!pattern.isTerm() || !target.isTerm()) {
        return pattern == target;
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned index = 0; index < patternTerm->arity(); ++index) {
        if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), substitution)) {
          return false;
        }
      }
      return true;
  };
  auto demodulatorSubstitution =
    [&](Kernel::Literal* equalityLiteral, Kernel::TermList leftTarget, Kernel::TermList rightTarget, Kernel::Substitution& substitution) {
      return equalityLiteral != nullptr
        && equalityLiteral->isEquality()
        && equalityLiteral->isPositive()
        && matchTermForDemodulation(matchTermForDemodulation, *equalityLiteral->nthArgument(0), leftTarget, substitution)
        && matchTermForDemodulation(matchTermForDemodulation, *equalityLiteral->nthArgument(1), rightTarget, substitution);
  };

  Kernel::Substitution emptySubstitution;
  std::vector<std::vector<Kernel::Substitution>> substitutionAlternatives;
  if (replaySubstitutionCount == 2) {
    substitutionAlternatives.push_back({
      replayInfo->substitutionForBanksSub[0],
      replayInfo->substitutionForBanksSub[1],
    });
  } else if (replaySubstitutionCount == 1) {
    substitutionAlternatives.push_back({
      replayInfo->substitutionForBanksSub[0],
      emptySubstitution,
    });
    substitutionAlternatives.push_back({
      emptySubstitution,
      replayInfo->substitutionForBanksSub[0],
    });
  } else {
    substitutionAlternatives.push_back({
      emptySubstitution,
      emptySubstitution,
    });
  }

  Kernel::TermList redex = hasReplayRewrite
    ? replayInfo->demodulationRedex
    : rewriteExtra->rewritten;
  Kernel::TermList replacement = hasReplayRewrite
    ? replayInfo->demodulationReplacement
    : rewriteExtra->replacement;

  std::vector<std::string> actual;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
    return false;
  }
  const std::string stepBase = "u" + std::to_string(unit->number());
  auto multisetContains = [](const std::vector<std::string>& candidate, const std::vector<std::string>& target) {
    std::map<std::string, int> counts;
    for (const std::string& literal : candidate) {
      ++counts[literal];
    }
    for (const std::string& literal : target) {
      auto found = counts.find(literal);
      if (found == counts.end() || found->second == 0) {
        return false;
      }
      --found->second;
    }
    return true;
  };
  auto factorDuplicateLiteralsToActual =
    [&](const std::vector<std::string>& start,
        std::vector<std::pair<unsigned, unsigned>>& factors,
        std::vector<std::vector<std::string>>& factorResults) {
      factors.clear();
      factorResults.clear();
      std::vector<std::string> current = start;
      while (!sameMultiset(current, actual)) {
        if (current.size() <= actual.size()) {
          return false;
        }
        bool progressed = false;
        for (unsigned i = 0; i < current.size() && !progressed; ++i) {
          for (unsigned j = i + 1; j < current.size(); ++j) {
            if (current[i] != current[j]) {
              continue;
            }
            std::vector<std::string> next = current;
            next.erase(next.begin() + j);
            if (!multisetContains(next, actual)) {
              continue;
            }
            factors.push_back({i, j});
            factorResults.push_back(next);
            current = next;
            progressed = true;
            break;
          }
        }
        if (!progressed) {
          return false;
        }
      }
      if (!factorResults.empty()) {
        factorResults.back() = actual;
      }
      return !factors.empty();
  };

  for (const auto& substitutions : substitutionAlternatives) {
    for (std::size_t equalityParentIndex = 0; equalityParentIndex < 2; ++equalityParentIndex) {
      const std::size_t targetParentIndex = equalityParentIndex == 0 ? 1 : 0;
      Kernel::Clause* equalityParent = premises[equalityParentIndex];
      Kernel::Clause* targetParent = premises[targetParentIndex];
      for (Kernel::Literal* equalityLiteral : equalityParent->iterLits()) {
        if (!equalityLiteral->isEquality() || !equalityLiteral->isPositive()) {
          continue;
        }

        std::vector<std::vector<Kernel::Substitution>> candidateSubstitutions;
        candidateSubstitutions.push_back(substitutions);
        if (hasProofExtraRewrite) {
          Kernel::Substitution forwardSubstitution;
          if (demodulatorSubstitution(equalityLiteral, redex, replacement, forwardSubstitution)) {
            std::vector<Kernel::Substitution> candidate;
            if (equalityParentIndex == 0) {
              candidate.push_back(forwardSubstitution);
              candidate.push_back(substitutions[targetParentIndex]);
            } else {
              candidate.push_back(substitutions[targetParentIndex]);
              candidate.push_back(forwardSubstitution);
            }
            candidateSubstitutions.push_back(candidate);
          }
          Kernel::Substitution reverseSubstitution;
          if (demodulatorSubstitution(equalityLiteral, replacement, redex, reverseSubstitution)) {
            std::vector<Kernel::Substitution> candidate;
            if (equalityParentIndex == 0) {
              candidate.push_back(reverseSubstitution);
              candidate.push_back(substitutions[targetParentIndex]);
            } else {
              candidate.push_back(substitutions[targetParentIndex]);
              candidate.push_back(reverseSubstitution);
            }
            candidateSubstitutions.push_back(candidate);
          }
        }

        for (const auto& activeSubstitutions : candidateSubstitutions) {
          Kernel::TermList equalityLeft = Kernel::SubstHelper::apply(*equalityLiteral->nthArgument(0), activeSubstitutions[equalityParentIndex]);
          Kernel::TermList equalityRight = Kernel::SubstHelper::apply(*equalityLiteral->nthArgument(1), activeSubstitutions[equalityParentIndex]);
          bool needsSymmetry = false;
          if (equalityLeft == redex && equalityRight == replacement) {
            needsSymmetry = false;
          } else if (equalityLeft == replacement && equalityRight == redex) {
            needsSymmetry = true;
          } else {
            continue;
          }

          unsigned equalityIndex = 0;
          if (!literalIndex(equalityParent, equalityLiteral, equalityIndex)) {
            return false;
          }

          for (Kernel::Literal* targetLiteral : targetParent->iterLits()) {
            Kernel::Literal* targetSubstituted = Kernel::SubstHelper::apply(targetLiteral, activeSubstitutions[targetParentIndex]);
            std::vector<unsigned> nativePosition;
            std::string rewrittenTarget;
            Kernel::Literal* rewrittenLiteral = nullptr;
            if (!certificateRewriteLiteralAtMegalodonPosition(
                  targetSubstituted,
                  redex,
                  replacement,
                  nativePosition,
                  rewrittenLiteral)
              || !certificateLiteralSexpr(rewrittenLiteral, rewrittenTarget)) {
              continue;
            }

            unsigned targetIndex = 0;
            if (!literalIndex(targetParent, targetLiteral, targetIndex)) {
              return false;
            }

            std::vector<std::string> paramClause;
            if (!appendSubstitutedClauseExcept(paramClause, equalityParent, activeSubstitutions[equalityParentIndex], equalityLiteral)
              || !appendSubstitutedClauseExcept(paramClause, targetParent, activeSubstitutions[targetParentIndex], targetLiteral)) {
              continue;
            }
            paramClause.push_back(rewrittenTarget);

            bool needsConclusionSymmetry = false;
            std::vector<std::string> paramodulationResult;
            std::vector<std::string> conclusionSymmetryResult;
            std::vector<std::pair<unsigned, unsigned>> conclusionFactors;
            std::vector<std::vector<std::string>> conclusionFactorResults;
            auto acceptConclusion =
              [&](const std::vector<std::string>& candidate, bool afterSymmetry) {
                if (sameMultiset(candidate, actual)) {
                  if (afterSymmetry) {
                    needsConclusionSymmetry = true;
                    paramodulationResult = paramClause;
                    conclusionSymmetryResult = actual;
                  } else {
                    paramodulationResult = actual;
                  }
                  return true;
                }
                std::vector<std::pair<unsigned, unsigned>> factors;
                std::vector<std::vector<std::string>> factorResults;
                if (!factorDuplicateLiteralsToActual(candidate, factors, factorResults)) {
                  return false;
                }
                if (afterSymmetry) {
                  needsConclusionSymmetry = true;
                  paramodulationResult = paramClause;
                  conclusionSymmetryResult = candidate;
                } else {
                  paramodulationResult = paramClause;
                }
                conclusionFactors = factors;
                conclusionFactorResults = factorResults;
                return true;
            };
            if (!acceptConclusion(paramClause, false)) {
              std::string swapped;
              if (!swappedEqualityLiteral(rewrittenTarget, swapped)) {
                swapped.clear();
              }
              bool acceptedSymmetry = false;
              if (!swapped.empty()) {
                std::vector<std::string> symmetryClause = paramClause;
                auto rewritten = std::find(symmetryClause.begin(), symmetryClause.end(), rewrittenTarget);
                if (rewritten != symmetryClause.end()) {
                  *rewritten = swapped;
                  acceptedSymmetry = acceptConclusion(symmetryClause, true);
                }
              }
              if (!acceptedSymmetry) {
                std::vector<std::string> steps;
                std::vector<std::string> parentIds(2);
                std::vector<std::vector<std::string>> substitutedParents(2);
                for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
                  std::string subst;
                  bool nonIdentity = false;
                  if (!certificateSubstitutionSexprForClause(activeSubstitutions[parentIndex], premises[parentIndex], subst)
                    || !substitutedClauseLiterals(premises[parentIndex], activeSubstitutions[parentIndex], substitutedParents[parentIndex])) {
                    return false;
                  }
                  nonIdentity = subst != "(subst)";
                  parentIds[parentIndex] = "u" + std::to_string(premises[parentIndex]->number());
                  if (nonIdentity) {
                    std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
                    std::string substituteStep;
                    if (!certificateSubstituteStepSexpr(
                          substituteId,
                          parentIds[parentIndex],
                          premises[parentIndex],
                          activeSubstitutions[parentIndex],
                          substituteStep)) {
                      return false;
                    }
                    steps.push_back(substituteStep);
                    parentIds[parentIndex] = substituteId;
                  }
                }

                std::string equalityParentLiteral;
                std::string equalityLiteralSexpr;
                std::string fromSexpr;
                std::string toSexpr;
                Kernel::TermList equalitySort =
                  Kernel::SubstHelper::apply(
                    Kernel::SortHelper::getEqualityArgumentSort(equalityLiteral),
                    activeSubstitutions[equalityParentIndex]);
                if (!substitutedLiteralSexpr(equalityLiteral, activeSubstitutions[equalityParentIndex], equalityParentLiteral)
                  || !positiveEqualityLiteralSexpr(redex, replacement, equalitySort, equalityLiteralSexpr)
                  || !certificateTermSexpr(redex, fromSexpr)
                  || !certificateTermSexpr(replacement, toSexpr)) {
                  return false;
                }

                std::string equalityParentId = parentIds[equalityParentIndex];
                if (needsSymmetry || equalityParentLiteral != equalityLiteralSexpr) {
                  std::vector<std::string> symmetryClause;
                  if (!substitutedClauseReplacingOneLiteral(
                        equalityParent,
                        activeSubstitutions[equalityParentIndex],
                        equalityLiteral,
                        equalityLiteralSexpr,
                        symmetryClause)) {
                    return false;
                  }
                  std::string symmetryStepId = stepBase + "_symmetry";
                  steps.push_back(
                    "(equality_symmetry " + sexprQuote(symmetryStepId)
                    + " (parent " + sexprQuote(equalityParentId) + ")"
                    + " (literal " + std::to_string(equalityIndex) + ")"
                    + " (result " + clauseSexprFromLiterals(symmetryClause) + "))");
                  equalityParentId = symmetryStepId;
                }

                std::vector<std::string> equalityRemainder;
                if (!appendSubstitutedClauseExcept(
                      equalityRemainder,
                      equalityParent,
                      activeSubstitutions[equalityParentIndex],
                      equalityLiteral)) {
                  continue;
                }

                struct TargetRewrite {
                  std::string literal;
                  std::string rewritten;
                  std::vector<unsigned> position;
                };
                std::vector<TargetRewrite> targetRewrites;
                Kernel::Literal* currentLiteral = Kernel::SubstHelper::apply(targetLiteral, activeSubstitutions[targetParentIndex]);
                std::string currentLiteralSexpr;
                if (!certificateLiteralSexpr(currentLiteral, currentLiteralSexpr)) {
                  return false;
                }
                for (unsigned guard = 0; guard < 16; ++guard) {
                  std::vector<unsigned> rewritePosition;
                  Kernel::Literal* nextLiteral = nullptr;
                  if (!certificateRewriteLiteralAtMegalodonPosition(
                        currentLiteral,
                        redex,
                        replacement,
                        rewritePosition,
                        nextLiteral)) {
                    break;
                  }
                  std::string nextLiteralSexpr;
                  if (!certificateLiteralSexpr(nextLiteral, nextLiteralSexpr)) {
                    return false;
                  }
                  targetRewrites.push_back({currentLiteralSexpr, nextLiteralSexpr, rewritePosition});
                  currentLiteral = nextLiteral;
                  currentLiteralSexpr = nextLiteralSexpr;
                }
                if (targetRewrites.empty()) {
                  continue;
                }

                std::vector<std::string> currentClause = substitutedParents[targetParentIndex];
                std::string currentParentId = parentIds[targetParentIndex];
                unsigned currentTargetIndex = targetIndex;
                bool expanded = true;
                for (std::size_t rewriteIndex = 0; rewriteIndex < targetRewrites.size(); ++rewriteIndex) {
                  const TargetRewrite& rewrite = targetRewrites[rewriteIndex];
                  if (currentTargetIndex >= currentClause.size()) {
                    expanded = false;
                    break;
                  }
                  std::vector<std::string> nextClause = currentClause;
                  nextClause.erase(nextClause.begin() + currentTargetIndex);
                  nextClause.insert(nextClause.end(), equalityRemainder.begin(), equalityRemainder.end());
                  nextClause.push_back(rewrite.rewritten);
                  const std::string rewriteId = stepBase + "_paramodulate" + std::to_string(rewriteIndex);
                  steps.push_back(
                    "(paramodulate " + sexprQuote(rewriteId)
                    + " (equality " + sexprQuote(equalityParentId) + " " + std::to_string(equalityIndex) + ")"
                    + " (target " + sexprQuote(currentParentId) + " " + std::to_string(currentTargetIndex) + ") "
                    + certificatePositionSexpr(rewrite.position)
                    + " (from " + fromSexpr + ")"
                    + " (to " + toSexpr + ")"
                    + " (result " + clauseSexprFromLiterals(nextClause) + "))");
                  currentTargetIndex = nextClause.size() - 1;
                  currentClause = nextClause;
                  currentParentId = rewriteId;
                }
                if (!expanded) {
                  continue;
                }

                auto emitFactors =
                  [&](std::vector<std::string>& candidateSteps,
                      std::string& candidateParentId,
                      const std::vector<std::pair<unsigned, unsigned>>& factors,
                      const std::vector<std::vector<std::string>>& factorResults) {
                    for (std::size_t factorIndex = 0; factorIndex < factors.size(); ++factorIndex) {
                      const std::string factorId = factorIndex + 1 == factors.size()
                        ? stepBase
                        : stepBase + "_factor" + std::to_string(factorIndex);
                      candidateSteps.push_back(
                        "(factor " + sexprQuote(factorId)
                        + " (parent " + sexprQuote(candidateParentId) + ")"
                        + " (literals " + std::to_string(factors[factorIndex].first)
                        + " " + std::to_string(factors[factorIndex].second) + ")"
                        + " (result " + clauseSexprFromLiterals(factorResults[factorIndex]) + "))");
                      candidateParentId = factorId;
                    }
                  };
                auto finishExpanded =
                  [&](std::vector<std::string>& candidateSteps,
                      std::vector<std::string> candidateClause,
                      std::string candidateParentId) {
                    if (sameMultiset(candidateClause, actual)) {
                      if (candidateParentId != stepBase) {
                        candidateSteps.push_back(
                          "(substitute " + sexprQuote(stepBase)
                          + " (parent " + sexprQuote(candidateParentId) + ") (subst)"
                          + " (result " + clauseSexprFromLiterals(actual) + "))");
                      }
                      return true;
                    }

                    std::vector<std::pair<unsigned, unsigned>> factors;
                    std::vector<std::vector<std::string>> factorResults;
                    if (factorDuplicateLiteralsToActual(candidateClause, factors, factorResults)) {
                      emitFactors(candidateSteps, candidateParentId, factors, factorResults);
                      return true;
                    }

                    for (unsigned literalIndex = 0; literalIndex < candidateClause.size(); ++literalIndex) {
                      std::string swappedLiteral;
                      if (!swappedEqualityLiteral(candidateClause[literalIndex], swappedLiteral)) {
                        continue;
                      }
                      std::vector<std::string> symmetryClause = candidateClause;
                      symmetryClause[literalIndex] = swappedLiteral;
                      std::vector<std::pair<unsigned, unsigned>> symmetryFactors;
                      std::vector<std::vector<std::string>> symmetryFactorResults;
                      if (sameMultiset(symmetryClause, actual)) {
                        candidateSteps.push_back(
                          "(equality_symmetry " + sexprQuote(stepBase)
                          + " (parent " + sexprQuote(candidateParentId) + ")"
                          + " (literal " + std::to_string(literalIndex) + ")"
                          + " (result " + clauseSexprFromLiterals(actual) + "))");
                        return true;
                      }
                      if (!factorDuplicateLiteralsToActual(symmetryClause, symmetryFactors, symmetryFactorResults)) {
                        continue;
                      }
                      const std::string symmetryStepId = stepBase + "_symmetry_result";
                      candidateSteps.push_back(
                        "(equality_symmetry " + sexprQuote(symmetryStepId)
                        + " (parent " + sexprQuote(candidateParentId) + ")"
                        + " (literal " + std::to_string(literalIndex) + ")"
                        + " (result " + clauseSexprFromLiterals(symmetryClause) + "))");
                      candidateParentId = symmetryStepId;
                      emitFactors(candidateSteps, candidateParentId, symmetryFactors, symmetryFactorResults);
                      return true;
                    }
                    return false;
                };
                if (!finishExpanded(steps, currentClause, currentParentId)) {
                  continue;
                }

                std::ostringstream out;
                for (std::size_t i = 0; i < steps.size(); ++i) {
                  if (i != 0) {
                    out << "\n  ";
                  }
                  out << steps[i];
                }
                result = out.str();
                return true;
              }
            }

            std::vector<std::string> steps;
            std::vector<std::string> parentIds(2);
            std::vector<std::vector<std::string>> substitutedParents(2);
            for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
              std::string subst;
              bool nonIdentity = false;
              if (!certificateSubstitutionSexprForClause(activeSubstitutions[parentIndex], premises[parentIndex], subst)
                || !substitutedClauseLiterals(premises[parentIndex], activeSubstitutions[parentIndex], substitutedParents[parentIndex])) {
                return false;
              }
              nonIdentity = subst != "(subst)";
              parentIds[parentIndex] = "u" + std::to_string(premises[parentIndex]->number());
              if (nonIdentity) {
                std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
                std::string substituteStep;
                if (!certificateSubstituteStepSexpr(
                      substituteId,
                      parentIds[parentIndex],
                      premises[parentIndex],
                      activeSubstitutions[parentIndex],
                      substituteStep)) {
                  return false;
                }
                steps.push_back(substituteStep);
                parentIds[parentIndex] = substituteId;
              }
            }

            std::string equalityParentLiteral;
            std::string equalityLiteralSexpr;
            std::string fromSexpr;
            std::string toSexpr;
            Kernel::TermList equalitySort =
              Kernel::SubstHelper::apply(
                Kernel::SortHelper::getEqualityArgumentSort(equalityLiteral),
                activeSubstitutions[equalityParentIndex]);
            if (!substitutedLiteralSexpr(equalityLiteral, activeSubstitutions[equalityParentIndex], equalityParentLiteral)
              || !positiveEqualityLiteralSexpr(redex, replacement, equalitySort, equalityLiteralSexpr)
              || !certificateTermSexpr(redex, fromSexpr)
              || !certificateTermSexpr(replacement, toSexpr)) {
              return false;
            }

            std::string equalityParentId = parentIds[equalityParentIndex];
            if (needsSymmetry || equalityParentLiteral != equalityLiteralSexpr) {
              std::vector<std::string> symmetryClause;
              if (!substitutedClauseReplacingOneLiteral(
                    equalityParent,
                    activeSubstitutions[equalityParentIndex],
                    equalityLiteral,
                    equalityLiteralSexpr,
                    symmetryClause)) {
                return false;
              }
              std::string symmetryStepId = stepBase + "_symmetry";
              steps.push_back(
                "(equality_symmetry " + sexprQuote(symmetryStepId)
                + " (parent " + sexprQuote(equalityParentId) + ")"
                + " (literal " + std::to_string(equalityIndex) + ")"
                + " (result " + clauseSexprFromLiterals(symmetryClause) + "))");
              equalityParentId = symmetryStepId;
            }

            const bool hasConclusionSteps = needsConclusionSymmetry || !conclusionFactors.empty();
            const std::string paramodulationStepId = hasConclusionSteps ? stepBase + "_paramodulate" : stepBase;
            steps.push_back(
              "(paramodulate " + sexprQuote(paramodulationStepId)
              + " (equality " + sexprQuote(equalityParentId) + " " + std::to_string(equalityIndex) + ")"
              + " (target " + sexprQuote(parentIds[targetParentIndex]) + " " + std::to_string(targetIndex) + ") "
              + certificatePositionSexpr(nativePosition)
              + " (from " + fromSexpr + ")"
              + " (to " + toSexpr + ")"
              + " (result " + clauseSexprFromLiterals(paramodulationResult) + "))");

            if (needsConclusionSymmetry) {
              auto rewritten = std::find(paramodulationResult.begin(), paramodulationResult.end(), rewrittenTarget);
              if (rewritten == paramodulationResult.end()) {
                return false;
              }
              const std::string symmetryStepId = conclusionFactors.empty() ? stepBase : stepBase + "_symmetry_result";
              steps.push_back(
                "(equality_symmetry " + sexprQuote(symmetryStepId)
                + " (parent " + sexprQuote(paramodulationStepId) + ")"
                + " (literal " + std::to_string(rewritten - paramodulationResult.begin()) + ")"
                + " (result " + clauseSexprFromLiterals(conclusionSymmetryResult) + "))");
            }

            std::string conclusionParentId = needsConclusionSymmetry
              ? (conclusionFactors.empty() ? stepBase : stepBase + "_symmetry_result")
              : paramodulationStepId;
            for (std::size_t factorIndex = 0; factorIndex < conclusionFactors.size(); ++factorIndex) {
              const std::string factorId = factorIndex + 1 == conclusionFactors.size()
                ? stepBase
                : stepBase + "_factor" + std::to_string(factorIndex);
              steps.push_back(
                "(factor " + sexprQuote(factorId)
                + " (parent " + sexprQuote(conclusionParentId) + ")"
                + " (literals " + std::to_string(conclusionFactors[factorIndex].first)
                + " " + std::to_string(conclusionFactors[factorIndex].second) + ")"
                + " (result " + clauseSexprFromLiterals(conclusionFactorResults[factorIndex]) + "))");
              conclusionParentId = factorId;
            }

            std::ostringstream out;
            for (std::size_t i = 0; i < steps.size(); ++i) {
              if (i != 0) {
                out << "\n  ";
              }
              out << steps[i];
            }
            result = out.str();
            return true;
          }
        }
      }
    }
  }
  return false;
}

bool MegalodonChecker::certificateSuperpositionStepsSexpr(
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
  if (targetLiteral == nullptr) {
    return false;
  }

  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto substitutedClauseLiterals = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
    literals.clear();
    for (Kernel::Literal* literal : clause->iterLits()) {
      std::string rendered;
      if (literal->isEquality()) {
        std::string lhs;
        std::string rhs;
        Kernel::TermList lhsTerm;
        Kernel::TermList rhsTerm;
        if (!safeApplySubstitution(*literal->nthArgument(0), substitution, lhsTerm)
          || !safeApplySubstitution(*literal->nthArgument(1), substitution, rhsTerm)) {
          return false;
        }
        if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
          return false;
        }
        rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
          + "(AP (AP (TMH \"=\") " + lhs + ") " + rhs + "))";
      } else {
        Kernel::Literal* substituted = nullptr;
        if (!safeApplySubstitution(literal, substitution, substituted)) {
          return false;
        }
        if (!certificateLiteralSexpr(substituted, rendered)) {
          return false;
        }
      }
      literals.push_back(rendered);
    }
    return appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto removeAt = [](std::vector<std::string> literals, unsigned index) {
    literals.erase(literals.begin() + index);
    return literals;
  };
  auto isVampireVariableName = [](const std::string& name) {
    if (name.size() < 2 || name[0] != 'X') {
      return false;
    }
    for (std::size_t i = 1; i < name.size(); ++i) {
      if (name[i] < '0' || name[i] > '9') {
        return false;
      }
    }
    return true;
  };
  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };
  auto collectSexprVariables = [&](const std::vector<std::string>& clause) {
    std::vector<std::string> variables;
    const std::string marker = "(TMH \"";
    for (const std::string& literal : clause) {
      std::size_t pos = 0;
      while ((pos = literal.find(marker, pos)) != std::string::npos) {
        pos += marker.size();
        std::size_t end = literal.find("\")", pos);
        if (end == std::string::npos) {
          break;
        }
        std::string name = literal.substr(pos, end - pos);
        if (isVampireVariableName(name)) {
          variables.push_back(name);
        }
        pos = end + 2;
      }
    }
    std::sort(variables.begin(), variables.end());
    variables.erase(std::unique(variables.begin(), variables.end()), variables.end());
    return variables;
  };
  auto applySexprVariableRenaming =
    [&](const std::vector<std::string>& source,
        const std::vector<std::pair<std::string, std::string>>& renaming) {
      std::vector<std::string> renamed = source;
      for (std::string& literal : renamed) {
        for (std::size_t i = 0; i < renaming.size(); ++i) {
          replaceAll(literal,
            "(TMH " + sexprQuote(renaming[i].first) + ")",
            "__mg_var_rename_" + std::to_string(i) + "__");
        }
        for (std::size_t i = 0; i < renaming.size(); ++i) {
          replaceAll(literal,
            "__mg_var_rename_" + std::to_string(i) + "__",
            "(TMH " + sexprQuote(renaming[i].second) + ")");
        }
      }
      return renamed;
    };
  auto findSexprVariableRenaming =
    [&](const std::vector<std::string>& source,
        const std::vector<std::string>& target,
        std::vector<std::pair<std::string, std::string>>& renaming) {
      std::vector<std::string> sourceVars = collectSexprVariables(source);
      std::vector<std::string> targetVars = collectSexprVariables(target);
      renaming.clear();
      if (sourceVars.size() != targetVars.size() || sourceVars.empty() || sourceVars.size() > 7) {
        return false;
      }

      std::vector<std::string> candidateTargets = targetVars;
      do {
        std::vector<std::pair<std::string, std::string>> candidate;
        candidate.reserve(sourceVars.size());
        bool nontrivial = false;
        for (std::size_t i = 0; i < sourceVars.size(); ++i) {
          candidate.push_back({sourceVars[i], candidateTargets[i]});
          nontrivial = nontrivial || sourceVars[i] != candidateTargets[i];
        }
        if (nontrivial && normalized(applySexprVariableRenaming(source, candidate)) == normalized(target)) {
          renaming = candidate;
          return true;
        }
      } while (std::next_permutation(candidateTargets.begin(), candidateTargets.end()));
      return false;
    };
  auto renamingSubstitutionSexpr = [&](const std::vector<std::pair<std::string, std::string>>& renaming) {
    std::ostringstream out;
    out << "(subst";
    for (const auto& item : renaming) {
      if (item.first == item.second) {
        continue;
      }
      out << " (" << sexprQuote(item.first) << " (TMH " << sexprQuote(item.second) << "))";
    }
    out << ')';
    return out.str();
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else {
      return false;
    }
    std::size_t leftStart = prefix.size();
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      if (start >= literal.size()) {
        return false;
      }
      if (literal[start] != '(') {
        end = literal.find_first_of(" )", start);
        return end != std::string::npos;
      }
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd)
      || leftEnd + 2 >= literal.size()
      || literal[leftEnd] != ')'
      || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd)
      || rightEnd + 2 != literal.size()
      || literal[rightEnd] != ')'
      || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto rewriteLiteralAtMegalodonPosition =
    [&](Kernel::Literal* literal,
        Kernel::TermList needle,
        Kernel::TermList replacement,
        std::vector<unsigned>& position,
        std::string& rendered,
        Kernel::Literal*& rewrittenLiteral) {
      Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
      if (positive->isEquality()) {
        for (unsigned side = 0; side < 2; ++side) {
          std::vector<unsigned> childPosition;
          Kernel::TermList childRewritten;
          if (!certificateRewriteTermAtMegalodonPosition(*positive->nthArgument(side), needle, replacement, childPosition, childRewritten)) {
            continue;
          }
          Kernel::TermList left = side == 0 ? childRewritten : *positive->nthArgument(0);
          Kernel::TermList right = side == 1 ? childRewritten : *positive->nthArgument(1);
          rewrittenLiteral = Kernel::Literal::createEquality(
            literal->isPositive(),
            left,
            right,
            Kernel::SortHelper::getEqualityArgumentSort(positive));
          position.clear();
          if (side == 0) {
            position.push_back(0);
            position.push_back(1);
          } else {
            position.push_back(1);
          }
          position.insert(position.end(), childPosition.begin(), childPosition.end());
          return certificateLiteralSexpr(rewrittenLiteral, rendered);
        }
        return false;
      }

      std::vector<Kernel::TermList> args;
      args.reserve(positive->arity());
      for (unsigned i = 0; i < positive->arity(); ++i) {
        args.push_back(*positive->nthArgument(i));
      }
      for (unsigned i = 0; i < positive->arity(); ++i) {
        std::vector<unsigned> childPosition;
        Kernel::TermList childRewritten;
        if (!certificateRewriteTermAtMegalodonPosition(args[i], needle, replacement, childPosition, childRewritten)) {
          continue;
        }
        args[i] = childRewritten;
        rewrittenLiteral = Kernel::Literal::create(
          positive->functor(),
          positive->arity(),
          literal->isPositive(),
          args.data());
        position.clear();
        for (unsigned j = i + 1; j < positive->arity(); ++j) {
          position.push_back(0);
        }
        position.push_back(1);
        position.insert(position.end(), childPosition.begin(), childPosition.end());
        return certificateLiteralSexpr(rewrittenLiteral, rendered);
      }
      return false;
    };
  unsigned targetIndex = 0;
  if (!literalIndex(targetParent, targetLiteral, targetIndex)) {
    return false;
  }
  Kernel::Literal* targetSubstitutedProbe = nullptr;
  if (!safeApplySubstitution(
        targetLiteral,
        replayInfo->substitutionForBanksSub[targetParentIndex],
        targetSubstitutedProbe)) {
    return false;
  }
  std::vector<Kernel::Literal*> equalityCandidates;
  if (equalityLiteral != nullptr && equalityLiteral->isEquality() && equalityLiteral->isPositive()) {
    equalityCandidates.push_back(equalityLiteral);
  }
  Kernel::Literal* recordedEqualityLiteral = equalityLiteral;
  for (Kernel::Literal* candidate : equalityParent->iterLits()) {
    if (candidate->isEquality()
      && candidate->isPositive()
      && std::find(equalityCandidates.begin(), equalityCandidates.end(), candidate) == equalityCandidates.end()) {
      equalityCandidates.push_back(candidate);
    }
  }
  unsigned equalityIndex = 0;
  bool foundEqualityCandidate = false;
  unsigned bestEqualityScore = 0;
  Kernel::TermList preferredRedex;
  Kernel::TermList preferredEqualitySide;
  if (!safeApplySubstitution(
        rewrite->rewrite.rewritten,
        replayInfo->substitutionForBanksSub[targetParentIndex],
        preferredRedex)
    || !safeApplySubstitution(
        rewrite->rewrite.lhs,
        replayInfo->substitutionForBanksSub[equalityParentIndex],
        preferredEqualitySide)) {
    return false;
  }
  auto isBooleanConstant = [](Kernel::TermList term) {
    if (term.isVar() || !term.isTerm()) {
      return false;
    }
    return term.term() == Kernel::Term::foolTrue()
      || term.term() == Kernel::Term::foolFalse();
  };
  auto candidateScore = [&](Kernel::TermList replacement) {
    if (isBooleanConstant(replacement)) {
      return 3u;
    }
    if (!replacement.isVar()) {
      return 2u;
    }
    return 1u;
  };
  auto rewriteCandidateScore = [&](Kernel::TermList source, Kernel::TermList replacement) {
    unsigned score = candidateScore(replacement);
    if (source == preferredRedex) {
      score += 200u;
    }
    if (source == preferredEqualitySide) {
      score += 120u;
    }
    if (!replacement.isVar() && replacement == preferredEqualitySide) {
      score += 80u;
    }
    if (replacement == preferredRedex) {
      score += 40u;
    }
    return score;
  };
  for (Kernel::Literal* candidate : equalityCandidates) {
    Kernel::Literal* substituted = nullptr;
    if (!safeApplySubstitution(
          candidate,
          replayInfo->substitutionForBanksSub[equalityParentIndex],
          substituted)) {
      continue;
    }
    if (!substituted->isEquality() || !substituted->isPositive()) {
      continue;
    }
    Kernel::TermList left = *substituted->nthArgument(0);
    Kernel::TermList right = *substituted->nthArgument(1);
    std::vector<unsigned> probePosition;
    Kernel::Literal* probeRewritten = nullptr;
    unsigned score = 0;
    bool rewritesLeftToRight =
      certificateRewriteLiteralAtMegalodonPosition(targetSubstitutedProbe, left, right, probePosition, probeRewritten);
    bool rewritesRightToLeft =
      certificateRewriteLiteralAtMegalodonPosition(targetSubstitutedProbe, right, left, probePosition, probeRewritten);
    if (rewritesLeftToRight) {
      score = std::max(score, rewriteCandidateScore(left, right));
      if (candidate == recordedEqualityLiteral
        && left == preferredRedex
        && !right.isVar()
        && !isBooleanConstant(right)) {
        score += 80u;
      }
    }
    if (rewritesRightToLeft) {
      score = std::max(score, rewriteCandidateScore(right, left));
      if (candidate == recordedEqualityLiteral
        && right == preferredRedex
        && !left.isVar()
        && !isBooleanConstant(left)) {
        score += 80u;
      }
    }
    unsigned candidateIndex = 0;
    if (score == 0
      || !literalIndex(equalityParent, candidate, candidateIndex)
      || (foundEqualityCandidate && score <= bestEqualityScore)) {
      continue;
    }
    equalityLiteral = candidate;
    equalityIndex = candidateIndex;
    bestEqualityScore = score;
    foundEqualityCandidate = true;
  }
  if (!foundEqualityCandidate) {
    return false;
  }

  std::vector<std::string> parentIds(2);
  std::vector<std::string> steps;
  std::vector<std::vector<std::string>> substitutedParentClauses(2);
  const std::string stepBase = "u" + std::to_string(unit->number());
  std::map<std::string, std::string> knownVariableSorts;
  auto rememberVariableSorts = [&](Kernel::Literal* literal) {
    Lib::DHMap<unsigned, Kernel::TermList> varSorts;
    Kernel::SortHelper::collectVariableSorts(literal, varSorts);
    Lib::DHMap<unsigned, Kernel::TermList>::Iterator it(varSorts);
    while (it.hasNext()) {
      unsigned var;
      Kernel::TermList sort;
      it.next(var, sort);
      std::string sortText;
      if (sortToMegalodon(sort, sortText)) {
        knownVariableSorts[variableName(var)] = sortText;
      }
    }
  };
  for (Kernel::Clause* parent : parents) {
    for (Kernel::Literal* literal : parent->iterLits()) {
      rememberVariableSorts(literal);
    }
  }
  for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
    rememberVariableSorts(literal);
  }
  std::set<std::string> emittedSyntheticVariableSorts;
  std::vector<std::string> syntheticVariableSortsMetadata;
  auto addSyntheticVariableSorts =
    [&](const std::string& id, const std::vector<std::string>& clause) {
      if (id == stepBase || !emittedSyntheticVariableSorts.insert(id).second) {
        return;
      }
      std::vector<std::string> variables = collectSexprVariables(clause);
      if (variables.empty()) {
        return;
      }
      std::ostringstream metadata;
      bool any = false;
      metadata << "(step_variable_sorts " << sexprQuote(id) << " (";
      for (const std::string& variable : variables) {
        auto sort = knownVariableSorts.find(variable);
        if (sort == knownVariableSorts.end()) {
          continue;
        }
        if (any) {
          metadata << ' ';
        }
        metadata << sexprQuote(variable + ":" + sort->second);
        any = true;
      }
      metadata << "))";
      if (any) {
        syntheticVariableSortsMetadata.push_back(metadata.str());
      }
    };
  for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
    std::string subst;
    bool nonIdentity = false;
    if (!certificateSubstitutionSexprForClause(replayInfo->substitutionForBanksSub[parentIndex], parents[parentIndex], subst)
      || !substitutedClauseLiterals(parents[parentIndex], replayInfo->substitutionForBanksSub[parentIndex], substitutedParentClauses[parentIndex])) {
      return false;
    }
    for (Kernel::Literal* literal : parents[parentIndex]->iterLits()) {
      Kernel::Literal* substituted = nullptr;
      if (!safeApplySubstitution(
            literal,
            replayInfo->substitutionForBanksSub[parentIndex],
            substituted)) {
        return false;
      }
      rememberVariableSorts(substituted);
    }
    nonIdentity = subst != "(subst)";
    parentIds[parentIndex] = "u" + std::to_string(parents[parentIndex]->number());
    if (nonIdentity) {
      const std::string substituteId = stepBase + "_subst" + std::to_string(parentIndex);
      std::string substituteStep;
      std::vector<std::string> substituteMetadata;
      if (!certificateSubstituteStepPartsSexpr(
            substituteId,
            parentIds[parentIndex],
            parents[parentIndex],
            replayInfo->substitutionForBanksSub[parentIndex],
            substituteStep,
            substituteMetadata)) {
        return false;
      }
      steps.push_back(substituteStep);
      syntheticVariableSortsMetadata.insert(
        syntheticVariableSortsMetadata.end(),
        substituteMetadata.begin(),
        substituteMetadata.end());
      parentIds[parentIndex] = substituteId;
    }
  }

  Kernel::Literal* equalitySubstituted = nullptr;
  Kernel::Literal* targetSubstituted = nullptr;
  if (!safeApplySubstitution(equalityLiteral, replayInfo->substitutionForBanksSub[equalityParentIndex], equalitySubstituted)
    || !safeApplySubstitution(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], targetSubstituted)) {
    return false;
  }
  if (!equalitySubstituted->isEquality() || !equalitySubstituted->isPositive()) {
    return false;
  }
  Kernel::TermList from = *equalitySubstituted->nthArgument(0);
  Kernel::TermList to = *equalitySubstituted->nthArgument(1);

  for (unsigned direction = 0; direction < 2; ++direction) {
    Kernel::TermList selectedFrom = direction == 0 ? from : to;
    Kernel::TermList selectedTo = direction == 0 ? to : from;
    std::string fromSexpr;
    std::string toSexpr;
    std::vector<unsigned> nativePosition;
    std::string rewrittenTarget;
    if (!certificateTermSexpr(selectedFrom, fromSexpr)
      || !certificateTermSexpr(selectedTo, toSexpr)
      || !certificateRewriteLiteralAtMegalodonPosition(targetSubstituted, selectedFrom, selectedTo, nativePosition, rewrittenTarget)) {
      continue;
    }

    std::vector<std::string> paramClause;
    for (unsigned i = 0; i < substitutedParentClauses[equalityParentIndex].size(); ++i) {
      if (i != equalityIndex) {
        paramClause.push_back(substitutedParentClauses[equalityParentIndex][i]);
      }
    }
    for (unsigned i = 0; i < substitutedParentClauses[targetParentIndex].size(); ++i) {
      if (i != targetIndex) {
        paramClause.push_back(substitutedParentClauses[targetParentIndex][i]);
      }
    }
    paramClause.push_back(rewrittenTarget);

    std::vector<std::string> actual;
    if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actual)) {
      return false;
    }
    const std::vector<std::string> actualNormalized = normalized(actual);
    auto literalMultiplicity =
      [](const std::vector<std::string>& literals, const std::string& literal) {
        return static_cast<unsigned>(std::count(literals.begin(), literals.end(), literal));
      };

    auto emitDuplicateFactors =
      [&](std::vector<std::string>& candidateSteps,
          std::vector<std::string>& current,
          std::string& currentParentId,
          const std::string& prefix) {
        unsigned factorCount = 0;
        bool changed = true;
        while (changed) {
          changed = false;
          for (unsigned left = 0; left < current.size() && !changed; ++left) {
            for (unsigned right = left + 1; right < current.size(); ++right) {
              if (current[left] != current[right]) {
                continue;
              }
              if (literalMultiplicity(current, current[left]) <= literalMultiplicity(actual, current[left])) {
                continue;
              }
              std::vector<std::string> factored = removeAt(current, right);
              const std::string factorId = prefix + "_factor" + std::to_string(factorCount++);
              candidateSteps.push_back(
                "(factor " + sexprQuote(factorId)
                + " (parent " + sexprQuote(currentParentId) + ")"
                + " (literals " + std::to_string(left) + " " + std::to_string(right) + ")"
                + " (result " + clauseSexprFromLiterals(factored) + "))");
              addSyntheticVariableSorts(factorId, factored);
              current = factored;
              currentParentId = factorId;
              changed = true;
              break;
            }
          }
        }
      };
    auto emitSymmetrySteps =
      [&](std::vector<std::string>& candidateSteps,
          std::vector<std::string>& current,
          std::string& currentParentId,
          const std::string& prefix) {
        unsigned symmetryCount = 0;
        bool any = false;
        for (unsigned guard = 0; normalized(current) != actualNormalized && guard < current.size(); ++guard) {
          bool changed = false;
          for (unsigned i = 0; i < current.size(); ++i) {
            std::string swapped;
            if (!swappedEqualityLiteral(current[i], swapped)) {
              continue;
            }
            std::vector<std::string> candidate = current;
            candidate[i] = swapped;
            if (normalized(candidate) != actualNormalized
              && std::find(actualNormalized.begin(), actualNormalized.end(), swapped) == actualNormalized.end()) {
              continue;
            }
            const std::string symmetryId = prefix + "_symmetry" + std::to_string(symmetryCount++);
            candidateSteps.push_back(
            "(equality_symmetry " + sexprQuote(symmetryId)
            + " (parent " + sexprQuote(currentParentId) + ")"
            + " (literal " + std::to_string(i) + ")"
            + " (result " + clauseSexprFromLiterals(candidate) + "))");
            addSyntheticVariableSorts(symmetryId, candidate);
            current = candidate;
            currentParentId = symmetryId;
            changed = true;
            any = true;
            break;
          }
          if (!changed) {
            break;
          }
        }
        return any;
      };
    auto canNormalizeBySymmetry = [&](std::vector<std::string> current) {
      for (unsigned guard = 0; normalized(current) != actualNormalized && guard < current.size(); ++guard) {
        bool changed = false;
        for (unsigned i = 0; i < current.size(); ++i) {
          std::string swapped;
          if (!swappedEqualityLiteral(current[i], swapped)) {
            continue;
          }
          std::vector<std::string> candidate = current;
          candidate[i] = swapped;
          if (normalized(candidate) == actualNormalized
            || std::find(actualNormalized.begin(), actualNormalized.end(), swapped) != actualNormalized.end()) {
            current = candidate;
            changed = true;
            break;
          }
        }
        if (!changed) {
          break;
        }
      }
      return normalized(current) == actualNormalized;
    };
    auto findSexprVariableRenamingThenSymmetry =
      [&](const std::vector<std::string>& source,
          const std::vector<std::string>& target,
          std::vector<std::pair<std::string, std::string>>& renaming) {
        std::vector<std::string> sourceVars = collectSexprVariables(source);
        std::vector<std::string> targetVars = collectSexprVariables(target);
        renaming.clear();
        if (sourceVars.size() != targetVars.size() || sourceVars.empty() || sourceVars.size() > 7) {
          return false;
        }
        std::vector<std::string> candidateTargets = targetVars;
        do {
          std::vector<std::pair<std::string, std::string>> candidate;
          candidate.reserve(sourceVars.size());
          bool nontrivial = false;
          for (std::size_t i = 0; i < sourceVars.size(); ++i) {
            candidate.push_back({sourceVars[i], candidateTargets[i]});
            nontrivial = nontrivial || sourceVars[i] != candidateTargets[i];
          }
          if (!nontrivial) {
            continue;
          }
          if (canNormalizeBySymmetry(applySexprVariableRenaming(source, candidate))) {
            renaming = candidate;
            return true;
          }
        } while (std::next_permutation(candidateTargets.begin(), candidateTargets.end()));
        return false;
      };
    auto finishCandidate =
      [&](const std::vector<std::string>& startSteps,
          const std::vector<std::string>& startClause,
          const std::string& startParentId,
          const std::string& prefix,
          std::vector<std::string>& finishedSteps) {
        std::vector<std::string> candidateSteps = startSteps;
        std::vector<std::string> current = startClause;
        std::string currentParentId = startParentId;

        std::vector<std::string> symmetryFirstCurrent = current;
        std::string symmetryFirstParentId = currentParentId;
        std::vector<std::string> symmetryFirstSteps = candidateSteps;
        emitSymmetrySteps(symmetryFirstSteps, symmetryFirstCurrent, symmetryFirstParentId, prefix);
        emitDuplicateFactors(symmetryFirstSteps, symmetryFirstCurrent, symmetryFirstParentId, prefix + "_post_symmetry_first");
        if (sameMultiset(symmetryFirstCurrent, actual)) {
          if (symmetryFirstParentId != stepBase) {
            symmetryFirstSteps.push_back(
              "(substitute " + sexprQuote(stepBase)
              + " (parent " + sexprQuote(symmetryFirstParentId) + ") (subst)"
              + " (result " + clauseSexprFromLiterals(actual) + "))");
          }
          finishedSteps = symmetryFirstSteps;
          return true;
        }

        emitDuplicateFactors(candidateSteps, current, currentParentId, prefix);
        if (sameMultiset(current, actual)) {
          if (currentParentId != stepBase) {
            candidateSteps.push_back(
              "(substitute " + sexprQuote(stepBase)
              + " (parent " + sexprQuote(currentParentId) + ") (subst)"
              + " (result " + clauseSexprFromLiterals(actual) + "))");
          }
          finishedSteps = candidateSteps;
          return true;
        }

        std::vector<std::string> symmetryCurrent = current;
        std::string symmetryParentId = currentParentId;
        std::vector<std::string> symmetrySteps = candidateSteps;
        emitSymmetrySteps(symmetrySteps, symmetryCurrent, symmetryParentId, prefix);
        emitDuplicateFactors(symmetrySteps, symmetryCurrent, symmetryParentId, prefix + "_post_symmetry");
        if (sameMultiset(symmetryCurrent, actual)) {
          if (symmetryParentId != stepBase) {
            symmetrySteps.push_back(
              "(substitute " + sexprQuote(stepBase)
              + " (parent " + sexprQuote(symmetryParentId) + ") (subst)"
              + " (result " + clauseSexprFromLiterals(actual) + "))");
          }
          finishedSteps = symmetrySteps;
          return true;
        }

        std::vector<std::pair<std::string, std::string>> renaming;
        if (!findSexprVariableRenaming(normalized(current), actualNormalized, renaming)
          && !findSexprVariableRenamingThenSymmetry(normalized(current), actualNormalized, renaming)) {
          return false;
        }
        std::vector<std::string> renamed = applySexprVariableRenaming(current, renaming);
        const std::string renameId = prefix + "_rename";
        candidateSteps.push_back(
          "(substitute " + sexprQuote(renameId)
          + " (parent " + sexprQuote(currentParentId) + ") "
          + renamingSubstitutionSexpr(renaming)
          + " (result " + clauseSexprFromLiterals(renamed) + "))");
        addSyntheticVariableSorts(renameId, renamed);
        current = renamed;
        currentParentId = renameId;
        emitDuplicateFactors(candidateSteps, current, currentParentId, prefix + "_post_rename");
        emitSymmetrySteps(candidateSteps, current, currentParentId, prefix + "_post_rename");
        emitDuplicateFactors(candidateSteps, current, currentParentId, prefix + "_post_rename_symmetry");
        if (!sameMultiset(current, actual)) {
          return false;
        }
        if (currentParentId != stepBase) {
          candidateSteps.push_back(
            "(substitute " + sexprQuote(stepBase)
            + " (parent " + sexprQuote(currentParentId) + ") (subst)"
            + " (result " + clauseSexprFromLiterals(actual) + "))");
        }
        finishedSteps = candidateSteps;
        return true;
      };

    std::vector<std::string> singleSteps = steps;
    if (sameMultiset(paramClause, actual)) {
      singleSteps.push_back(
        "(paramodulate " + sexprQuote(stepBase)
        + " (equality " + sexprQuote(parentIds[equalityParentIndex]) + " " + std::to_string(equalityIndex) + ")"
        + " (target " + sexprQuote(parentIds[targetParentIndex]) + " " + std::to_string(targetIndex) + ") "
        + certificatePositionSexpr(nativePosition)
        + " (from " + fromSexpr + ")"
        + " (to " + toSexpr + ")"
        + " (result " + clauseSexprFromLiterals(actual) + "))");
      steps = singleSteps;
    } else {
      singleSteps.push_back(
        "(paramodulate " + sexprQuote(stepBase + "_paramodulate")
        + " (equality " + sexprQuote(parentIds[equalityParentIndex]) + " " + std::to_string(equalityIndex) + ")"
        + " (target " + sexprQuote(parentIds[targetParentIndex]) + " " + std::to_string(targetIndex) + ") "
        + certificatePositionSexpr(nativePosition)
        + " (from " + fromSexpr + ")"
        + " (to " + toSexpr + ")"
        + " (result " + clauseSexprFromLiterals(paramClause) + "))");
      addSyntheticVariableSorts(stepBase + "_paramodulate", paramClause);
      if (!finishCandidate(singleSteps, paramClause, stepBase + "_paramodulate", stepBase, steps)) {
        std::vector<std::string> equalityRemainder;
        for (unsigned i = 0; i < substitutedParentClauses[equalityParentIndex].size(); ++i) {
          if (i != equalityIndex) {
            equalityRemainder.push_back(substitutedParentClauses[equalityParentIndex][i]);
          }
        }
        struct TargetRewrite {
          std::string literal;
          std::string rewritten;
          std::vector<unsigned> position;
        };
        std::vector<TargetRewrite> targetRewrites;
        for (unsigned i = 0; i < targetParent->length(); ++i) {
          Kernel::Literal* currentLiteral = nullptr;
          if (!safeApplySubstitution((*targetParent)[i], replayInfo->substitutionForBanksSub[targetParentIndex], currentLiteral)) {
            return false;
          }
          std::string currentLiteralSexpr;
          if (!certificateLiteralSexpr(currentLiteral, currentLiteralSexpr)) {
            return false;
          }
          for (unsigned guard = 0; guard < 16; ++guard) {
            std::vector<unsigned> rewritePosition;
            std::string nextLiteralSexpr;
            Kernel::Literal* nextLiteral = nullptr;
            if (!rewriteLiteralAtMegalodonPosition(
                  currentLiteral,
                  selectedFrom,
                  selectedTo,
                  rewritePosition,
                  nextLiteralSexpr,
                  nextLiteral)) {
              break;
            }
            targetRewrites.push_back({currentLiteralSexpr, nextLiteralSexpr, rewritePosition});
            currentLiteral = nextLiteral;
            currentLiteralSexpr = nextLiteralSexpr;
          }
        }
        if (targetRewrites.empty()) {
          continue;
        }
        std::vector<std::string> clauseWideSteps = steps;
        std::vector<std::string> currentClause = substitutedParentClauses[targetParentIndex];
        std::string currentTargetParentId = parentIds[targetParentIndex];
        std::vector<bool> usedRewrites(targetRewrites.size(), false);
        std::function<bool(
          std::vector<std::string>,
          std::vector<std::string>,
          std::string,
          std::vector<bool>,
          unsigned,
          unsigned)> finishClauseWideSearch;
        finishClauseWideSearch =
          [&](std::vector<std::string> searchSteps,
              std::vector<std::string> searchClause,
              std::string searchParentId,
              std::vector<bool> searchUsed,
              unsigned emittedRewriteCount,
              unsigned depth) {
          std::vector<std::string> candidateFinishedSteps;
          if (finishCandidate(
                searchSteps,
                searchClause,
                searchParentId,
                stepBase,
                candidateFinishedSteps)) {
            steps = candidateFinishedSteps;
            return true;
          }
          if (depth >= targetRewrites.size()) {
            return false;
          }
          for (std::size_t rewriteIndex = 0; rewriteIndex < targetRewrites.size(); ++rewriteIndex) {
            if (searchUsed[rewriteIndex]) {
              continue;
            }
            const TargetRewrite& rewrite = targetRewrites[rewriteIndex];
            auto literalIt = std::find(searchClause.begin(), searchClause.end(), rewrite.literal);
            if (literalIt == searchClause.end()) {
              continue;
            }
            unsigned currentTargetIndex = literalIt - searchClause.begin();
            std::vector<std::string> nextClause = removeAt(searchClause, currentTargetIndex);
            nextClause.insert(nextClause.end(), equalityRemainder.begin(), equalityRemainder.end());
            nextClause.push_back(rewrite.rewritten);
            const std::string rewriteId = stepBase + "_paramodulate" + std::to_string(emittedRewriteCount);
            std::vector<std::string> nextSteps = searchSteps;
            nextSteps.push_back(
              "(paramodulate " + sexprQuote(rewriteId)
              + " (equality " + sexprQuote(parentIds[equalityParentIndex]) + " " + std::to_string(equalityIndex) + ")"
              + " (target " + sexprQuote(searchParentId) + " " + std::to_string(currentTargetIndex) + ") "
              + certificatePositionSexpr(rewrite.position)
              + " (from " + fromSexpr + ")"
              + " (to " + toSexpr + ")"
              + " (result " + clauseSexprFromLiterals(nextClause) + "))");
            addSyntheticVariableSorts(rewriteId, nextClause);
            std::vector<bool> nextUsed = searchUsed;
            nextUsed[rewriteIndex] = true;
            if (finishClauseWideSearch(
                  nextSteps,
                  nextClause,
                  rewriteId,
                  nextUsed,
                  emittedRewriteCount + 1,
                  depth + 1)) {
              return true;
            }
          }
          return false;
        };
        if (!finishClauseWideSearch(
              clauseWideSteps,
              currentClause,
              currentTargetParentId,
              usedRewrites,
              0,
              0)) {
          continue;
        }
      }
    }

    std::ostringstream out;
    for (std::size_t i = 0; i < steps.size(); ++i) {
      if (i != 0) {
        out << "\n  ";
      }
      out << steps[i];
    }
    result = out.str();
    _certificateNativeMetadata.insert(
      _certificateNativeMetadata.end(),
      syntheticVariableSortsMetadata.begin(),
      syntheticVariableSortsMetadata.end());
    return true;
  }
  return false;
}

bool MegalodonChecker::certificateSuperpositionStepSexpr(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  auto fail = [&](const char* reason) {
    if (std::getenv("MEGALODON_CERT_DEBUG")
      && unit->isClause()
      && unit->inference().rule() == Kernel::InferenceRule::SUPERPOSITION) {
      std::cerr << "megalodon native superposition fallback failed for u"
                << unit->number() << ": " << reason << std::endl;
    }
    return false;
  };
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::SUPERPOSITION) {
    return fail("bad replay precondition");
  }
  const bool hasReplaySubstitutions = replayInfo != nullptr
    && replayInfo->premises.size() == 2
    && replayInfo->substitutionForBanksSub.size() == 2;
  const auto* extra = env.proofExtra.find(unit);
  if (extra == nullptr) {
    return fail("missing proof extra");
  }
  const auto* rewrite = static_cast<const Inferences::TwoLiteralRewriteInferenceExtra*>(extra);

  std::vector<Kernel::Clause*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    if (parent->isClause()) {
      parents.push_back(parent->asClause());
    }
  }
  if (parents.size() != 2
    || (hasReplaySubstitutions
      && (parents[0] != replayInfo->premises[0] || parents[1] != replayInfo->premises[1]))) {
    return fail("parent/replay mismatch");
  }
  Kernel::Substitution emptySubstitution0;
  Kernel::Substitution emptySubstitution1;
  auto directSubstitution = [&](std::size_t index) -> const Kernel::Substitution& {
    if (hasReplaySubstitutions) {
      return replayInfo->substitutionForBanksSub[index];
    }
    return index == 0 ? emptySubstitution0 : emptySubstitution1;
  };

  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto substitutedLiteralSexpr =
    [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::string& rendered) {
      if (literal->isEquality()) {
        std::string lhs;
        std::string rhs;
        Kernel::TermList lhsTerm;
        Kernel::TermList rhsTerm;
        if (!safeApplySubstitution(*literal->nthArgument(0), substitution, lhsTerm)
          || !safeApplySubstitution(*literal->nthArgument(1), substitution, rhsTerm)) {
          return false;
        }
        if (!certificateTermSexpr(lhsTerm, lhs) || !certificateTermSexpr(rhsTerm, rhs)) {
          return false;
        }
        rendered = std::string("(") + (literal->isPositive() ? "pos " : "neg ")
          + "(AP (AP (TMH \"=\") " + lhs + ") " + rhs + "))";
        return true;
      }
      Kernel::Literal* substituted = nullptr;
      if (!safeApplySubstitution(literal, substitution, substituted)) {
        return false;
      }
      return certificateLiteralSexpr(substituted, rendered);
  };
  auto substitutedClauseLiterals =
    [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
      literals.clear();
      for (Kernel::Literal* literal : clause->iterLits()) {
        std::string rendered;
        if (!substitutedLiteralSexpr(literal, substitution, rendered)) {
          return false;
        }
        literals.push_back(rendered);
      }
      return appendCertificateSplitLiteralsSexpr(clause, literals);
  };
  auto clauseSexprFromLiterals = [](const std::vector<std::string>& literals) {
    std::ostringstream out;
    out << "(clause";
    for (const std::string& literal : literals) {
      out << ' ' << literal;
    }
    out << ')';
    return out.str();
  };
  auto normalized = [](std::vector<std::string> literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return literals;
  };
  auto sameMultiset = [](std::vector<std::string> left, std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto removeAt = [](std::vector<std::string> literals, unsigned index) {
    literals.erase(literals.begin() + index);
    return literals;
  };
  auto swappedEqualityLiteral = [&](const std::string& literal, std::string& swapped) {
    const std::string posPrefix = "(pos (AP (AP (TMH \"=\") ";
    const std::string negPrefix = "(neg (AP (AP (TMH \"=\") ";
    std::string prefix;
    if (literal.rfind(posPrefix, 0) == 0) {
      prefix = posPrefix;
    } else if (literal.rfind(negPrefix, 0) == 0) {
      prefix = negPrefix;
    } else {
      return false;
    }
    auto termEnd = [&](std::size_t start, std::size_t& end) {
      int depth = 0;
      for (std::size_t i = start; i < literal.size(); ++i) {
        if (literal[i] == '(') {
          ++depth;
        } else if (literal[i] == ')') {
          --depth;
          if (depth == 0) {
            end = i + 1;
            return true;
          }
        }
      }
      return false;
    };
    std::size_t leftStart = prefix.size();
    std::size_t leftEnd = std::string::npos;
    if (!termEnd(leftStart, leftEnd) || leftEnd + 2 >= literal.size() || literal[leftEnd] != ')' || literal[leftEnd + 1] != ' ') {
      return false;
    }
    std::size_t rightStart = leftEnd + 2;
    std::size_t rightEnd = std::string::npos;
    if (!termEnd(rightStart, rightEnd) || rightEnd + 2 != literal.size() || literal[rightEnd] != ')' || literal[rightEnd + 1] != ')') {
      return false;
    }
    std::string left = literal.substr(leftStart, leftEnd - leftStart);
    std::string right = literal.substr(rightStart, rightEnd - rightStart);
    swapped = prefix + right + ") " + left + "))";
    return true;
  };
  auto sameModuloEqualitySymmetry = [&](std::vector<std::string> current, const std::vector<std::string>& actual) {
    const std::vector<std::string> actualNormalized = normalized(actual);
    for (unsigned guard = 0; normalized(current) != actualNormalized && guard < current.size(); ++guard) {
      bool changed = false;
      for (unsigned i = 0; i < current.size(); ++i) {
        std::string swapped;
        if (!swappedEqualityLiteral(current[i], swapped)) {
          continue;
        }
        std::vector<std::string> candidate = current;
        candidate[i] = swapped;
        if (normalized(candidate) == actualNormalized
          || std::find(actualNormalized.begin(), actualNormalized.end(), swapped) != actualNormalized.end()) {
          current = candidate;
          changed = true;
          break;
        }
      }
      if (!changed) {
        break;
      }
    }
    return normalized(current) == actualNormalized;
  };
  auto isVampireVariableName = [](const std::string& name) {
    if (name.size() < 2 || name[0] != 'X') {
      return false;
    }
    for (std::size_t i = 1; i < name.size(); ++i) {
      if (name[i] < '0' || name[i] > '9') {
        return false;
      }
    }
    return true;
  };
  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };
  auto collectSexprVariables = [&](const std::vector<std::string>& clause) {
    std::vector<std::string> variables;
    const std::string marker = "(TMH \"";
    for (const std::string& literal : clause) {
      std::size_t pos = 0;
      while ((pos = literal.find(marker, pos)) != std::string::npos) {
        pos += marker.size();
        std::size_t end = literal.find("\")", pos);
        if (end == std::string::npos) {
          break;
        }
        std::string name = literal.substr(pos, end - pos);
        if (isVampireVariableName(name)) {
          variables.push_back(name);
        }
        pos = end + 2;
      }
    }
    std::sort(variables.begin(), variables.end());
    variables.erase(std::unique(variables.begin(), variables.end()), variables.end());
    return variables;
  };
  auto applySexprVariableRenaming =
    [&](const std::vector<std::string>& source,
        const std::vector<std::pair<std::string, std::string>>& renaming) {
      std::vector<std::string> renamed = source;
      for (std::string& literal : renamed) {
        for (std::size_t i = 0; i < renaming.size(); ++i) {
          replaceAll(literal,
            "(TMH " + sexprQuote(renaming[i].first) + ")",
            "__mg_var_rename_" + std::to_string(i) + "__");
        }
        for (std::size_t i = 0; i < renaming.size(); ++i) {
          replaceAll(literal,
            "__mg_var_rename_" + std::to_string(i) + "__",
            "(TMH " + sexprQuote(renaming[i].second) + ")");
        }
      }
      return renamed;
    };
  auto sameModuloVariableRenaming =
    [&](const std::vector<std::string>& source,
        const std::vector<std::string>& target) {
      std::vector<std::string> sourceVars = collectSexprVariables(source);
      std::vector<std::string> targetVars = collectSexprVariables(target);
      if (sourceVars.size() != targetVars.size() || sourceVars.empty() || sourceVars.size() > 7) {
        return false;
      }
      std::vector<std::string> candidateTargets = targetVars;
      do {
        std::vector<std::pair<std::string, std::string>> candidate;
        candidate.reserve(sourceVars.size());
        bool nontrivial = false;
        for (std::size_t i = 0; i < sourceVars.size(); ++i) {
          candidate.push_back({sourceVars[i], candidateTargets[i]});
          nontrivial = nontrivial || sourceVars[i] != candidateTargets[i];
        }
        if (!nontrivial) {
          continue;
        }
        std::vector<std::string> renamed = applySexprVariableRenaming(source, candidate);
        if (normalized(renamed) == normalized(target)
          || sameModuloEqualitySymmetry(renamed, target)) {
          return true;
        }
      } while (std::next_permutation(candidateTargets.begin(), candidateTargets.end()));
      return false;
  };
  auto matchTerm =
    [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, Kernel::Substitution& bindings) -> bool {
      if (pattern.isVar()) {
        Kernel::TermList existing;
        if (!bindings.findBinding(pattern.var(), existing)) {
          bindings.bind(pattern.var(), target);
          return true;
        }
        return existing == target;
      }
      if (!pattern.isTerm() || !target.isTerm()) {
        return pattern == target;
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned i = 0; i < patternTerm->arity(); ++i) {
        if (!self(self, *patternTerm->nthArgument(i), *targetTerm->nthArgument(i), bindings)) {
          return false;
        }
      }
      return true;
  };
  auto termContainsVariable =
    [&](auto&& self, Kernel::TermList term, unsigned variable) -> bool {
      if (term.isVar()) {
        return term.var() == variable;
      }
      if (!term.isTerm()) {
        return false;
      }
      Kernel::Term* asTerm = term.term();
      for (unsigned i = 0; i < asTerm->arity(); ++i) {
        if (self(self, *asTerm->nthArgument(i), variable)) {
          return true;
        }
      }
      return false;
  };
  auto termContainsMatcher =
    [&](auto&& self, Kernel::TermList term, Kernel::TermList target, Kernel::Substitution& bindings) -> bool {
      if (!term.isVar()) {
        Kernel::Substitution candidate = bindings;
        if (matchTerm(matchTerm, term, target, candidate)) {
          Kernel::Substitution candidateCopy = candidate;
          for (auto [var, replacement] : iterTraits(candidateCopy.items())) {
            bindings.rebind(var, replacement);
          }
          return true;
        }
      }
      if (!term.isTerm()) {
        return false;
      }
      Kernel::Term* asTerm = term.term();
      for (unsigned i = 0; i < asTerm->arity(); ++i) {
        if (self(self, *asTerm->nthArgument(i), target, bindings)) {
          return true;
        }
      }
      return false;
  };
  auto collectTermPatternMatchers =
    [&](auto&& self,
        Kernel::TermList term,
        Kernel::TermList pattern,
        Kernel::Substitution bindings,
        std::vector<Kernel::Substitution>& matches) -> void {
      Kernel::Substitution candidate = bindings;
      if ((!pattern.isVar() || !termContainsVariable(termContainsVariable, term, pattern.var()))
        && matchTerm(matchTerm, pattern, term, candidate)) {
        matches.push_back(candidate);
      }
      if (!term.isTerm()) {
        return;
      }
      Kernel::Term* asTerm = term.term();
      for (unsigned i = 0; i < asTerm->arity(); ++i) {
        self(self, *asTerm->nthArgument(i), pattern, bindings, matches);
      }
  };
  auto literalContainsMatcher =
    [&](Kernel::Literal* literal, Kernel::TermList target, Kernel::Substitution& bindings) {
      Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
      for (unsigned i = 0; i < positive->arity(); ++i) {
        if (termContainsMatcher(termContainsMatcher, *positive->nthArgument(i), target, bindings)) {
          return true;
        }
      }
      return false;
  };
  auto literalPatternMatchers =
    [&](Kernel::Literal* literal, Kernel::TermList pattern, std::vector<Kernel::Substitution>& matches) {
      Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
      for (unsigned i = 0; i < positive->arity(); ++i) {
        Kernel::Substitution empty;
        collectTermPatternMatchers(collectTermPatternMatchers, *positive->nthArgument(i), pattern, empty, matches);
      }
  };
  auto substitutionWithExtras =
    [&](const Kernel::Substitution& substitution, const Kernel::Substitution& extras) {
      Kernel::Substitution merged = substitution;
      Kernel::Substitution extrasCopy = extras;
      for (auto [var, term] : iterTraits(extrasCopy.items())) {
        merged.rebind(var, term);
      }
      return merged;
  };
  std::vector<std::string> actualDirect;
  if (!appendCertificateClauseLiteralsSexpr(unit->asClause(), actualDirect)) {
    return fail("render actual clause");
  }
  const bool debugDirectSuperposition = std::getenv("MEGALODON_CERT_DEBUG") != nullptr;
  unsigned directRewriteCandidates = 0;
  unsigned directMatcherCandidates = 0;
  unsigned directClauseCandidates = 0;
  std::string firstDirectExpected;
  std::string firstDirectActual;
  for (std::size_t targetParentIndex = 0; targetParentIndex < 2; ++targetParentIndex) {
    const std::size_t equalityParentIndex = targetParentIndex == 0 ? 1 : 0;
    std::vector<std::string> targetClause;
    std::vector<std::string> equalityClause;
    if (!substitutedClauseLiterals(parents[targetParentIndex], directSubstitution(targetParentIndex), targetClause)
      || !substitutedClauseLiterals(parents[equalityParentIndex], directSubstitution(equalityParentIndex), equalityClause)) {
      continue;
    }
    for (unsigned targetIndex = 0; targetIndex < parents[targetParentIndex]->length(); ++targetIndex) {
      Kernel::Literal* targetSubstituted = nullptr;
      if (!safeApplySubstitution(
            (*parents[targetParentIndex])[targetIndex],
            directSubstitution(targetParentIndex),
            targetSubstituted)) {
        continue;
      }
      for (unsigned equalityIndex = 0; equalityIndex < parents[equalityParentIndex]->length(); ++equalityIndex) {
        Kernel::Literal* equalityLiteralCandidate = (*parents[equalityParentIndex])[equalityIndex];
        if (!equalityLiteralCandidate->isEquality() || !equalityLiteralCandidate->isPositive()) {
          continue;
        }
        Kernel::Literal* equalitySubstituted = nullptr;
        if (!safeApplySubstitution(
              equalityLiteralCandidate,
              directSubstitution(equalityParentIndex),
              equalitySubstituted)) {
          continue;
        }
        if (!equalitySubstituted->isEquality() || !equalitySubstituted->isPositive()) {
          continue;
        }
        for (unsigned direction = 0; direction < 2; ++direction) {
          Kernel::TermList from = *equalitySubstituted->nthArgument(direction == 0 ? 0 : 1);
          Kernel::TermList to = *equalitySubstituted->nthArgument(direction == 0 ? 1 : 0);
          struct DirectSuperpositionCandidate {
            Kernel::Substitution targetMatcher;
            Kernel::Substitution equalityMatcher;
            Kernel::Literal* effectiveTarget;
            Kernel::TermList effectiveFrom;
            Kernel::TermList effectiveTo;
            bool usesMatcher;
          };
          std::vector<DirectSuperpositionCandidate> candidates;
          candidates.push_back({Kernel::Substitution(), Kernel::Substitution(), targetSubstituted, from, to, false});

          Kernel::Substitution targetMatcher;
          if (literalContainsMatcher(targetSubstituted, from, targetMatcher)) {
            Kernel::Literal* effectiveTarget = nullptr;
            Kernel::TermList effectiveFrom;
            Kernel::TermList effectiveTo;
            if (!safeApplySubstitution(targetSubstituted, targetMatcher, effectiveTarget)
              || !safeApplySubstitution(from, targetMatcher, effectiveFrom)
              || !safeApplySubstitution(to, targetMatcher, effectiveTo)) {
              continue;
            }
            candidates.push_back({
              targetMatcher,
              Kernel::Substitution(),
              effectiveTarget,
              effectiveFrom,
              effectiveTo,
              true});
          }

          std::vector<Kernel::Substitution> equalityMatchers;
          literalPatternMatchers(targetSubstituted, from, equalityMatchers);
          for (Kernel::Substitution& equalityMatcher : equalityMatchers) {
            Kernel::TermList effectiveFrom;
            Kernel::TermList effectiveTo;
            if (!safeApplySubstitution(from, equalityMatcher, effectiveFrom)
              || !safeApplySubstitution(to, equalityMatcher, effectiveTo)) {
              continue;
            }
            candidates.push_back({
              Kernel::Substitution(),
              equalityMatcher,
              targetSubstituted,
              effectiveFrom,
              effectiveTo,
              true});
          }

          for (const DirectSuperpositionCandidate& candidate : candidates) {
            std::vector<unsigned> position;
            std::string rewrittenTarget;
            if (!certificateRewriteLiteralAtMegalodonPosition(
                  candidate.effectiveTarget,
                  candidate.effectiveFrom,
                  candidate.effectiveTo,
                  position,
                  rewrittenTarget)) {
              continue;
            }
            if (candidate.usesMatcher) {
              ++directMatcherCandidates;
            }
            ++directRewriteCandidates;
            Kernel::Substitution effectiveTargetSubstitution =
              substitutionWithExtras(directSubstitution(targetParentIndex), candidate.targetMatcher);
            Kernel::Substitution effectiveEqualitySubstitution =
              substitutionWithExtras(directSubstitution(equalityParentIndex), candidate.equalityMatcher);
            auto forceEqualityOrientation =
              [&](Kernel::Substitution& substitution) {
                for (unsigned orientation = 0; orientation < 2; ++orientation) {
                  Kernel::Substitution orientationSubstitution;
                  Kernel::TermList originalFrom =
                    *equalityLiteralCandidate->nthArgument(orientation == 0 ? 0 : 1);
                  Kernel::TermList originalTo =
                    *equalityLiteralCandidate->nthArgument(orientation == 0 ? 1 : 0);
                  if (!matchTerm(matchTerm, originalFrom, candidate.effectiveFrom, orientationSubstitution)
                    || !matchTerm(matchTerm, originalTo, candidate.effectiveTo, orientationSubstitution)) {
                    continue;
                  }
                  Kernel::Substitution orientationCopy = orientationSubstitution;
                  for (auto [var, term] : iterTraits(orientationCopy.items())) {
                    substitution.rebind(var, term);
                  }
                  return true;
                }
                return false;
              };
            forceEqualityOrientation(effectiveEqualitySubstitution);
            std::vector<std::string> effectiveTargetClause;
            std::vector<std::string> effectiveEqualityClause;
            if (!substitutedClauseLiterals(parents[targetParentIndex], effectiveTargetSubstitution, effectiveTargetClause)
              || !substitutedClauseLiterals(parents[equalityParentIndex], effectiveEqualitySubstitution, effectiveEqualityClause)) {
              continue;
            }
            std::vector<std::string> expected = removeAt(effectiveEqualityClause, equalityIndex);
            std::vector<std::string> targetRest = removeAt(effectiveTargetClause, targetIndex);
            expected.insert(expected.end(), targetRest.begin(), targetRest.end());
            expected.push_back(rewrittenTarget);
            std::vector<std::vector<std::string>> expectedVariants;
            expectedVariants.push_back(expected);
            std::vector<std::string> simultaneousExpected;
            std::string simultaneousRewrittenTarget;
            Kernel::Literal* simultaneousTarget =
              Kernel::EqHelper::replace(candidate.effectiveTarget, candidate.effectiveFrom, candidate.effectiveTo);
            if (simultaneousTarget != candidate.effectiveTarget
              && certificateLiteralSexpr(simultaneousTarget, simultaneousRewrittenTarget)
              && simultaneousRewrittenTarget != rewrittenTarget) {
              simultaneousExpected = removeAt(effectiveEqualityClause, equalityIndex);
              simultaneousExpected.insert(simultaneousExpected.end(), targetRest.begin(), targetRest.end());
              simultaneousExpected.push_back(simultaneousRewrittenTarget);
              expectedVariants.push_back(simultaneousExpected);
            }
            ++directClauseCandidates;
            if (debugDirectSuperposition && firstDirectExpected.empty()) {
              firstDirectExpected = clauseSexprFromLiterals(expected);
              firstDirectActual = clauseSexprFromLiterals(actualDirect);
            }
            const bool directExpectedMatches =
              sameMultiset(expected, actualDirect)
              || sameModuloEqualitySymmetry(expected, actualDirect)
              || sameModuloVariableRenaming(expected, actualDirect);
            const bool simultaneousExpectedMatches =
              !simultaneousExpected.empty()
              && (sameMultiset(simultaneousExpected, actualDirect)
                || sameModuloEqualitySymmetry(simultaneousExpected, actualDirect)
                || sameModuloVariableRenaming(simultaneousExpected, actualDirect));
            if (!directExpectedMatches && !simultaneousExpectedMatches) {
              continue;
            }
            std::string fromSexpr;
            std::string toSexpr;
            if (!certificateTermSexpr(candidate.effectiveFrom, fromSexpr)
              || !certificateTermSexpr(candidate.effectiveTo, toSexpr)) {
              continue;
            }
            const std::string stepBase = "u" + std::to_string(unit->number());
            std::vector<std::string> steps;
            auto maybeSubstituteParent =
              [&](const std::string& substituteId,
                  Kernel::Clause* parent,
                  const Kernel::Substitution& substitution,
                  std::string& parentId) {
                std::string substitutionSexpr;
                if (!certificateSubstitutionSexprForClause(substitution, parent, substitutionSexpr)) {
                  return false;
                }
                if (substitutionSexpr == "(subst)") {
                  return true;
                }
                std::string substituteStep;
                if (!certificateSubstituteStepSexpr(substituteId, parentId, parent, substitution, substituteStep)) {
                  return false;
                }
                steps.push_back(substituteStep);
                parentId = substituteId;
                return true;
              };

            std::string targetParentId = "u" + std::to_string(parents[targetParentIndex]->number());
            std::string equalityParentId = "u" + std::to_string(parents[equalityParentIndex]->number());
            if (!maybeSubstituteParent(
                  stepBase + "_target_subst",
                  parents[targetParentIndex],
                  effectiveTargetSubstitution,
                  targetParentId)
              || !maybeSubstituteParent(
                  stepBase + "_equality_subst",
                  parents[equalityParentIndex],
                  effectiveEqualitySubstitution,
                  equalityParentId)) {
              continue;
            }
            if (directExpectedMatches) {
              steps.push_back(
                "(paramodulate " + sexprQuote(stepBase)
                + " (equality " + sexprQuote(equalityParentId)
                + " " + std::to_string(equalityIndex) + ")"
                + " (target " + sexprQuote(targetParentId)
                + " " + std::to_string(targetIndex) + ") "
                + certificatePositionSexpr(position)
                + " (from " + fromSexpr + ")"
                + " (to " + toSexpr + ")"
                + " (result " + clauseSexprFromLiterals(expected) + "))");
            } else {
              struct DirectRewriteStep {
                std::vector<unsigned> position;
                std::string rewritten;
              };
              std::vector<DirectRewriteStep> rewriteSteps;
              Kernel::Literal* currentLiteral = candidate.effectiveTarget;
              for (unsigned guard = 0; guard < 16; ++guard) {
                std::vector<unsigned> stepPosition;
                std::string stepRewritten;
                Kernel::Literal* nextLiteral = nullptr;
                if (!certificateRewriteLiteralAtMegalodonPosition(
                      currentLiteral,
                      candidate.effectiveFrom,
                      candidate.effectiveTo,
                      stepPosition,
                      nextLiteral)
                  || !certificateLiteralSexpr(nextLiteral, stepRewritten)) {
                  break;
                }
                rewriteSteps.push_back({stepPosition, stepRewritten});
                currentLiteral = nextLiteral;
                if (stepRewritten == simultaneousRewrittenTarget) {
                  break;
                }
              }
              if (rewriteSteps.empty()
                || rewriteSteps.back().rewritten != simultaneousRewrittenTarget) {
                continue;
              }

              std::vector<std::string> equalityRemainder = removeAt(effectiveEqualityClause, equalityIndex);
              std::vector<std::string> currentClause = effectiveTargetClause;
              std::string currentParentId = targetParentId;
              unsigned currentTargetIndex = targetIndex;
              bool expanded = true;
              for (std::size_t rewriteIndex = 0; rewriteIndex < rewriteSteps.size(); ++rewriteIndex) {
                if (currentTargetIndex >= currentClause.size()) {
                  expanded = false;
                  break;
                }
                std::vector<std::string> nextClause = removeAt(currentClause, currentTargetIndex);
                nextClause.insert(nextClause.end(), equalityRemainder.begin(), equalityRemainder.end());
                nextClause.push_back(rewriteSteps[rewriteIndex].rewritten);
                const std::string rewriteId = rewriteIndex + 1 == rewriteSteps.size()
                  ? stepBase
                  : stepBase + "_paramodulate" + std::to_string(rewriteIndex);
                steps.push_back(
                  "(paramodulate " + sexprQuote(rewriteId)
                  + " (equality " + sexprQuote(equalityParentId)
                  + " " + std::to_string(equalityIndex) + ")"
                  + " (target " + sexprQuote(currentParentId)
                  + " " + std::to_string(currentTargetIndex) + ") "
                  + certificatePositionSexpr(rewriteSteps[rewriteIndex].position)
                  + " (from " + fromSexpr + ")"
                  + " (to " + toSexpr + ")"
                  + " (result " + clauseSexprFromLiterals(nextClause) + "))");
                currentClause = nextClause;
                currentParentId = rewriteId;
                currentTargetIndex = currentClause.size() - 1;
              }
              if (!expanded || !sameMultiset(currentClause, actualDirect)) {
                continue;
              }
            }

            std::ostringstream out;
            for (std::size_t i = 0; i < steps.size(); ++i) {
              if (i != 0) {
                out << "\n  ";
              }
              out << steps[i];
            }
            result = out.str();
            return true;
          }
        }
      }
    }
  }
  if (debugDirectSuperposition) {
    std::cerr << "megalodon native direct superposition search failed for u"
              << unit->number()
              << ": rewrites=" << directRewriteCandidates
              << " matcher_rewrites=" << directMatcherCandidates
              << " clause_candidates=" << directClauseCandidates
              << std::endl;
    if (!firstDirectExpected.empty()) {
      std::cerr << "megalodon native direct superposition first expected for u"
                << unit->number() << ": " << firstDirectExpected << std::endl;
      std::cerr << "megalodon native direct superposition actual for u"
                << unit->number() << ": " << firstDirectActual << std::endl;
    }
  }

  if (!hasReplaySubstitutions) {
    return fail("bad replay precondition");
  }
  if (rewrite == nullptr) {
    return fail("missing proof extra");
  }
  Kernel::Literal* targetLiteral = rewrite->selected.selectedLiteral.selectedLiteral;
  Kernel::Literal* equalityLiteral = rewrite->selected.otherLiteral;
  if (targetLiteral == nullptr || equalityLiteral == nullptr || !equalityLiteral->isEquality() || !equalityLiteral->isPositive()) {
    return fail("recorded target/equality shape");
  }

  unsigned targetIndex = 0;
  std::size_t targetParentIndex = 0;
  bool foundTarget = false;
  for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
    unsigned index = 0;
    if (literalIndex(parents[parentIndex], targetLiteral, index)) {
      targetParentIndex = parentIndex;
      targetIndex = index;
      foundTarget = true;
    }
  }
  if (!foundTarget) {
    return fail("target literal not found in parents");
  }
  const std::size_t equalityParentIndex = targetParentIndex == 0 ? 1 : 0;
  std::vector<unsigned> equalityCandidates;
  unsigned recordedEqualityIndex = 0;
  if (literalIndex(parents[equalityParentIndex], equalityLiteral, recordedEqualityIndex)) {
    equalityCandidates.push_back(recordedEqualityIndex);
  }
  for (unsigned i = 0; i < parents[equalityParentIndex]->length(); ++i) {
    Kernel::Literal* candidate = (*parents[equalityParentIndex])[i];
    if (candidate->isEquality()
      && candidate->isPositive()
      && std::find(equalityCandidates.begin(), equalityCandidates.end(), i) == equalityCandidates.end()) {
      equalityCandidates.push_back(i);
    }
  }

  Kernel::Literal* targetSubstituted = nullptr;
  if (!safeApplySubstitution(
        targetLiteral,
        replayInfo->substitutionForBanksSub[targetParentIndex],
        targetSubstituted)) {
    return fail("substitute target literal");
  }

  std::vector<std::string> targetClause;
  std::vector<std::string> equalityClause;
  if (!substitutedClauseLiterals(parents[targetParentIndex], replayInfo->substitutionForBanksSub[targetParentIndex], targetClause)
    || !substitutedClauseLiterals(parents[equalityParentIndex], replayInfo->substitutionForBanksSub[equalityParentIndex], equalityClause)) {
    return fail("render substituted clauses");
  }

  for (unsigned equalityIndex : equalityCandidates) {
    Kernel::Literal* equalityLiteralCandidate = (*parents[equalityParentIndex])[equalityIndex];
    Kernel::Literal* equalitySubstituted = nullptr;
    if (!safeApplySubstitution(
          equalityLiteralCandidate,
          replayInfo->substitutionForBanksSub[equalityParentIndex],
          equalitySubstituted)) {
      continue;
    }
    if (!equalitySubstituted->isEquality() || !equalitySubstituted->isPositive()) {
      continue;
    }
    auto matchTerm =
      [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, Kernel::Substitution& bindings) -> bool {
        if (pattern.isVar()) {
          Kernel::TermList existing;
          if (!bindings.findBinding(pattern.var(), existing)) {
            bindings.bind(pattern.var(), target);
            return true;
          }
          return existing == target;
        }
        if (!pattern.isTerm() || !target.isTerm()) {
          return pattern == target;
        }
        Kernel::Term* patternTerm = pattern.term();
        Kernel::Term* targetTerm = target.term();
        if (patternTerm->functor() != targetTerm->functor()
          || patternTerm->arity() != targetTerm->arity()) {
          return false;
        }
        for (unsigned i = 0; i < patternTerm->arity(); ++i) {
          if (!self(self, *patternTerm->nthArgument(i), *targetTerm->nthArgument(i), bindings)) {
            return false;
          }
        }
        return true;
    };
    Kernel::TermList preferredRedex;
    if (!safeApplySubstitution(
          rewrite->rewrite.rewritten,
          replayInfo->substitutionForBanksSub[targetParentIndex],
          preferredRedex)) {
      return fail("substitute preferred redex");
    }
    auto substitutionWithExtras =
      [&](const Kernel::Substitution& substitution,
          const std::vector<std::pair<unsigned, Kernel::TermList>>& extraBindings) {
        Kernel::Substitution merged = substitution;
        for (const auto& binding : extraBindings) {
          merged.rebind(binding.first, binding.second);
        }
        return merged;
    };
    auto emitSuperposition =
      [&](Kernel::TermList from,
          Kernel::TermList to,
          const std::vector<unsigned>& position,
          const Kernel::Substitution& equalitySubstitution,
          const std::vector<std::pair<unsigned, Kernel::TermList>>& extraEqualityBindings) {
      std::string fromSexpr;
      std::string toSexpr;
      std::string resultClause;
      if (!certificateTermSexpr(from, fromSexpr)
        || !certificateTermSexpr(to, toSexpr)
        || !certificateClauseSexpr(unit->asClause(), resultClause)) {
        return false;
      }
      const std::string stepBase = "u" + std::to_string(unit->number());
      std::vector<std::string> steps;
      auto maybeSubstituteParent =
        [&](const std::string& substituteId,
            Kernel::Clause* parent,
            const Kernel::Substitution& substitution,
            std::string& parentId) {
          std::string substitutionSexpr;
          if (!certificateSubstitutionSexprForClause(substitution, parent, substitutionSexpr)) {
            return false;
          }
          if (substitutionSexpr == "(subst)") {
            return true;
          }
          std::string substituteStep;
          if (!certificateSubstituteStepSexpr(substituteId, parentId, parent, substitution, substituteStep)) {
            return false;
          }
          steps.push_back(substituteStep);
          parentId = substituteId;
          return true;
        };

      std::string targetParentId = "u" + std::to_string(parents[targetParentIndex]->number());
      std::string equalityParentId = "u" + std::to_string(parents[equalityParentIndex]->number());
      Kernel::Substitution effectiveEqualitySubstitution =
        substitutionWithExtras(equalitySubstitution, extraEqualityBindings);
      for (unsigned orientation = 0; orientation < 2; ++orientation) {
        Kernel::Substitution orientationSubstitution;
        Kernel::TermList originalFrom =
          *equalityLiteralCandidate->nthArgument(orientation == 0 ? 0 : 1);
        Kernel::TermList originalTo =
          *equalityLiteralCandidate->nthArgument(orientation == 0 ? 1 : 0);
        if (!matchTerm(matchTerm, originalFrom, from, orientationSubstitution)
          || !matchTerm(matchTerm, originalTo, to, orientationSubstitution)) {
          continue;
        }
        Kernel::Substitution orientationCopy = orientationSubstitution;
        for (auto [var, term] : iterTraits(orientationCopy.items())) {
          effectiveEqualitySubstitution.rebind(var, term);
        }
        break;
      }
      if (!maybeSubstituteParent(
            stepBase + "_target_subst",
            parents[targetParentIndex],
            replayInfo->substitutionForBanksSub[targetParentIndex],
            targetParentId)
        || !maybeSubstituteParent(
            stepBase + "_equality_subst",
            parents[equalityParentIndex],
            effectiveEqualitySubstitution,
            equalityParentId)) {
        return false;
      }
      steps.push_back(
        "(paramodulate " + sexprQuote(stepBase)
        + " (equality " + sexprQuote(equalityParentId)
        + " " + std::to_string(equalityIndex) + ")"
        + " (target " + sexprQuote(targetParentId)
        + " " + std::to_string(targetIndex) + ") "
        + certificatePositionSexpr(position)
        + " (from " + fromSexpr + ")"
        + " (to " + toSexpr + ")"
        + " (result " + resultClause + "))");
      std::ostringstream out;
      for (std::size_t i = 0; i < steps.size(); ++i) {
        if (i != 0) {
          out << "\n  ";
        }
        out << steps[i];
      }
      result = out.str();
      return true;
    };
    for (unsigned phase = 0; phase < 2; ++phase) {
      for (unsigned direction = 0; direction < 2; ++direction) {
        Kernel::TermList from = *equalitySubstituted->nthArgument(direction == 0 ? 0 : 1);
        Kernel::TermList to = *equalitySubstituted->nthArgument(direction == 0 ? 1 : 0);
        std::vector<unsigned> position;
        std::string rewrittenTarget;
        if (phase == 0) {
          Kernel::Substitution matcherSubstitution;
          if (!matchTerm(matchTerm, from, preferredRedex, matcherSubstitution)) {
            continue;
          }
          Kernel::TermList instantiatedTo;
          if (!safeApplySubstitution(to, matcherSubstitution, instantiatedTo)) {
            continue;
          }
          if (!certificateRewriteLiteralAtMegalodonPosition(targetSubstituted, preferredRedex, instantiatedTo, position, rewrittenTarget)) {
            continue;
          }
          Kernel::Substitution equalityOutputSubstitution = replayInfo->substitutionForBanksSub[equalityParentIndex];
          Kernel::Substitution matcherCopy = matcherSubstitution;
          std::vector<std::pair<unsigned, Kernel::TermList>> extraEqualityBindings;
          Kernel::TermList originalFrom = *equalityLiteralCandidate->nthArgument(direction == 0 ? 0 : 1);
          Kernel::TermList originalTo = *equalityLiteralCandidate->nthArgument(direction == 0 ? 1 : 0);
          for (auto [var, term] : iterTraits(matcherCopy.items())) {
            equalityOutputSubstitution.rebind(var, term);
            extraEqualityBindings.push_back({var, term});
          }
          if (originalFrom.isVar() && originalFrom != preferredRedex) {
            extraEqualityBindings.push_back({originalFrom.var(), preferredRedex});
          }
          if (originalTo.isVar() && originalTo != instantiatedTo) {
            extraEqualityBindings.push_back({originalTo.var(), instantiatedTo});
          }
          if (from.isVar() && from != preferredRedex) {
            extraEqualityBindings.push_back({from.var(), preferredRedex});
          }
          if (emitSuperposition(preferredRedex, instantiatedTo, position, equalityOutputSubstitution, extraEqualityBindings)) {
            return true;
          }
          return false;
        }
        if (!certificateRewriteLiteralAtMegalodonPosition(targetSubstituted, from, to, position, rewrittenTarget)) {
          continue;
        }
        if (emitSuperposition(from, to, position, replayInfo->substitutionForBanksSub[equalityParentIndex], {})) {
          return true;
        }
        return false;
      }
    }
  }
  return fail("no equality candidate rewrites to actual result");
}

bool MegalodonChecker::certificateNativeStepSexpr(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  return certificateInputStepSexpr(unit, result)
    || certificateFormulaInputStepSexpr(unit, result)
    || certificateFormulaTermInputStepSexpr(unit, result)
    || certificateRectifyFormulaStepSexpr(unit, result)
    || certificateFormulaCopyStepSexpr(unit, result)
    || certificateFormulaTermCopyStepSexpr(unit, result)
    || certificateFoolBoolStepSexpr(unit, result)
    || certificateFoolFormulaStepSexpr(unit, result)
    || certificateEnnfFormulaStepSexpr(unit, result)
    || certificateSkolemFormulaStepSexpr(unit, result)
    || certificateCnfLiteralStepSexpr(unit, result)
    || certificateCnfFormulaClauseStepSexpr(unit, result)
    || certificatePredicateDefinitionStepSexpr(unit, result)
    || certificatePredicateDefinitionFoldStepSexpr(unit, result)
    || certificateDefinitionInputStepSexpr(unit, result)
    || certificateInequalitySplittingNameIntroductionStepSexpr(unit, result)
    || certificateInequalitySplittingStepSexpr(unit, result)
    || certificateExtensionalityResolutionStepsSexpr(unit, result)
    || certificateAvatarComponentStepSexpr(unit, result)
    || certificateAvatarSplitStepSexpr(unit, result)
    || certificateAvatarContradictionStepSexpr(unit, result)
    || certificateAvatarRefutationStepSexpr(unit, result)
    || certificateCondensationStepSexpr(unit, result)
    || certificateDefinitionRewriteStepsSexpr(unit, result)
    || certificateDefinitionFoldingStepsSexpr(unit, result)
    || certificateFoolExhaustivenessStepSexpr(unit, result)
    || certificateFoolDistinctnessStepSexpr(unit, result)
    || certificateBoolSimplificationStepSexpr(unit, result)
    || certificateUnitResultingResolutionStepsSexpr(unit, result, true)
    || certificateResolveStepSexpr(unit, result)
    || certificateSubstitutedResolutionStepsSexpr(unit, replayInfo, result)
    || certificateSatSubsumptionResolutionStepSexpr(unit, result)
    || certificateFactorStepSexpr(unit, result)
    || certificateTrivialInequalityRemovalStepsSexpr(unit, result)
    || certificateEqualityResolutionStepSexpr(unit, replayInfo, result)
    || certificateEqualityFactoringStepSexpr(unit, replayInfo, result)
    || certificateTruthConflictStepSexpr(unit, result)
    || certificateForwardSubsumptionDemodulationStepsSexpr(unit, result)
    || certificateDemodulationStepsSexpr(unit, replayInfo, result)
    || certificateSuperpositionStepsSexpr(unit, replayInfo, result)
    || certificateSuperpositionStepSexpr(unit, replayInfo, result)
    || certificateParamodulateStepSexpr(unit, replayInfo, result);
}

std::string MegalodonChecker::certificateJsonWithStepIds(Kernel::Unit* unit, const std::string& certificateJson)
{
  auto hasTopLevelField = [](const std::string& object, const std::string& field) {
    bool inString = false;
    bool escaped = false;
    unsigned depth = 0;
    for (std::size_t i = 0; i < object.size(); ++i) {
      char ch = object[i];
      if (inString) {
        if (escaped) {
          escaped = false;
        } else if (ch == '\\') {
          escaped = true;
        } else if (ch == '"') {
          inString = false;
        }
        continue;
      }
      if (ch == '"') {
        if (depth == 1 && object.compare(i, field.size(), field) == 0) {
          return true;
        }
        inString = true;
      } else if (ch == '{' || ch == '[') {
        ++depth;
      } else if ((ch == '}' || ch == ']') && depth > 0) {
        --depth;
      }
    }
    return false;
  };
  auto topLevelStringFieldEquals = [&](const std::string& object, const std::string& field, const std::string& expected) {
    bool inString = false;
    bool escaped = false;
    unsigned depth = 0;
    for (std::size_t i = 0; i < object.size(); ++i) {
      char ch = object[i];
      if (inString) {
        if (escaped) {
          escaped = false;
        } else if (ch == '\\') {
          escaped = true;
        } else if (ch == '"') {
          inString = false;
        }
        continue;
      }
      if (ch == '"') {
        if (depth == 1 && object.compare(i, field.size(), field) == 0) {
          std::size_t cursor = i + field.size();
          while (cursor < object.size() && std::isspace(static_cast<unsigned char>(object[cursor]))) {
            ++cursor;
          }
          if (cursor >= object.size() || object[cursor] != ':') {
            return false;
          }
          ++cursor;
          while (cursor < object.size() && std::isspace(static_cast<unsigned char>(object[cursor]))) {
            ++cursor;
          }
          std::string quotedExpected = quote(expected);
          return object.compare(cursor, quotedExpected.size(), quotedExpected) == 0;
        }
        inString = true;
      } else if (ch == '{' || ch == '[') {
        ++depth;
      } else if ((ch == '}' || ch == ']') && depth > 0) {
        --depth;
      }
    }
    return false;
  };

  auto addFields = [&](const std::string& object, const std::string& id) {
    if (object.empty() || object.front() != '{') {
      return object;
    }
    std::vector<std::string> fields;
    if (!hasTopLevelField(object, "\"id\"")) {
      fields.push_back("\"id\":" + quote(id));
    }
    const std::string unitId = "u" + std::to_string(unit->number());
    if ((id == unitId || topLevelStringFieldEquals(object, "\"id\"", unitId))
      && unit->isClause()
      && !hasTopLevelField(object, "\"clause\"")) {
      std::string clauseJson;
      if (certificateClauseJson(unit->asClause(), clauseJson)) {
        fields.push_back("\"clause\":" + clauseJson);
      }
    }
    if (fields.empty()) {
      return object;
    }
    std::ostringstream out;
    out << '{';
    for (std::size_t i = 0; i < fields.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << fields[i];
    }
    out << ',' << object.substr(1);
    return out.str();
  };

  if (certificateJson.empty()) {
    return certificateJson;
  }

  const std::string baseId = "u" + std::to_string(unit->number());
  if (certificateJson.front() == '{') {
    return addFields(certificateJson, baseId);
  }
  if (certificateJson.front() != '[') {
    return certificateJson;
  }

  std::vector<std::string> objects;
  bool inString = false;
  bool escaped = false;
  int depth = 0;
  std::size_t objectStart = std::string::npos;
  for (std::size_t i = 0; i < certificateJson.size(); ++i) {
    char ch = certificateJson[i];
    if (inString) {
      if (escaped) {
        escaped = false;
      } else if (ch == '\\') {
        escaped = true;
      } else if (ch == '"') {
        inString = false;
      }
      continue;
    }
    if (ch == '"') {
      inString = true;
    } else if (ch == '{') {
      if (depth == 0) {
        objectStart = i;
      }
      ++depth;
    } else if (ch == '}') {
      --depth;
      if (depth == 0 && objectStart != std::string::npos) {
        objects.push_back(certificateJson.substr(objectStart, i - objectStart + 1));
        objectStart = std::string::npos;
      }
    }
  }
  if (objects.empty()) {
    return certificateJson;
  }

  std::ostringstream out;
  out << '[';
  for (std::size_t i = 0; i < objects.size(); ++i) {
    if (i != 0) {
      out << ',';
    }
    out << addFields(objects[i], baseId + "_cert" + std::to_string(i));
  }
  out << ']';
  return out.str();
}

void MegalodonChecker::printMegalodonCertificateJson() const
{
  out << "megalodon_certificate_json_start.\n";
  out << "{\"format\":\"vampire-megalodon-certificate\","
      << "\"version\":1,"
      << "\"steps\":[";
  bool first = true;
  for (std::size_t i = 0; i < _certificateSteps.size(); ++i) {
    std::string chunk = _certificateSteps[i];
    if (chunk.size() >= 2 && chunk.front() == '[' && chunk.back() == ']') {
      chunk = chunk.substr(1, chunk.size() - 2);
      if (chunk.empty()) {
        continue;
      }
    }
    if (!first) {
      out << ',';
    }
    first = false;
    out << chunk;
  }
  out << "]}\n";
  out << "megalodon_certificate_json_end.\n";
}

void MegalodonChecker::printMegalodonCertificateNativeSexpr() const
{
  out << "megalodon_certificate_native_sexpr_start.\n";
  out << "(certificate vampire-megalodon 1\n";
  out << "  (problem \"vampire-native-certificate\")\n";
  for (const std::string& metadata : _certificateNativeMetadata) {
    out << "  " << metadata << "\n";
  }
  for (const std::string& step : _certificateNativeSteps) {
    out << "  " << step << "\n";
  }
  out << ")\n";
  out << "megalodon_certificate_native_sexpr_end.\n";
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
    std::ostringstream metadata;
    metadata << "(step_extra " << sexprQuote("u" + std::to_string(u->number()))
             << ' ' << sexprQuote(kind) << " (";
    for (std::size_t i = 0; i < fields.size(); ++i) {
      if (i != 0) {
        out << ',';
        metadata << ' ';
      }
      out << quote(fields[i]);
      metadata << sexprQuote(fields[i]);
    }
    out << "]).\n";
    metadata << "))";
    _certificateNativeMetadata.push_back(metadata.str());
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
  auto literalSexprForKernel = [&](Kernel::Literal* literal, std::string& text) {
    if (literal == nullptr) {
      return false;
    }
    return certificateLiteralSexpr(literal, text);
  };
  auto termSexprForKernel = [&](Kernel::TermList term, std::string& text) {
    return certificateTermSexpr(term, text);
  };
  auto clauseSexprForKernel = [&](Kernel::Clause* clause, std::string& text) {
    if (clause == nullptr) {
      return false;
    }
    return certificateClauseSexpr(clause, text);
  };
  auto literalVectorClauseSexprForKernel =
    [&](const std::vector<Kernel::Literal*>& literals, std::string& text) {
      std::ostringstream out;
      out << "(clause";
      for (Kernel::Literal* literal : literals) {
        std::string rendered;
        if (!literalSexprForKernel(literal, rendered)) {
          return false;
        }
        out << ' ' << rendered;
      }
      out << ')';
      text = out.str();
      return true;
    };
  auto substitutionSexprForKernel = [&](const Kernel::Substitution& substitution, std::string& text) {
    return certificateSubstitutionSexpr(substitution, text);
  };
  auto satClauseSexprForKernel = [](SAT::SATClause* clause, std::string& text) {
    if (clause == nullptr) {
      return false;
    }
    std::ostringstream out;
    out << "(sat_clause";
    for (SATLiteral literal : clause->iter()) {
      out << " (lit " << literal.var() << ' ' << (literal.positive() ? "true" : "false") << ')';
    }
    out << ')';
    text = out.str();
    return true;
  };
  auto setKernelParents = [&](MegalodonKernelSyntax::MegalodonKernelStep& step) {
    MegalodonKernelSyntax::setParentList(step);
    for (std::size_t parentIndex = 0; parentIndex < parentClauses.size(); ++parentIndex) {
      Kernel::Clause* parent = parentClauses[parentIndex];
      MegalodonKernelSyntax::RenderedKernelParent renderedParent;
      renderedParent.unit = MegalodonKernelSyntax::unitRef("u" + std::to_string(parent->number()));
      std::string clause;
      if (clauseSexprForKernel(parent, clause)) {
        renderedParent.hasClause = true;
        renderedParent.clause = MegalodonKernelSyntax::clause(clause);
      }
      std::vector<std::string> literals;
      if (appendCertificateClauseLiteralsSexpr(parent, literals)) {
        renderedParent.hasLiterals = true;
        renderedParent.literals = MegalodonKernelSyntax::literals(literals);
      }
      if (
        info != nullptr
        && parentIndex < info->premises.size()
        && parentIndex < info->substitutionForBanksSub.size()
      ) {
        std::string subst;
        if (substitutionSexprForKernel(info->substitutionForBanksSub[parentIndex], subst)) {
          renderedParent.hasSubstitution = true;
          renderedParent.substitution = MegalodonKernelSyntax::substitution(subst);
        }
        std::vector<std::string> substitutedLiterals;
        for (Kernel::Literal* literal : info->premises[parentIndex]->iterLits()) {
          Kernel::Literal* substituted =
            Kernel::SubstHelper::apply(literal, info->substitutionForBanksSub[parentIndex]);
          std::string rendered;
          if (literalSexprForKernel(substituted, rendered)) {
            substitutedLiterals.push_back(rendered);
          }
        }
        if (appendCertificateSplitLiteralsSexpr(info->premises[parentIndex], substitutedLiterals)) {
          renderedParent.hasSubstitutedLiterals = true;
          renderedParent.substitutedLiterals = MegalodonKernelSyntax::literals(substitutedLiterals);
        }
      }
      MegalodonKernelSyntax::addParent(step, renderedParent);
    }
  };
  auto setKernelConclusion = [&](MegalodonKernelSyntax::MegalodonKernelStep& step) {
    MegalodonKernelSyntax::RenderedKernelConclusion conclusion;
    conclusion.unit = MegalodonKernelSyntax::unitRef("u" + std::to_string(u->number()));
    conclusion.vampireRule = std::string(Kernel::ruleName(u->inference().rule()));
    if (u->isClause()) {
      std::string clause;
      if (clauseSexprForKernel(u->asClause(), clause)) {
        conclusion.hasClause = true;
        conclusion.clause = MegalodonKernelSyntax::clause(clause);
      }
      std::vector<std::string> resultLiterals;
      if (appendCertificateClauseLiteralsSexpr(u->asClause(), resultLiterals)) {
        conclusion.hasResultLiterals = true;
        conclusion.resultLiterals = MegalodonKernelSyntax::literals(resultLiterals);
      }
    } else {
      std::string formula;
      if (certificateFormulaTermSexpr(u->getFormula(), formula)) {
        conclusion.hasFormula = true;
        conclusion.formula = MegalodonKernelSyntax::formula(formula);
      }
    }
    MegalodonKernelSyntax::setConclusion(step, conclusion);
  };
  auto addKernelLiteralFields =
    [&](std::vector<std::string>& fields,
        const std::string& prefix,
        Kernel::Literal* literal,
        int preferredParentIndex = -1) {
      MegalodonKernelSyntax::RenderedKernelLiteralSelection selection;
      selection.prefix = prefix;
      std::string rendered;
      if (literalSexprForKernel(literal, rendered)) {
        selection.hasLiteral = true;
        selection.literal = MegalodonKernelSyntax::literal(rendered);
      }
      auto [parentIndex, literalIndex] = literalPosition(literal, preferredParentIndex);
      if (parentIndex >= 0 && literalIndex >= 0) {
        selection.hasParent = true;
        selection.parentIndex = parentIndex;
        selection.literalIndex = literalIndex;
        selection.parentUnit =
          MegalodonKernelSyntax::unitRef("u" + std::to_string(parentClauses[parentIndex]->number()));
        bool addedSubstituted = false;
        if (info != nullptr
          && static_cast<std::size_t>(parentIndex) < info->premises.size()
          && static_cast<std::size_t>(parentIndex) < info->substitutionForBanksSub.size()) {
          Kernel::Literal* substituted =
            Kernel::SubstHelper::apply(literal, info->substitutionForBanksSub[parentIndex]);
          if (literalSexprForKernel(substituted, rendered)) {
            selection.hasSubstituted = true;
            selection.substituted = MegalodonKernelSyntax::literal(rendered);
            addedSubstituted = true;
          }
        }
        if (!addedSubstituted && literalSexprForKernel(literal, rendered)) {
          selection.hasSubstituted = true;
          selection.substituted = MegalodonKernelSyntax::literal(rendered);
        }
      }
      MegalodonKernelSyntax::appendLiteralSelection(fields, selection);
    };
  auto addKernelTermField = [&](std::vector<std::string>& fields, const std::string& name, Kernel::TermList term) {
    std::string rendered;
    if (termSexprForKernel(term, rendered)) {
      fields.push_back(name + "=" + rendered);
    }
  };
  auto addKernelPrimitiveParentSubstitutions =
    [&](MegalodonKernelSyntax::MegalodonKernelStep& step) {
    if (info == nullptr || info->premises.size() != info->substitutionForBanksSub.size()) {
      return;
    }
    for (std::size_t parentIndex = 0; parentIndex < info->substitutionForBanksSub.size(); ++parentIndex) {
      std::string subst;
      if (substitutionSexprForKernel(info->substitutionForBanksSub[parentIndex], subst)) {
        MegalodonKernelSyntax::addPrimitiveParentSubstitution(
          step,
          MegalodonKernelSyntax::primitiveParentSubstitution(
            parentIndex,
            MegalodonKernelSyntax::substitution(subst)));
      }
    }
  };
  auto populateKernelSatProofSteps = [&](MegalodonKernelSyntax::RenderedKernelAvatarRefutation& refutation, SAT::SATClause* root) {
    struct CompareSATClauses {
      bool operator()(SAT::SATClause* left, SAT::SATClause* right) const
      {
        return left->number < right->number;
      }
    };

    std::set<SAT::SATClause*, CompareSATClauses> proof;
    std::vector<SAT::SATClause*> todo;
    todo.push_back(root);
    while (!todo.empty()) {
      SAT::SATClause* current = todo.back();
      todo.pop_back();
      if (current == nullptr || !proof.insert(current).second) {
        continue;
      }
      SAT::SATInference* inference = current->inference();
      if (inference == nullptr || inference->getType() != SAT::SATInference::PROP_INF) {
        continue;
      }
      SAT::PropInference* prop = static_cast<SAT::PropInference*>(inference);
      for (SAT::SATClause* parent : iterTraits(prop->getPremises()->iter())) {
        todo.push_back(parent);
      }
    }

    std::size_t proofIndex = 0;
    for (SAT::SATClause* clause : proof) {
      MegalodonKernelSyntax::RenderedKernelSatProofStep step;
      step.index = proofIndex;
      step.id = clause->number;
      std::string rendered;
      if (satClauseSexprForKernel(clause, rendered)) {
        step.hasClause = true;
        step.clause = MegalodonKernelSyntax::clause(rendered);
      }
      SAT::SATInference* inference = clause->inference();
      if (inference == nullptr) {
        step.kind = "unknown";
        refutation.proofSteps.push_back(step);
        ++proofIndex;
        continue;
      }
      switch (inference->getType()) {
        case SAT::SATInference::FO_CONVERSION: {
          step.kind = "input";
          Kernel::Unit* origin = inference->foConversion()->getOrigin();
          if (origin != nullptr) {
            step.hasOriginUnit = true;
            step.originUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(origin->number()));
          }
          break;
        }
        case SAT::SATInference::PROP_INF: {
          step.kind = "rup";
          SAT::PropInference* prop = static_cast<SAT::PropInference*>(inference);
          unsigned parentIndex = 0;
          for (SAT::SATClause* parent : iterTraits(prop->getPremises()->iter())) {
            MegalodonKernelSyntax::RenderedKernelSatProofParent renderedParent;
            renderedParent.index = parentIndex;
            renderedParent.id = parent->number;
            if (satClauseSexprForKernel(parent, rendered)) {
              renderedParent.hasClause = true;
              renderedParent.clause = MegalodonKernelSyntax::clause(rendered);
            }
            step.parents.push_back(renderedParent);
            ++parentIndex;
          }
          break;
        }
      }
      refutation.proofSteps.push_back(step);
      ++proofIndex;
    }
  };
  auto addKernelSuperpositionRewriteFields =
    [&](std::vector<std::string>& fields,
        Kernel::Literal* targetLiteral,
        Kernel::Literal* equalityLiteral) {
      if (info == nullptr || info->premises.size() != info->substitutionForBanksSub.size()) {
        return;
      }
      auto [targetParent, targetIndex] = literalPosition(targetLiteral, 0);
      auto [equalityParent, equalityIndex] = literalPosition(equalityLiteral, 1);
      if (targetParent < 0
        || targetIndex < 0
        || equalityParent < 0
        || equalityIndex < 0
        || static_cast<std::size_t>(targetParent) >= info->substitutionForBanksSub.size()
        || static_cast<std::size_t>(equalityParent) >= info->substitutionForBanksSub.size()) {
        return;
      }
      Kernel::Literal* targetSubstituted =
        Kernel::SubstHelper::apply(targetLiteral, info->substitutionForBanksSub[targetParent]);
      Kernel::Literal* equalitySubstituted =
        Kernel::SubstHelper::apply(equalityLiteral, info->substitutionForBanksSub[equalityParent]);
      if (targetSubstituted == nullptr
        || equalitySubstituted == nullptr
        || !equalitySubstituted->isEquality()
        || !equalitySubstituted->isPositive()) {
        return;
      }

      MegalodonKernelSyntax::RenderedKernelRewrite rewrite;
      rewrite.hasTargetLocation = true;
      rewrite.targetParentIndex = targetParent;
      rewrite.targetLiteralIndex = targetIndex;
      rewrite.hasEqualityLocation = true;
      rewrite.equalityParentIndex = equalityParent;
      rewrite.equalityLiteralIndex = equalityIndex;

      std::string rendered;
      if (literalSexprForKernel(targetSubstituted, rendered)) {
        rewrite.hasTargetSubstituted = true;
        rewrite.targetSubstituted = MegalodonKernelSyntax::literal(rendered);
      }
      if (literalSexprForKernel(equalitySubstituted, rendered)) {
        rewrite.hasEqualitySubstituted = true;
        rewrite.equalitySubstituted = MegalodonKernelSyntax::literal(rendered);
      }

      for (unsigned direction = 0; direction < 2; ++direction) {
        Kernel::TermList from = *equalitySubstituted->nthArgument(direction == 0 ? 0 : 1);
        Kernel::TermList to = *equalitySubstituted->nthArgument(direction == 0 ? 1 : 0);
        std::vector<unsigned> position;
        Kernel::Literal* rewrittenTarget = nullptr;
        if (!certificateRewriteLiteralAtMegalodonPosition(
              targetSubstituted,
              from,
              to,
              position,
              rewrittenTarget)) {
          continue;
        }
        rewrite.hasDirection = true;
        rewrite.direction = direction == 0 ? "forward" : "backward";
        rewrite.hasPosition = true;
        rewrite.position = MegalodonKernelSyntax::position(certificatePositionSexpr(position));
        if (termSexprForKernel(from, rendered)) {
          rewrite.hasFrom = true;
          rewrite.from = MegalodonKernelSyntax::term(rendered);
        }
        if (termSexprForKernel(to, rendered)) {
          rewrite.hasTo = true;
          rewrite.to = MegalodonKernelSyntax::term(rendered);
        }
        if (literalSexprForKernel(rewrittenTarget, rendered)) {
          rewrite.hasRewrittenTarget = true;
          rewrite.rewrittenTarget = MegalodonKernelSyntax::literal(rendered);
        }
        MegalodonKernelSyntax::appendRewrite(fields, rewrite);
        return;
      }
    };
  auto addKernelDemodulationRewriteFields = [&](std::vector<std::string>& fields) {
    if (info == nullptr
      || !info->hasDemodulationRewrite
      || info->premises.size() != info->substitutionForBanksSub.size()) {
      return;
    }
    MegalodonKernelSyntax::RenderedKernelRewrite rewrite;
    bool addedEquality = false;
    for (std::size_t parentIndex = 0; parentIndex < info->premises.size() && !addedEquality; ++parentIndex) {
      Kernel::Clause* premise = info->premises[parentIndex];
      for (unsigned literalIndex = 0; literalIndex < premise->length(); ++literalIndex) {
        Kernel::Literal* literal = (*premise)[literalIndex];
        if (!literal->isEquality() || !literal->isPositive()) {
          continue;
        }
        Kernel::Literal* substituted =
          Kernel::SubstHelper::apply(literal, info->substitutionForBanksSub[parentIndex]);
        if (substituted == nullptr || !substituted->isEquality() || !substituted->isPositive()) {
          continue;
        }
        Kernel::TermList left = *substituted->nthArgument(0);
        Kernel::TermList right = *substituted->nthArgument(1);
        if (!((Kernel::TermList::equals(left, info->demodulationRedex)
              && Kernel::TermList::equals(right, info->demodulationReplacement))
            || (Kernel::TermList::equals(right, info->demodulationRedex)
              && Kernel::TermList::equals(left, info->demodulationReplacement))
            || (Kernel::TermList::equals(left, info->demodulationRuleLhs)
              && Kernel::TermList::equals(right, info->demodulationRuleRhs))
            || (Kernel::TermList::equals(right, info->demodulationRuleLhs)
              && Kernel::TermList::equals(left, info->demodulationRuleRhs)))) {
          continue;
        }
        std::string rendered;
        if (literalSexprForKernel(substituted, rendered)) {
          rewrite.hasEqualitySubstituted = true;
          rewrite.equalitySubstituted = MegalodonKernelSyntax::literal(rendered);
        }
        rewrite.hasEqualityLocation = true;
        rewrite.equalityParentIndex = static_cast<int>(parentIndex);
        rewrite.equalityLiteralIndex = static_cast<int>(literalIndex);
        addedEquality = true;
        break;
      }
    }
    std::string rendered;
    if (termSexprForKernel(info->demodulationRedex, rendered)) {
      rewrite.hasFrom = true;
      rewrite.from = MegalodonKernelSyntax::term(rendered);
    }
    if (termSexprForKernel(info->demodulationReplacement, rendered)) {
      rewrite.hasTo = true;
      rewrite.to = MegalodonKernelSyntax::term(rendered);
    }
    for (std::size_t parentIndex = 0; parentIndex < info->premises.size(); ++parentIndex) {
      Kernel::Clause* premise = info->premises[parentIndex];
      for (unsigned literalIndex = 0; literalIndex < premise->length(); ++literalIndex) {
        Kernel::Literal* literal = (*premise)[literalIndex];
        Kernel::Literal* substituted =
          Kernel::SubstHelper::apply(literal, info->substitutionForBanksSub[parentIndex]);
        std::vector<unsigned> position;
        Kernel::Literal* rewrittenTarget = nullptr;
        if (!certificateRewriteLiteralAtMegalodonPosition(
              substituted,
              info->demodulationRedex,
              info->demodulationReplacement,
              position,
              rewrittenTarget)) {
          continue;
        }
        rewrite.hasTargetLocation = true;
        rewrite.targetParentIndex = static_cast<int>(parentIndex);
        rewrite.targetLiteralIndex = static_cast<int>(literalIndex);
        rewrite.hasPosition = true;
        rewrite.position = MegalodonKernelSyntax::position(certificatePositionSexpr(position));
        if (literalSexprForKernel(substituted, rendered)) {
          rewrite.hasTargetSubstituted = true;
          rewrite.targetSubstituted = MegalodonKernelSyntax::literal(rendered);
        }
        if (literalSexprForKernel(rewrittenTarget, rendered)) {
          rewrite.hasRewrittenTarget = true;
          rewrite.rewrittenTarget = MegalodonKernelSyntax::literal(rendered);
        }
        MegalodonKernelSyntax::appendRewrite(fields, rewrite);
        return;
      }
    }
  };
  auto emitKernelV1 =
    [&](const std::string& kernelRule,
        std::vector<std::string> fields,
        bool includePrimitiveParentSubstitutions = false,
        const MegalodonKernelSyntax::RenderedKernelSubsumptionResolutionPivot* subsumptionPivot = nullptr,
        const std::vector<MegalodonKernelSyntax::RenderedKernelSkolemIntroducedSymbol>* skolemIntroducedSymbols = nullptr,
        const MegalodonKernelSyntax::RenderedKernelSourceFormulaTransform* sourceFormulaTransform = nullptr,
        const MegalodonKernelSyntax::RenderedKernelRectifyRenamings* rectifyRenamings = nullptr,
        const MegalodonKernelSyntax::RenderedKernelCnfClause* cnfClause = nullptr,
        const MegalodonKernelSyntax::RenderedKernelDefinitionFold* definitionFold = nullptr,
        const MegalodonKernelSyntax::RenderedKernelUrrTrace* urrTrace = nullptr,
        const MegalodonKernelSyntax::RenderedKernelAvatarComponent* avatarComponent = nullptr,
        const MegalodonKernelSyntax::RenderedKernelAvatarDefinition* avatarDefinition = nullptr,
        const MegalodonKernelSyntax::RenderedKernelSplitDependency* splitDependency = nullptr,
        const MegalodonKernelSyntax::RenderedKernelAvatarSplitStep* avatarSplit = nullptr,
        const MegalodonKernelSyntax::RenderedKernelAvatarRefutation* avatarRefutation = nullptr,
        const MegalodonKernelSyntax::RenderedKernelPredicateDefinition* predicateDefinition = nullptr) {
    if (!MegalodonKernelSyntax::isSupportedRule(kernelRule)) {
      INVALID_OPERATION("unsupported Megalodon kernel_v1 rule: " + kernelRule);
    }
    MegalodonKernelSyntax::MegalodonKernelStep step =
      MegalodonKernelSyntax::kernelStep(
        "u" + std::to_string(u->number()),
        kernelRule);
    MegalodonKernelSyntax::addFields(step, fields);
    if (includePrimitiveParentSubstitutions) {
      addKernelPrimitiveParentSubstitutions(step);
    }
    if (subsumptionPivot != nullptr) {
      MegalodonKernelSyntax::setSubsumptionResolutionPivot(step, *subsumptionPivot);
    }
    if (skolemIntroducedSymbols != nullptr) {
      for (const auto& introduced : *skolemIntroducedSymbols) {
        MegalodonKernelSyntax::addSkolemIntroducedSymbol(step, introduced);
      }
    }
    if (sourceFormulaTransform != nullptr) {
      MegalodonKernelSyntax::setSourceFormulaTransform(step, *sourceFormulaTransform);
    }
    if (rectifyRenamings != nullptr) {
      MegalodonKernelSyntax::setRectifyRenamings(step, *rectifyRenamings);
    }
    if (cnfClause != nullptr) {
      MegalodonKernelSyntax::setCnfClause(step, *cnfClause);
    }
    if (definitionFold != nullptr) {
      MegalodonKernelSyntax::setDefinitionFold(step, *definitionFold);
    }
    if (urrTrace != nullptr) {
      MegalodonKernelSyntax::setUrrTrace(step, *urrTrace);
    }
    if (avatarComponent != nullptr) {
      MegalodonKernelSyntax::setAvatarComponent(step, *avatarComponent);
    }
    if (avatarDefinition != nullptr) {
      MegalodonKernelSyntax::setAvatarDefinition(step, *avatarDefinition);
    }
    if (splitDependency != nullptr) {
      MegalodonKernelSyntax::setSplitDependency(step, *splitDependency);
    }
    if (avatarSplit != nullptr) {
      MegalodonKernelSyntax::setAvatarSplit(step, *avatarSplit);
    }
    if (avatarRefutation != nullptr) {
      MegalodonKernelSyntax::setAvatarRefutation(step, *avatarRefutation);
    }
    if (predicateDefinition != nullptr) {
      MegalodonKernelSyntax::setPredicateDefinition(step, *predicateDefinition);
    }
    auto addPrimitiveExpansion = [&](const std::string& primitiveRule) {
      MegalodonKernelSyntax::addPrimitiveExpansion(
        step,
        MegalodonKernelSyntax::primitiveExpansion(
          "u" + std::to_string(u->number()),
          primitiveRule));
    };
    const auto fixedPrimitives =
      MegalodonKernelSyntax::requiredPrimitivesForRule(kernelRule);
    if (fixedPrimitives.size() == 1) {
      addPrimitiveExpansion(fixedPrimitives[0]);
    } else if (kernelRule == "cnf_clause") {
      std::string primitiveStep;
      if (certificateCnfLiteralStepSexpr(u, primitiveStep)) {
        addPrimitiveExpansion("cnf_literal");
      } else if (certificateCnfFormulaClauseStepSexpr(u, primitiveStep)) {
        addPrimitiveExpansion("cnf_formula_clause");
      }
    } else if (kernelRule == "formula_copy") {
      std::string primitiveStep;
      if (certificateFormulaCopyStepSexpr(u, primitiveStep)) {
        addPrimitiveExpansion("formula_copy");
      } else if (certificateFormulaTermCopyStepSexpr(u, primitiveStep)) {
        addPrimitiveExpansion("formula_term_copy");
      }
    } else if (kernelRule == "rectify_formula") {
      addPrimitiveExpansion("rectify_formula");
    } else if (kernelRule == "fool_exhaustiveness") {
      addPrimitiveExpansion("fool_exhaustiveness");
    } else if (kernelRule == "truth_conflict") {
      addPrimitiveExpansion("truth_conflict");
    } else if (kernelRule == "equality_resolution") {
      std::string primitiveStep;
      if (certificateEqualityResolutionStepSexpr(u, info, primitiveStep)) {
        addPrimitiveExpansion(
          primitiveStep.find("(equality_resolution_constraints ") != std::string::npos
            ? "equality_resolution_constraints"
            : "equality_resolution");
      }
    } else if (kernelRule == "equality_factoring") {
      std::string primitiveStep;
      if (certificateEqualityFactoringStepSexpr(u, info, primitiveStep)) {
        addPrimitiveExpansion(
          primitiveStep.find("(equality_factoring_constraints ") != std::string::npos
            ? "equality_factoring_constraints"
            : "equality_factoring");
      }
    }
    setKernelConclusion(step);
    setKernelParents(step);
    fields = MegalodonKernelSyntax::kernelStepFields(step);
    emit("kernel_v1", fields);
  };

  if (u->isClause() && u->inference().rule() == Kernel::InferenceRule::FOOL_AXIOM_ALL_IS_TRUE_OR_FALSE) {
    std::vector<std::string> kernelFields;
    kernelFields.push_back("axiom_kind=all_is_true_or_false");
    std::string clause;
    if (clauseSexprForKernel(u->asClause(), clause)) {
      kernelFields.push_back("result_clause=" + clause);
    }
    kernelFields.push_back("literal_count=" + std::to_string(u->asClause()->length()));
    for (unsigned index = 0; index < u->asClause()->length(); ++index) {
      std::string literal;
      if (literalSexprForKernel((*u->asClause())[index], literal)) {
        kernelFields.push_back("literal_" + std::to_string(index) + "=" + literal);
      }
    }
    emitKernelV1("fool_exhaustiveness", kernelFields);
  }

  if (u->isClause()
    && u->inference().rule() == Kernel::InferenceRule::AVATAR_COMPONENT
    && u->asClause()->splits()
    && !u->asClause()->splits()->isEmpty()) {
    std::vector<std::string> kernelFields;
    MegalodonKernelSyntax::RenderedKernelAvatarComponent avatarComponent;
    std::string clause;
    if (clauseSexprForKernel(u->asClause(), clause)) {
      avatarComponent.hasResultClause = true;
      avatarComponent.resultClause = MegalodonKernelSyntax::clause(clause);
    }
    avatarComponent.literalCount = u->asClause()->length();
    for (unsigned index = 0; index < u->asClause()->length(); ++index) {
      std::string literal;
      if (literalSexprForKernel((*u->asClause())[index], literal)) {
        avatarComponent.literals.push_back(MegalodonKernelSyntax::literal(literal));
      }
    }
    unsigned splitIndex = 0;
    for (unsigned split : iterTraits(u->asClause()->splits()->iter())) {
      SATLiteral splitLiteral = Splitter::getLiteralFromName(split);
      _avatarComponentBySatVar[splitLiteral.var()] = u->asClause();
      MegalodonKernelSyntax::RenderedKernelAvatarSplit renderedSplit;
      renderedSplit.index = splitIndex;
      renderedSplit.level = split;
      renderedSplit.variable = splitLiteral.var();
      renderedSplit.positive = splitLiteral.positive();
      avatarComponent.splits.push_back(renderedSplit);
      ++splitIndex;
    }
    avatarComponent.splitCount = splitIndex;
    emitKernelV1(
      "avatar_component",
      kernelFields,
      false,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      &avatarComponent);
  }

  auto renderFormulaForExtra = [&](Kernel::Formula* formula, std::string& text) {
    bool usesEquality = _usesEquality;
    std::set<std::string> equalitySorts = _equalitySorts;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySorts.clear();
    _renderingReplayExtra = true;
    bool ok = formulaToMegalodon(formula, text);
    _usesEquality = usesEquality;
    _equalitySorts = equalitySorts;
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
    std::set<std::string> equalitySorts = _equalitySorts;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySorts.clear();
    _renderingReplayExtra = true;
    std::map<unsigned, Kernel::TermList> substitutionMap;
    for (auto [variable, term] : iterTraits(substitution.items())) {
      substitutionMap[variable] = term;
    }
    bool ok = formulaToMegalodon(formula, substitutionMap, text);
    _usesEquality = usesEquality;
    _equalitySorts = equalitySorts;
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
    std::set<std::string> equalitySorts = _equalitySorts;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySorts.clear();
    _renderingReplayExtra = true;
    bool ok = termToMegalodon(term, text);
    _usesEquality = usesEquality;
    _equalitySorts = equalitySorts;
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
    std::set<std::string> equalitySorts = _equalitySorts;
    bool usesConjunction = _usesConjunction;
    bool usesFalse = _usesFalse;
    bool usesDisjunction = _usesDisjunction;
    bool usesSetExists = _usesSetExists;
    bool usesTrue = _usesTrue;
    bool usesPropEquality = _usesPropEquality;
    bool renderingReplayExtra = _renderingReplayExtra;
    _usesEquality = false;
    _equalitySorts.clear();
    _renderingReplayExtra = true;
    bool ok = skeletonClauseToMegalodon(clause, text);
    _usesEquality = usesEquality;
    _equalitySorts = equalitySorts;
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
  auto collectClauseVariableSorts = [&](Kernel::Clause* clause) {
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
    std::vector<std::string> fields;
    fields.reserve(rendered.size());
    for (const auto& item : rendered) {
      fields.push_back(item.second);
    }
    return fields;
  };
  auto addClauseVariableSortFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Clause* clause) {
    std::vector<std::string> rendered = collectClauseVariableSorts(clause);
    fields.push_back(prefix + "_variable_sort_count=" + std::to_string(rendered.size()));
    for (std::size_t i = 0; i < rendered.size(); ++i) {
      fields.push_back(prefix + "_variable_sort_" + std::to_string(i) + "=" + rendered[i]);
    }
  };
  auto collectClauseDbIndexSorts = [&](Kernel::Clause* clause) {
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
    std::vector<std::string> fields;
    fields.reserve(rendered.size());
    for (const auto& entry : rendered) {
      fields.push_back(entry.second);
    }
    return fields;
  };
  auto addClauseDbIndexSortFields = [&](std::vector<std::string>& fields, const std::string& prefix, Kernel::Clause* clause) {
    std::vector<std::string> rendered = collectClauseDbIndexSorts(clause);
    fields.push_back(prefix + "_db_sort_count=" + std::to_string(rendered.size()));
    for (std::size_t i = 0; i < rendered.size(); ++i) {
      fields.push_back(prefix + "_db_sort_" + std::to_string(i) + "=" + rendered[i]);
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
        MegalodonKernelSyntax::RenderedKernelAvatarDefinition avatarDefinition;
        avatarDefinition.componentSplit.level = componentLevel;
        avatarDefinition.componentSplit.variable = componentLiteral.var();
        avatarDefinition.componentSplit.positive = componentLiteral.positive();
        std::vector<std::string> fields;
        fields.push_back("component_split_level=" + std::to_string(componentLevel));
        fields.push_back("component_split_var=" + std::to_string(componentLiteral.var()));
        fields.push_back(std::string("component_split_positive=") + (componentLiteral.positive() ? "1" : "0"));
        std::string componentText;
        if (renderClauseForExtra(splitExtra->component, componentText)) {
          fields.push_back("component_clause=" + componentText);
          avatarDefinition.hasComponentClause = true;
          avatarDefinition.componentClause = componentText;
        }
        std::string componentClause;
        if (clauseSexprForKernel(splitExtra->component, componentClause)) {
          fields.push_back("component_clause_sexpr=" + componentClause);
          avatarDefinition.hasComponentClauseSexpr = true;
          avatarDefinition.componentClauseSexpr = MegalodonKernelSyntax::clause(componentClause);
        }
        avatarDefinition.componentClauseVariableSorts = collectClauseVariableSorts(splitExtra->component);
        avatarDefinition.componentClauseDbSorts = collectClauseDbIndexSorts(splitExtra->component);
        addClauseVariableSortFields(fields, "component_clause", splitExtra->component);
        addClauseDbIndexSortFields(fields, "component_clause", splitExtra->component);
        if (!componentClause.empty()
          && _certificateNativeStepIds.insert(u->number()).second) {
          std::ostringstream native;
          native << "(avatar_definition " << sexprQuote("u" + std::to_string(u->number()))
                 << " (split " << componentLiteral.var() << ' '
                 << (componentLiteral.positive() ? "true" : "false") << ")"
                 << " (result " << componentClause << "))";
          _certificateNativeSteps.push_back(native.str());
        }
        {
          std::vector<std::string> kernelFields;
          if (!componentClause.empty()) {
            avatarDefinition.hasResultClause = true;
            avatarDefinition.resultClause = MegalodonKernelSyntax::clause(componentClause);
          }
          emitKernelV1(
            "avatar_definition",
            kernelFields,
            false,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            &avatarDefinition);
        }
        emit("avatar_definition", fields);
      }
    }
  }

  if (u->isClause() && u->asClause()->splits() && !u->asClause()->splits()->isEmpty()) {
    std::vector<std::string> fields;
    std::vector<std::string> nativeDependencies;
    MegalodonKernelSyntax::RenderedKernelSplitDependency splitDependency;
    unsigned dependencyIndex = 0;
    for (unsigned split : iterTraits(u->asClause()->splits()->iter())) {
      SATLiteral splitLiteral = Splitter::getLiteralFromName(split);
      MegalodonKernelSyntax::RenderedKernelSplitDependencyItem dependency;
      dependency.index = dependencyIndex;
      dependency.split.level = split;
      dependency.split.variable = splitLiteral.var();
      dependency.split.positive = splitLiteral.positive();
      std::string prefix = "dependency_" + std::to_string(dependencyIndex);
      fields.push_back(prefix + "_split_level=" + std::to_string(split));
      fields.push_back(prefix + "_split_var=" + std::to_string(splitLiteral.var()));
      fields.push_back(prefix + "_split_positive=" + (splitLiteral.positive() ? "1" : "0"));
      auto component = _avatarComponentBySatVar.find(splitLiteral.var());
      if (component != _avatarComponentBySatVar.end() && component->second != nullptr) {
        std::string componentText;
        if (renderClauseForExtra(component->second, componentText)) {
          fields.push_back(prefix + "_component_clause=" + componentText);
          dependency.hasComponentClause = true;
          dependency.componentClause = componentText;
        }
        std::string componentClause;
        if (clauseSexprForKernel(component->second, componentClause)) {
          fields.push_back(prefix + "_component_clause_sexpr=" + componentClause);
          dependency.hasComponentClauseSexpr = true;
          dependency.componentClauseSexpr = MegalodonKernelSyntax::clause(componentClause);
          std::ostringstream nativeDependency;
          nativeDependency << "(dependency " << splitLiteral.var() << ' '
                           << (splitLiteral.positive() ? "true" : "false")
                           << " (component " << componentClause << "))";
          nativeDependencies.push_back(nativeDependency.str());
        }
        dependency.componentClauseVariableSorts = collectClauseVariableSorts(component->second);
        dependency.componentClauseDbSorts = collectClauseDbIndexSorts(component->second);
        addClauseVariableSortFields(fields, prefix + "_component_clause", component->second);
        addClauseDbIndexSortFields(fields, prefix + "_component_clause", component->second);
        std::vector<std::string> extraFields;
        addLambdaSubtermFields(extraFields, prefix + "_component_clause", component->second, nullptr);
        if (!dependency.componentClauseDbSorts.empty()) {
          extraFields.push_back(prefix + "_scoped_split_certificate=component_contains_de_bruijn");
          extraFields.push_back(
            prefix + "_scoped_split_certificate_db_sort_count="
            + std::to_string(dependency.componentClauseDbSorts.size()));
          for (std::size_t sortIndex = 0; sortIndex < dependency.componentClauseDbSorts.size(); ++sortIndex) {
            extraFields.push_back(
              prefix + "_scoped_split_certificate_db_sort_" + std::to_string(sortIndex)
              + "=" + dependency.componentClauseDbSorts[sortIndex]);
          }
        }
        for (const std::string& extraField : extraFields) {
          fields.push_back(extraField);
          dependency.componentClauseExtraFields.push_back(
            MegalodonKernelSyntax::migrationField(extraField));
        }
      }
      splitDependency.dependencies.push_back(dependency);
      ++dependencyIndex;
    }
    fields.push_back("dependency_count=" + std::to_string(dependencyIndex));
    {
      std::vector<std::string> kernelFields;
      std::string resultClause;
      if (clauseSexprForKernel(u->asClause(), resultClause)) {
        splitDependency.hasResultClause = true;
        splitDependency.resultClause = MegalodonKernelSyntax::clause(resultClause);
        std::ostringstream native;
        native << "(split_dependency "
               << sexprQuote("u" + std::to_string(u->number()) + "_split_dependency")
               << " (owner " << sexprQuote("u" + std::to_string(u->number())) << ")"
               << " (dependencies";
        for (const std::string& dependency : nativeDependencies) {
          native << ' ' << dependency;
        }
        native << ") (result " << resultClause << "))";
        _certificateNativeSteps.push_back(native.str());
      }
      emitKernelV1(
        "split_dependency",
        kernelFields,
        false,
        nullptr,
        nullptr,
        nullptr,
        nullptr,
        nullptr,
        nullptr,
        nullptr,
        nullptr,
        nullptr,
        &splitDependency);
    }
    emit("split_dependency", fields);
  }

  if (u->inference().rule() == Kernel::InferenceRule::AVATAR_SPLIT_CLAUSE) {
    UnitIterator parents = u->getParents();
    if (parents.hasNext()) {
      Kernel::Unit* mainParentUnit = parents.next();
      if (mainParentUnit->isClause()) {
        Kernel::Clause* mainParent = mainParentUnit->asClause();
        std::vector<std::string> fields;
        MegalodonKernelSyntax::RenderedKernelAvatarSplitStep avatarSplit;
        avatarSplit.sourceUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(mainParentUnit->number()));
        avatarSplit.vampireRule = Kernel::ruleName(u->inference().rule());
        fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
        std::string sourceText;
        if (renderClauseForExtra(mainParent, sourceText)) {
          fields.push_back("source=" + sourceText);
          avatarSplit.hasSourceText = true;
          avatarSplit.sourceText = sourceText;
        }
        std::string targetText;
        if (renderUnitForExtra(u, targetText)) {
          fields.push_back("target=" + targetText);
          avatarSplit.hasTargetText = true;
          avatarSplit.targetText = targetText;
        }

        std::set<unsigned> previousSplitVars;
        if (!mainParent->noSplits()) {
          unsigned previousIndex = 0;
          for (unsigned split : iterTraits(mainParent->splits()->iter())) {
            SATLiteral splitLiteral = Splitter::getLiteralFromName(split);
            previousSplitVars.insert(splitLiteral.var());
            MegalodonKernelSyntax::RenderedKernelAvatarSplit previousSplit;
            previousSplit.index = previousIndex;
            previousSplit.level = split;
            previousSplit.variable = splitLiteral.var();
            previousSplit.positive = splitLiteral.positive();
            avatarSplit.previousSplits.push_back(previousSplit);
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
            MegalodonKernelSyntax::RenderedKernelAvatarSatLiteral renderedLiteral;
            renderedLiteral.index = satIndex;
            renderedLiteral.variable = literal.var();
            renderedLiteral.positive = literal.positive();
            avatarSplit.satLiterals.push_back(renderedLiteral);
            fields.push_back("sat_literal_" + std::to_string(satIndex) + "_var=" + std::to_string(literal.var()));
            fields.push_back("sat_literal_" + std::to_string(satIndex) + "_positive=" + (literal.positive() ? "1" : "0"));
            ++satIndex;
          }
          fields.push_back("sat_literal_count=" + std::to_string(satIndex));
        }

        std::map<unsigned, Kernel::Clause*> components;
        std::map<unsigned, std::pair<unsigned, Kernel::Clause*>> splitToParentMap;
        unsigned parentIndex = 1;
        unsigned componentParentRefIndex = 0;
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
          MegalodonKernelSyntax::RenderedKernelAvatarComponentParent componentParent;
          componentParent.parentIndex = parentIndex - 1;
          componentParent.refIndex = componentParentRefIndex;
          componentParent.unit = MegalodonKernelSyntax::unitRef(std::to_string(splitParent->number()));
          componentParent.split.level = componentLevel;
          componentParent.split.variable = componentLiteral.var();
          componentParent.split.positive = componentLiteral.positive();
          std::string prefix = "component_parent_" + std::to_string(parentIndex - 1);
          fields.push_back(prefix + "_unit=" + std::to_string(splitParent->number()));
          fields.push_back(prefix + "_split_level=" + std::to_string(componentLevel));
          fields.push_back(prefix + "_split_var=" + std::to_string(componentLiteral.var()));
          fields.push_back(prefix + "_split_positive=" + (componentLiteral.positive() ? "1" : "0"));
          std::string componentText;
          if (renderClauseForExtra(splitExtra->component, componentText)) {
            fields.push_back(prefix + "_clause=" + componentText);
            componentParent.hasClause = true;
            componentParent.clause = componentText;
          }
          std::string normalizedPrefix =
            "component_parent_ref_" + std::to_string(componentParentRefIndex);
          fields.push_back(normalizedPrefix + "_unit=u" + std::to_string(splitParent->number()));
          fields.push_back(normalizedPrefix + "_split_level=" + std::to_string(componentLevel));
          fields.push_back(normalizedPrefix + "_split_var=" + std::to_string(componentLiteral.var()));
          fields.push_back(normalizedPrefix + "_split_positive=" + (componentLiteral.positive() ? "1" : "0"));
          std::string componentClause;
          if (clauseSexprForKernel(splitExtra->component, componentClause)) {
            fields.push_back(normalizedPrefix + "_clause=" + componentClause);
            componentParent.hasClauseSexpr = true;
            componentParent.clauseSexpr = MegalodonKernelSyntax::clause(componentClause);
          }
          avatarSplit.componentParents.push_back(componentParent);
          ++componentParentRefIndex;
          ++parentIndex;
        }
        fields.push_back("component_parent_count=" + std::to_string(parentIndex > 1 ? parentIndex - 2 : 0));
        avatarSplit.componentParentCount = parentIndex > 1 ? parentIndex - 2 : 0;
        fields.push_back("component_parent_ref_count=" + std::to_string(componentParentRefIndex));

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
          MegalodonKernelSyntax::RenderedKernelAvatarLiteralClass literalClass;
          literalClass.index = classIndex;
          literalClass.literalCount = klass.size();
          std::string classPrefix = "literal_class_" + std::to_string(classIndex);
          fields.push_back(classPrefix + "_literal_count=" + std::to_string(klass.size()));
          for (unsigned literalIndex = 0; literalIndex < klass.size(); ++literalIndex) {
            std::string literalText;
            if (skeletonLiteralToMegalodon(klass[literalIndex], literalText)) {
              fields.push_back(classPrefix + "_literal_" + std::to_string(literalIndex) + "=" + literalText);
              literalClass.literals.push_back(literalText);
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
              literalClass.hasMatchedSplitLevel = true;
              literalClass.matchedSplitLevel = splitLevel;
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
              literalClass.hasMatchedSplitLevel = true;
              literalClass.matchedSplitLevel = splitLevel;
              break;
            }
          }
          avatarSplit.literalClasses.push_back(literalClass);
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
          MegalodonKernelSyntax::RenderedKernelAvatarParentVarBinding binding;
          binding.index = bindingIndex;
          binding.parentVar = variableName(var);
          std::string prefix = "parent_var_binding_" + std::to_string(bindingIndex);
          fields.push_back(prefix + "_parent_var=" + variableName(var));
          if (substituted.isVar()) {
            fields.push_back(prefix + "_component_var=" + variableName(substituted.var()));
            binding.hasComponentVar = true;
            binding.componentVar = variableName(substituted.var());
          }
          if (splitVar != varToSplitMap.end()) {
            fields.push_back(prefix + "_split_var=" + std::to_string(splitVar->second));
            binding.hasSplitVar = true;
            binding.splitVar = splitVar->second;
          }
          avatarSplit.parentVarBindings.push_back(binding);
          ++bindingIndex;
        }
        fields.push_back("parent_var_binding_count=" + std::to_string(bindingIndex));
        {
          std::vector<std::string> kernelFields;
          std::string sourceClause;
          if (clauseSexprForKernel(mainParent, sourceClause)) {
            avatarSplit.hasSourceClause = true;
            avatarSplit.sourceClause = MegalodonKernelSyntax::clause(sourceClause);
          }
          if (u->isClause()) {
            std::string resultClause;
            if (clauseSexprForKernel(u->asClause(), resultClause)) {
              avatarSplit.hasResultClause = true;
              avatarSplit.resultClause = MegalodonKernelSyntax::clause(resultClause);
            }
          } else if (!targetText.empty()) {
            avatarSplit.hasResultFormula = true;
            avatarSplit.resultFormula = MegalodonKernelSyntax::formula(targetText);
          }
          emitKernelV1(
            "avatar_split",
            kernelFields,
            false,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            &avatarSplit);
        }
        emit("avatar_split", fields);
      }
    }
  }

  if (u->isClause()
    && (
      u->inference().rule() == Kernel::InferenceRule::AVATAR_REFUTATION
      || u->inference().rule() == Kernel::InferenceRule::AVATAR_REFUTATION_SMT
    )
    && u->asClause()->length() == 0) {
    std::vector<std::string> kernelFields;
    MegalodonKernelSyntax::RenderedKernelAvatarRefutation avatarRefutation;
    avatarRefutation.hasResultClause = true;
    avatarRefutation.resultClause = MegalodonKernelSyntax::clause("(clause)");
    if (SAT::SATClause* refutation = u->inference().satPremise()) {
      std::string refutationClause;
      if (satClauseSexprForKernel(refutation, refutationClause)) {
        avatarRefutation.hasSatRefutationClause = true;
        avatarRefutation.satRefutationClause = MegalodonKernelSyntax::clause(refutationClause);
      }
      unsigned satInputIndex = 0;
      SAT::SATInference::visitFOConversions(refutation, [&](SAT::SATClause* clause) {
        MegalodonKernelSyntax::RenderedKernelSatInput input;
        input.index = satInputIndex;
        std::string rendered;
        if (satClauseSexprForKernel(clause, rendered)) {
          input.hasClause = true;
          input.clause = MegalodonKernelSyntax::clause(rendered);
        }
        Kernel::Unit* origin = clause->inference()->foConversion()->getOrigin();
        if (origin != nullptr) {
          input.hasOriginUnit = true;
          input.originUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(origin->number()));
        }
        avatarRefutation.inputs.push_back(input);
        ++satInputIndex;
      });
      populateKernelSatProofSteps(avatarRefutation, refutation);
    } else {
      unsigned satInputIndex = 0;
      for (Kernel::Unit* parent : iterTraits(u->getParents())) {
        const auto* parentExtra = env.proofExtra.find(parent);
        if (parentExtra == nullptr) {
          continue;
        }
        const auto* satExtra = static_cast<const Indexing::SATClauseExtra*>(parentExtra);
        if (satExtra->clause == nullptr) {
          continue;
        }
        MegalodonKernelSyntax::RenderedKernelSatInput input;
        input.index = satInputIndex;
        std::string rendered;
        if (satClauseSexprForKernel(satExtra->clause, rendered)) {
          input.hasClause = true;
          input.clause = MegalodonKernelSyntax::clause(rendered);
        }
        input.hasOriginUnit = true;
        input.originUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(parent->number()));
        avatarRefutation.inputs.push_back(input);
        ++satInputIndex;
      }
    }
    emitKernelV1(
      "avatar_refutation",
      kernelFields,
      false,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      nullptr,
      &avatarRefutation);
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

        std::string sourceFormula;
        std::string resultFormula;
        if (certificateFormulaTermSexpr(source, sourceFormula)
          && certificateFormulaTermSexpr(target, resultFormula)
          && sourceFormula == resultFormula) {
          std::vector<std::string> kernelFields;
          MegalodonKernelSyntax::RenderedKernelSourceFormulaTransform transform;
          transform.sourceUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(parent->number()));
          transform.sourceFormula = MegalodonKernelSyntax::formula(sourceFormula);
          transform.resultFormula = MegalodonKernelSyntax::formula(resultFormula);
          transform.hasCopyKind = true;
          transform.copyKind = "formula_term_identity";
          emitKernelV1(
            "formula_copy",
            kernelFields,
            false,
            nullptr,
            nullptr,
            &transform);
        }

        unsigned pairCount = 0;
        std::size_t totalPairText = 0;
        const unsigned pairLimit = 32;
        const std::size_t textLimit = 120000;
        std::vector<std::tuple<std::string, std::string, std::string, std::string>> transformationPairs;
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

        auto emitPair = [&](const std::string& leftText, const std::string& rightText, const std::string& path, const std::string& kind) {
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
          fields.push_back("pair_" + std::to_string(index) + "_kind=" + kind);
          transformationPairs.push_back(std::make_tuple(leftText, rightText, path, kind));
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
        auto connectiveKind = [](Kernel::Connective connective) {
          switch (connective) {
            case Kernel::IMP: return std::string("imp");
            case Kernel::FORALL: return std::string("forall");
            case Kernel::EXISTS: return std::string("exists");
            case Kernel::AND: return std::string("and");
            case Kernel::OR: return std::string("or");
            case Kernel::NOT: return std::string("not");
            case Kernel::IFF: return std::string("iff");
            case Kernel::XOR: return std::string("xor");
            default: return std::string("other");
          }
        };
        auto pairKind = [&](Kernel::Formula* left, Kernel::Formula* right) {
          if (left == nullptr || right == nullptr) {
            return std::string("unknown");
          }
          if (left->connective() == right->connective()) {
            return std::string("context_") + connectiveKind(left->connective());
          }
          std::vector<Kernel::Formula*> rightArgs;
          if (right->connective() == Kernel::AND || right->connective() == Kernel::OR) {
            rightArgs = formulaArgs(right);
          }
          if (left->connective() == Kernel::IMP && right->connective() == Kernel::OR && rightArgs.size() == 2) {
            return std::string("imp_to_or");
          }
          Kernel::Formula* negated = negatedBody(left);
          if (negated == nullptr) {
            return std::string("unknown");
          }
          if (negated->connective() == Kernel::IMP && right->connective() == Kernel::AND && rightArgs.size() == 2) {
            return std::string("not_imp_to_and");
          }
          if (negated->connective() == Kernel::FORALL && right->connective() == Kernel::EXISTS) {
            return std::string("not_forall_to_exists");
          }
          if (negated->connective() == Kernel::AND && right->connective() == Kernel::OR) {
            return std::string("not_and_to_or");
          }
          if (negated->connective() == Kernel::OR && right->connective() == Kernel::AND) {
            return std::string("not_or_to_and");
          }
          return std::string("unknown");
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
            emitPair(leftText, rightText, path, pairKind(left, right));
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
            if (negated->connective() == Kernel::FORALL && right->connective() == Kernel::EXISTS) {
              collectPairs(negatedFormula(negated->qarg()), right->qarg(), depth + 1, path + ".ennf_neg_forall_body");
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
                  emitPair(leftText, rightText, path + ".and[1]", "context_and_slice");
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
                emitPair(leftText, rightText, path + ".or[0]", "context_or_slice");
              }
              collectSlicePairs(leftArgs, leftBegin, leftEnd - 1, rightArgs, rightBegin, rightEnd - 1, connective, depth + 1, path + ".or[0]");
              collectPairs(leftArgs[leftEnd - 1], rightArgs[rightEnd - 1], depth + 1, path + ".or[1]");
            }
          };
        collectPairs(source, target, 0, "root");
        if (!sourceFormula.empty()
          && !resultFormula.empty()
          && sourceFormula != resultFormula
          && !transformationPairs.empty()) {
          std::vector<std::string> kernelFields;
          MegalodonKernelSyntax::RenderedKernelSourceFormulaTransform transform;
          transform.sourceUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(parent->number()));
          transform.sourceFormula = MegalodonKernelSyntax::formula(sourceFormula);
          transform.resultFormula = MegalodonKernelSyntax::formula(resultFormula);
          transform.hasNormalFormRule = true;
          transform.normalFormRule = std::string(Kernel::ruleName(u->inference().rule()));
          for (std::size_t index = 0; index < transformationPairs.size(); ++index) {
            const auto& [leftText, rightText, path, kind] = transformationPairs[index];
            MegalodonKernelSyntax::RenderedKernelTransformationPair pair;
            pair.index = index;
            pair.source = MegalodonKernelSyntax::formula(leftText);
            pair.target = MegalodonKernelSyntax::formula(rightText);
            pair.hasPath = true;
            pair.path = path;
            pair.hasKind = true;
            pair.kind = kind;
            transform.transformationPairs.push_back(pair);
          }
          emitKernelV1(
            "formula_normalize",
            kernelFields,
            false,
            nullptr,
            nullptr,
            &transform);
        }
        emit("normal_form", fields);
      }
    }
  }

  if (isNormalFormRule(u->inference().rule()) && u->isClause()) {
    UnitIterator parentIterator = u->getParents();
    if (parentIterator.hasNext()) {
      Kernel::Unit* parent = parentIterator.next();
      if (parent->isClause()) {
        std::vector<std::string> fields;
        fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
        fields.push_back("parent_unit=" + std::to_string(parent->number()));

        std::string sourceClause;
        if (certificateClauseJson(parent->asClause(), sourceClause)) {
          fields.push_back("source_clause=" + sourceClause);
        } else {
          fields.push_back("source_clause_conversion_failed=1");
        }

        std::string targetClause;
        if (certificateClauseJson(u->asClause(), targetClause)) {
          fields.push_back("target_clause=" + targetClause);
        } else {
          fields.push_back("target_clause_conversion_failed=1");
        }

        std::string sourceProposition;
        if (renderClauseForExtra(parent->asClause(), sourceProposition)) {
          fields.push_back("source_proposition=" + sourceProposition);
        } else {
          fields.push_back("source_proposition_conversion_failed=1");
        }

        std::string targetProposition;
        if (renderClauseForExtra(u->asClause(), targetProposition)) {
          fields.push_back("target_proposition=" + targetProposition);
        } else {
          fields.push_back("target_proposition_conversion_failed=1");
        }

        addClauseVariableSortFields(fields, "source", parent->asClause());
        addClauseVariableSortFields(fields, "target", u->asClause());
        addLambdaSubtermFields(fields, "source", parent->asClause(), nullptr);
        addLambdaSubtermFields(fields, "target", u->asClause(), nullptr);
        emit("normal_form_clause", fields);
      }
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::RECTIFY && !u->isClause()) {
    const auto* genericInfo = InferenceRecorder::instance()->getGenericLastInferenceInformation();
    const auto* rectifyInfo = static_cast<const InferenceRecorder::RectifyInferenceExtra*>(genericInfo);
    if (rectifyInfo != nullptr) {
      std::vector<std::string> kernelFields;
      MegalodonKernelSyntax::RenderedKernelSourceFormulaTransform sourceTransform;
      bool hasSourceTransform = false;
      UnitIterator kernelParentIterator = u->getParents();
      unsigned kernelParentCount = 0;
      if (kernelParentIterator.hasNext()) {
        Kernel::Unit* parent = kernelParentIterator.next();
        const std::string parentUnit = "u" + std::to_string(parent->number());
        ++kernelParentCount;
        if (!parent->isClause()) {
          std::string sourceFormula;
          std::string resultFormula;
          if (certificateFormulaTermSexpr(parent->getFormula(), sourceFormula)) {
            if (certificateFormulaTermSexpr(u->getFormula(), resultFormula)) {
              sourceTransform.sourceUnit = MegalodonKernelSyntax::unitRef(parentUnit);
              sourceTransform.sourceFormula = MegalodonKernelSyntax::formula(sourceFormula);
              sourceTransform.resultFormula = MegalodonKernelSyntax::formula(resultFormula);
              sourceTransform.proofParentCount = 1;
              hasSourceTransform = true;
            } else {
              kernelFields.push_back("source_unit=" + parentUnit);
              kernelFields.push_back("parent_0_unit=" + parentUnit);
              kernelFields.push_back("source_formula=" + sourceFormula);
              kernelFields.push_back("parent_0_formula=" + sourceFormula);
            }
          } else {
            kernelFields.push_back("source_unit=" + parentUnit);
            kernelFields.push_back("parent_0_unit=" + parentUnit);
          }
        } else {
          kernelFields.push_back("source_unit=" + parentUnit);
          kernelFields.push_back("parent_0_unit=" + parentUnit);
        }
      }
      if (!hasSourceTransform) {
        kernelFields.push_back("proof_parent_count=" + std::to_string(kernelParentCount));
        std::string resultFormula;
        if (certificateFormulaTermSexpr(u->getFormula(), resultFormula)) {
          kernelFields.push_back("result_formula=" + resultFormula);
        }
      }
      MegalodonKernelSyntax::RenderedKernelRectifyRenamings rectifyRenamings;
      rectifyRenamings.reportedCount = rectifyInfo->renamings.size();
      std::map<std::string, std::string> rectifyVariableMap;
      auto addRectifyVariableMapEntry =
        [&](unsigned sourceVar, unsigned targetVar, Kernel::TermList sourceSort, Kernel::TermList targetSort) {
          std::string sourceType;
          std::string targetType;
          if (!sortToMegalodon(sourceSort, sourceType)
              || !sortToMegalodon(targetSort, targetType)
              || sourceType != targetType) {
            return;
          }
          const std::string sourceName = variableName(sourceVar);
          const std::string targetName = variableName(targetVar);
          if (sourceName == targetName) {
            return;
          }
          auto it = rectifyVariableMap.find(sourceName);
          if (it == rectifyVariableMap.end()) {
            rectifyVariableMap[sourceName] = targetName;
          } else if (it->second != targetName) {
            rectifyVariableMap[sourceName] = "";
          }
        };
      std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned)> collectRectifyVariableMap;
      collectRectifyVariableMap =
        [&](Kernel::Formula* source, Kernel::Formula* target, unsigned depth) {
          if (source == nullptr || target == nullptr || depth > 64) {
            return;
          }
          if (source->connective() != target->connective()) {
            return;
          }
          switch (source->connective()) {
            case Kernel::FORALL:
            case Kernel::EXISTS: {
              Kernel::VSList::Iterator sourceVars(source->vars());
              Kernel::VSList::Iterator targetVars(target->vars());
              while (sourceVars.hasNext() && targetVars.hasNext()) {
                auto sourceVar = sourceVars.next();
                auto targetVar = targetVars.next();
                addRectifyVariableMapEntry(sourceVar.first, targetVar.first, sourceVar.second, targetVar.second);
              }
              if (sourceVars.hasNext() || targetVars.hasNext()) {
                return;
              }
              collectRectifyVariableMap(source->qarg(), target->qarg(), depth + 1);
              return;
            }
            case Kernel::AND:
            case Kernel::OR: {
              Kernel::FormulaList::Iterator sourceArgs(source->args());
              Kernel::FormulaList::Iterator targetArgs(target->args());
              while (sourceArgs.hasNext() && targetArgs.hasNext()) {
                collectRectifyVariableMap(sourceArgs.next(), targetArgs.next(), depth + 1);
              }
              return;
            }
            case Kernel::IMP:
            case Kernel::IFF:
            case Kernel::XOR:
              collectRectifyVariableMap(source->left(), target->left(), depth + 1);
              collectRectifyVariableMap(source->right(), target->right(), depth + 1);
              return;
            case Kernel::NOT:
              collectRectifyVariableMap(source->uarg(), target->uarg(), depth + 1);
              return;
            default:
              return;
          }
        };
      unsigned kernelRenamingIndex = 0;
      const unsigned kernelRenamingLimit = 64;
      for (auto [newFormula, formulaAndSubst] : rectifyInfo->renamings) {
        if (kernelRenamingIndex >= kernelRenamingLimit) {
          rectifyRenamings.truncated = true;
          break;
        }
        auto [formula, substitution] = formulaAndSubst;
        collectRectifyVariableMap(formula, newFormula, 0);
        MegalodonKernelSyntax::RenderedKernelRectifyRenaming renaming;
        renaming.index = kernelRenamingIndex;
        std::string renamingSource;
        if (certificateFormulaTermSexpr(formula, renamingSource)) {
          renaming.hasSource = true;
          renaming.source = MegalodonKernelSyntax::formula(renamingSource);
        }
        std::string renamingTarget;
        if (certificateFormulaTermSexpr(newFormula, renamingTarget)) {
          renaming.hasTarget = true;
          renaming.target = MegalodonKernelSyntax::formula(renamingTarget);
        }
        std::string renamingSubstitution;
        if (substitutionSexprForKernel(substitution, renamingSubstitution)) {
          renaming.hasSubstitution = true;
          renaming.substitution = MegalodonKernelSyntax::substitution(renamingSubstitution);
        }
        rectifyRenamings.renamings.push_back(renaming);
        ++kernelRenamingIndex;
      }
      std::vector<std::string> variableMapItems;
      for (const auto& entry : rectifyVariableMap) {
        if (entry.second.empty()) {
          variableMapItems.clear();
          break;
        }
        variableMapItems.push_back(
          "(" + sexprQuote(entry.first) + " (TMH " + sexprQuote(entry.second) + "))");
      }
      if (!variableMapItems.empty()) {
        std::ostringstream variableMap;
        variableMap << "(subst";
        for (const std::string& item : variableMapItems) {
          variableMap << " " << item;
        }
        variableMap << ")";
        rectifyRenamings.hasVariableMap = true;
        rectifyRenamings.variableMap = MegalodonKernelSyntax::substitution(variableMap.str());
      }
      emitKernelV1(
        "rectify_formula",
        kernelFields,
        false,
        nullptr,
        nullptr,
        hasSourceTransform ? &sourceTransform : nullptr,
        &rectifyRenamings);

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
        std::vector<std::tuple<std::string, std::string, std::string>> foolPairs;
        std::function<void(Kernel::Formula*, Kernel::Formula*, unsigned, std::string)> collectPairs =
          [&](Kernel::Formula* left, Kernel::Formula* right, unsigned depth, std::string path) {
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
                fields.push_back("pair_" + std::to_string(index) + "_path=" + path);
                foolPairs.push_back(std::make_tuple(leftText, rightText, path));
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
                unsigned index = 0;
                while (leftIt.hasNext() && rightIt.hasNext()) {
                  collectPairs(leftIt.next(), rightIt.next(), depth + 1, path + ".arg[" + std::to_string(index) + "]");
                  ++index;
                }
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
        collectPairs(source, target, 0, "root");
        std::string sourceFormula;
        std::string resultFormula;
        std::string foolBoolStep;
        const bool emitsFoolBool = certificateFoolBoolStepSexpr(u, foolBoolStep);
        if (!emitsFoolBool
          && certificateFormulaTermSexpr(source, sourceFormula)
          && certificateFormulaTermSexpr(target, resultFormula)
          && sourceFormula != resultFormula
          && !foolPairs.empty()) {
          std::vector<std::string> kernelFields;
          MegalodonKernelSyntax::RenderedKernelSourceFormulaTransform transform;
          transform.sourceUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(parent->number()));
          transform.sourceFormula = MegalodonKernelSyntax::formula(sourceFormula);
          transform.resultFormula = MegalodonKernelSyntax::formula(resultFormula);
          for (std::size_t index = 0; index < foolPairs.size(); ++index) {
            const auto& [leftText, rightText, path] = foolPairs[index];
            MegalodonKernelSyntax::RenderedKernelTransformationPair pair;
            pair.index = index;
            pair.source = MegalodonKernelSyntax::formula(leftText);
            pair.target = MegalodonKernelSyntax::formula(rightText);
            pair.hasPath = true;
            pair.path = path;
            transform.transformationPairs.push_back(pair);
          }
          emitKernelV1(
            "fool_formula",
            kernelFields,
            false,
            nullptr,
            nullptr,
            &transform);
        }
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
        if (renderTermForExtra(foldingExtra->steps[stepIndex].from, lhs)) {
          fields.push_back(prefix + "_lhs=" + lhs);
        }
        std::string rhs;
        if (renderTermForExtra(foldingExtra->steps[stepIndex].to, rhs)) {
          fields.push_back(prefix + "_rhs=" + rhs);
        }
        fields.push_back(prefix + "_literal=" + std::to_string(foldingExtra->steps[stepIndex].literal));
        std::ostringstream position;
        for (std::size_t positionIndex = 0; positionIndex < foldingExtra->steps[stepIndex].position.size(); ++positionIndex) {
          if (positionIndex) {
            position << ".";
          }
          position << foldingExtra->steps[stepIndex].position[positionIndex];
        }
        fields.push_back(prefix + "_position=" + position.str());
      }
    }
    if (u->inference().rule() == Kernel::InferenceRule::DEFINITION_FOLDING_PRED && !u->isClause()) {
      Kernel::Unit* sourceParent = nullptr;
      std::vector<Kernel::Unit*> definitionParents;
      for (Kernel::Unit* parent : iterTraits(u->getParents())) {
        if (parent->isClause()) {
          continue;
        }
        if (parent->inference().rule() == Kernel::InferenceRule::PREDICATE_DEFINITION) {
          definitionParents.push_back(parent);
        } else if (sourceParent == nullptr) {
          sourceParent = parent;
        }
      }
      if (sourceParent != nullptr && !definitionParents.empty()) {
        std::vector<std::string> kernelFields;
        MegalodonKernelSyntax::RenderedKernelDefinitionFold definitionFold;
        definitionFold.sourceUnit =
          MegalodonKernelSyntax::unitRef("u" + std::to_string(sourceParent->number()));
        std::string sourceFormula;
        if (certificateFormulaTermSexpr(sourceParent->getFormula(), sourceFormula)) {
          definitionFold.hasSourceFormula = true;
          definitionFold.sourceFormula = MegalodonKernelSyntax::formula(sourceFormula);
        }
        std::reverse(definitionParents.begin(), definitionParents.end());
        for (std::size_t definitionIndex = 0; definitionIndex < definitionParents.size(); ++definitionIndex) {
          Kernel::Unit* definitionParent = definitionParents[definitionIndex];
          MegalodonKernelSyntax::RenderedKernelDefinitionParent definition;
          definition.index = definitionIndex;
          definition.unit =
            MegalodonKernelSyntax::unitRef("u" + std::to_string(definitionParent->number()));
          std::string definitionFormula;
          if (certificateFormulaTermSexpr(definitionParent->getFormula(), definitionFormula)) {
            definition.hasFormula = true;
            definition.formula = MegalodonKernelSyntax::formula(definitionFormula);
          }
          std::string symbolName;
          if (certificatePredicateDefinitionSymbol(definitionParent->getFormula(), symbolName)) {
            definition.hasSymbol = true;
            definition.symbol = symbolName;
          }
          definitionFold.definitions.push_back(definition);
        }
        std::string resultFormula;
        if (certificateFormulaTermSexpr(u->getFormula(), resultFormula)) {
          definitionFold.hasResultFormula = true;
          definitionFold.resultFormula = MegalodonKernelSyntax::formula(resultFormula);
        }
        emitKernelV1(
          definitionParents.size() == 1
            ? "predicate_definition_fold"
            : "predicate_definition_fold_chain",
          kernelFields,
          false,
          nullptr,
          nullptr,
          nullptr,
          nullptr,
          nullptr,
          &definitionFold);
      }
    }
    emit("definition_rewrite", fields);
  }

  if (u->inference().rule() == Kernel::InferenceRule::CLAUSIFY && u->isClause()) {
    UnitIterator parentIterator = u->getParents();
    if (parentIterator.hasNext()) {
      Kernel::Unit* parent = parentIterator.next();
      std::vector<std::string> fields;
      {
        std::vector<std::string> kernelFields;
        MegalodonKernelSyntax::RenderedKernelCnfClause cnfClause;
        cnfClause.sourceUnit = MegalodonKernelSyntax::unitRef("u" + std::to_string(parent->number()));
        cnfClause.sourceKind = parent->isClause() ? "clause" : "formula";
        if (parent->isClause()) {
          std::string sourceClause;
          if (clauseSexprForKernel(parent->asClause(), sourceClause)) {
            cnfClause.hasSourceClause = true;
            cnfClause.sourceClause = MegalodonKernelSyntax::clause(sourceClause);
          }
        } else {
          std::string sourceFormula;
          if (certificateFormulaTermSexpr(parent->getFormula(), sourceFormula)) {
            cnfClause.hasSourceFormula = true;
            cnfClause.sourceFormula = MegalodonKernelSyntax::formula(sourceFormula);
          }
        }
        std::string resultClause;
        if (clauseSexprForKernel(u->asClause(), resultClause)) {
          cnfClause.hasResultClause = true;
          cnfClause.resultClause = MegalodonKernelSyntax::clause(resultClause);
        }
        const auto* parentExtra = env.proofExtra.find(parent);
        if (parentExtra != nullptr) {
          const auto* cnfExtra = static_cast<const Inferences::CNFTransformationInferenceExtra*>(parentExtra);
          cnfClause.hasParentClauseCount = true;
          cnfClause.parentClauseCount = cnfExtra->number;
        }
        if (extra != nullptr) {
          const auto* clauseExtra = static_cast<const Inferences::CNFClauseInferenceExtra*>(extra);
          cnfClause.hasClauseParentUnit = true;
          cnfClause.clauseParentUnit =
            MegalodonKernelSyntax::unitRef("u" + std::to_string(clauseExtra->parentNumber));
          cnfClause.hasClauseIndex = true;
          cnfClause.clauseIndex = clauseExtra->index;
          cnfClause.hasClauseCount = true;
          cnfClause.clauseCount = clauseExtra->count;
        }
        emitKernelV1(
          "cnf_clause",
          kernelFields,
          false,
          nullptr,
          nullptr,
          nullptr,
          nullptr,
          &cnfClause);
      }
      fields.push_back("rule=" + Kernel::ruleName(u->inference().rule()));
      fields.push_back("parent_unit=" + std::to_string(parent->number()));
      fields.push_back(std::string("parent_kind=") + (parent->isClause() ? "clause" : "formula"));
      std::string sourceText;
      if (renderUnitForExtra(parent, sourceText)) {
        fields.push_back("source=" + sourceText);
        fields.push_back("source_proposition=" + sourceText);
      }
      std::string targetText;
      if (renderUnitForExtra(u, targetText)) {
        fields.push_back("target=" + targetText);
        fields.push_back("target_proposition=" + targetText);
      }
      std::string targetClause;
      if (certificateClauseJson(u->asClause(), targetClause)) {
        fields.push_back("target_clause=" + targetClause);
      } else {
        fields.push_back("target_clause_conversion_failed=1");
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
      if (extra != nullptr) {
        const auto* clauseExtra = static_cast<const Inferences::CNFClauseInferenceExtra*>(extra);
        fields.push_back("clause_parent_unit=" + std::to_string(clauseExtra->parentNumber));
        fields.push_back("clause_index=" + std::to_string(clauseExtra->index));
        fields.push_back("clause_count=" + std::to_string(clauseExtra->count));
      }
      addClauseVariableSortFields(fields, "target", u->asClause());
      addLambdaSubtermFields(fields, "target", u->asClause(), nullptr);
      emit("cnf", fields);
    }
  }

  if (u->inference().rule() == Kernel::InferenceRule::SKOLEMIZE && !u->isClause()) {
    {
      std::vector<std::string> kernelFields;
      std::string resultFormula;
      if (certificateFormulaTermSexpr(u->getFormula(), resultFormula)) {
        kernelFields.push_back("result_formula=" + resultFormula);
      }
      unsigned kernelParentIndex = 0;
      for (Kernel::Unit* parent : iterTraits(u->getParents())) {
        const std::string prefix = "parent_" + std::to_string(kernelParentIndex);
        kernelFields.push_back(prefix + "_unit=u" + std::to_string(parent->number()));
        if (kernelParentIndex == 0) {
          kernelFields.push_back("source_unit=u" + std::to_string(parent->number()));
        }
        if (!parent->isClause()) {
          std::string parentFormula;
          if (certificateFormulaTermSexpr(parent->getFormula(), parentFormula)) {
            kernelFields.push_back(prefix + "_formula=" + parentFormula);
            if (kernelParentIndex == 0) {
              kernelFields.push_back("source_formula=" + parentFormula);
            }
          }
        }
        ++kernelParentIndex;
      }
      kernelFields.push_back("proof_parent_count=" + std::to_string(kernelParentIndex));
      std::vector<MegalodonKernelSyntax::RenderedKernelSkolemIntroducedSymbol> skolemIntroducedSymbols;
      if (_is->hasIntroducedSymbols(u)) {
        auto& symbols = _is->getIntroducedSymbols(u);
        Kernel::Formula* sourceFormulaForSkolem = nullptr;
        for (Kernel::Unit* parent : iterTraits(u->getParents())) {
          if (!parent->isClause()) {
            sourceFormulaForSkolem = parent->getFormula();
          }
          break;
        }
        std::map<unsigned, Kernel::TermList> sourceVariableSorts;
        if (sourceFormulaForSkolem != nullptr) {
          Lib::DHMap<unsigned, Kernel::TermList> collectedSorts;
          Kernel::SortHelper::collectVariableSorts(sourceFormulaForSkolem, collectedSorts);
          Lib::DHMap<unsigned, Kernel::TermList>::Iterator sortIterator(collectedSorts);
          while (sortIterator.hasNext()) {
            unsigned var;
            Kernel::TermList sort;
            sortIterator.next(var, sort);
            sourceVariableSorts[var] = sort;
          }
        }
        unsigned symbolIndex = 0;
        for (auto symbol : iterTraits(Kernel::InferenceStore::SymbolStack::ConstIterator(symbols))) {
          MegalodonKernelSyntax::RenderedKernelSkolemIntroducedSymbol introduced;
          introduced.index = symbolIndex;
          introduced.hasKind = true;
          introduced.kind = std::to_string(static_cast<int>(symbol.first));
          introduced.hasRawSymbol = true;
          introduced.rawSymbol = std::to_string(symbol.second);
          long replacedVar = _is->variableReplacedByIntroducedSymbol(symbol.second);
          if (replacedVar >= 0) {
            introduced.hasReplacedVariable = true;
            introduced.replacedVariable = variableName(static_cast<unsigned>(replacedVar));
          }
          if (symbol.first == SymbolType::FUNC) {
            std::string name = functionName(symbol.second);
            introduced.hasSymbol = true;
            introduced.symbol = name;
            std::string declaration = functionDeclaration(symbol.second, name);
            if (!declaration.empty()) {
              introduced.hasDeclaration = true;
              introduced.declaration = declaration;
            }
            if (replacedVar >= 0 && sourceFormulaForSkolem != nullptr) {
              auto replacedSort = sourceVariableSorts.find(static_cast<unsigned>(replacedVar));
              if (replacedSort != sourceVariableSorts.end()) {
                std::string replacedSortText;
                std::string replacedSortSexpr;
                if (sortToMegalodon(replacedSort->second, replacedSortText)) {
                  introduced.hasReplacedVariableSort = true;
                  introduced.replacedVariableSort = replacedSortText;
                }
                if (certificateTypeSexpr(replacedSort->second, replacedSortSexpr)) {
                  introduced.hasReplacedVariableSortSexpr = true;
                  introduced.replacedVariableSortSexpr =
                    MegalodonKernelSyntax::type(replacedSortSexpr);
                }
              }
              Kernel::TermList witness;
              unsigned parentApplicationCount = 0;
              if (skolemWitnessTerm(
                  sourceFormulaForSkolem,
                  u->getFormula(),
                  symbol.second,
                  static_cast<unsigned>(replacedVar),
                  witness,
                  parentApplicationCount)) {
                std::string witnessSexpr;
                if (certificateTermSexpr(witness, witnessSexpr)) {
                  introduced.hasWitnessTerm = true;
                  introduced.witnessTerm = MegalodonKernelSyntax::term(witnessSexpr);
                }
                Kernel::TermList witnessSort;
                if (Kernel::SortHelper::tryGetResultSort(witness, witnessSort)) {
                  std::string witnessSortText;
                  std::string witnessSortSexpr;
                  if (sortToMegalodon(witnessSort, witnessSortText)) {
                    introduced.hasWitnessSort = true;
                    introduced.witnessSort = witnessSortText;
                  }
                  if (certificateTypeSexpr(witnessSort, witnessSortSexpr)) {
                    introduced.hasWitnessSortSexpr = true;
                    introduced.witnessSortSexpr = MegalodonKernelSyntax::type(witnessSortSexpr);
                  }
                }
                introduced.hasSourceVariableApplicationCount = true;
                introduced.sourceVariableApplicationCount = parentApplicationCount;
                Kernel::TermList witnessHead;
                std::vector<Kernel::TermList> dependencies;
                decomposeApplicationSpine(witness, witnessHead, dependencies);
                if (termHasHeadFunctor(witnessHead, symbol.second)) {
                  for (std::size_t dependencyIndex = 0; dependencyIndex < dependencies.size(); ++dependencyIndex) {
                    MegalodonKernelSyntax::RenderedKernelSkolemDependency dependency;
                    std::string dependencySexpr;
                    if (certificateTermSexpr(dependencies[dependencyIndex], dependencySexpr)) {
                      dependency.hasTerm = true;
                      dependency.term = MegalodonKernelSyntax::term(dependencySexpr);
                    }
                    if (dependencies[dependencyIndex].isVar()) {
                      unsigned dependencyVar = dependencies[dependencyIndex].var();
                      dependency.hasVariable = true;
                      dependency.variable = variableName(dependencyVar);
                      auto dependencySort = sourceVariableSorts.find(dependencyVar);
                      if (dependencySort != sourceVariableSorts.end()) {
                        std::string dependencySortText;
                        std::string dependencySortSexpr;
                        if (sortToMegalodon(dependencySort->second, dependencySortText)) {
                          dependency.hasSort = true;
                          dependency.sort = dependencySortText;
                        }
                        if (certificateTypeSexpr(dependencySort->second, dependencySortSexpr)) {
                          dependency.hasSortSexpr = true;
                          dependency.sortSexpr = MegalodonKernelSyntax::type(dependencySortSexpr);
                        }
                      }
                    } else {
                      Kernel::TermList dependencySort;
                      if (Kernel::SortHelper::tryGetResultSort(dependencies[dependencyIndex], dependencySort)) {
                        std::string dependencySortText;
                        std::string dependencySortSexpr;
                        if (sortToMegalodon(dependencySort, dependencySortText)) {
                          dependency.hasSort = true;
                          dependency.sort = dependencySortText;
                        }
                        if (certificateTypeSexpr(dependencySort, dependencySortSexpr)) {
                          dependency.hasSortSexpr = true;
                          dependency.sortSexpr = MegalodonKernelSyntax::type(dependencySortSexpr);
                        }
                      }
                    }
                    introduced.dependencies.push_back(dependency);
                  }
                }
                introduced.hasChoicePrinciple = true;
                introduced.choicePrinciple = "classical_choice";
              }
            }
          } else if (symbol.first == SymbolType::PRED) {
            std::string name = predicateName(symbol.second);
            introduced.hasSymbol = true;
            introduced.symbol = name;
            std::string declaration = predicateDeclaration(symbol.second, name);
            if (!declaration.empty()) {
              introduced.hasDeclaration = true;
              introduced.declaration = declaration;
            }
          } else {
            introduced.hasSymbol = true;
            introduced.symbol = recoverMegalodonSymbolName(env.signature->typeConName(symbol.second), "T");
          }
          skolemIntroducedSymbols.push_back(introduced);
          ++symbolIndex;
        }
      }
      emitKernelV1(
        "skolemize",
        kernelFields,
        false,
        nullptr,
        skolemIntroducedSymbols.empty() ? nullptr : &skolemIntroducedSymbols);
    }
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
        {
          std::vector<std::string> kernelFields;
          MegalodonKernelSyntax::RenderedKernelPredicateDefinition predicateDefinition;
          predicateDefinition.introducedSymbol = name;
          if (!sort.empty()) {
            predicateDefinition.hasSort = true;
            predicateDefinition.sort = sort;
          }
          std::string symbolName;
          if (certificatePredicateDefinitionSymbol(u->getFormula(), symbolName)) {
            predicateDefinition.hasDefiniendumSymbol = true;
            predicateDefinition.definiendumSymbol = symbolName;
          }
          std::string bodyFormula;
          if (certificateFormulaTermSexpr(formula, bodyFormula)) {
            predicateDefinition.hasBodyFormula = true;
            predicateDefinition.bodyFormula = MegalodonKernelSyntax::formula(bodyFormula);
          }
          std::string resultFormula;
          if (certificateFormulaTermSexpr(u->getFormula(), resultFormula)) {
            predicateDefinition.hasResultFormula = true;
            predicateDefinition.resultFormula = MegalodonKernelSyntax::formula(resultFormula);
          }
          for (std::size_t index = 0; index < renderedBodyVarSorts.size(); ++index) {
            MegalodonKernelSyntax::RenderedKernelPredicateDefinitionVariable variable;
            variable.index = index;
            variable.renderedSort = renderedBodyVarSorts[index].second;
            predicateDefinition.bodyVariables.push_back(variable);
          }
          emitKernelV1(
            "predicate_definition",
            kernelFields,
            false,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            &predicateDefinition);
        }
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

  if (u->isClause()
    && u->inference().rule() == Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL
    && parentClauses.size() == 1) {
    Kernel::Clause* parent = parentClauses[0];
    auto isTruthConstant = [](const std::string& rendered, const std::string& name) {
      return rendered == "(TMH \"" + name + "\")";
    };
    auto isPositiveTruthConflict = [&](Kernel::Literal* literal) {
      if (literal == nullptr
        || !literal->isEquality()
        || !literal->isPositive()) {
        return false;
      }
      std::string lhs;
      std::string rhs;
      if (!termSexprForKernel(*literal->nthArgument(0), lhs)
        || !termSexprForKernel(*literal->nthArgument(1), rhs)) {
        return false;
      }
      return (isTruthConstant(lhs, "f__true") && isTruthConstant(rhs, "f__false"))
        || (isTruthConstant(lhs, "f__false") && isTruthConstant(rhs, "f__true"));
    };

    for (unsigned literalIndex = 0; literalIndex < parent->length(); ++literalIndex) {
      Kernel::Literal* literal = (*parent)[literalIndex];
      if (!isPositiveTruthConflict(literal)) {
        continue;
      }
      std::vector<std::string> kernelFields;
      kernelFields.push_back("selected_parent_index=0");
      kernelFields.push_back("selected_literal_index=" + std::to_string(literalIndex));
      std::string rendered;
      if (literalSexprForKernel(literal, rendered)) {
        kernelFields.push_back("selected=" + rendered);
        kernelFields.push_back("selected_substituted=" + rendered);
      }
      std::string resultClause;
      if (clauseSexprForKernel(u->asClause(), resultClause)) {
        kernelFields.push_back("result_clause=" + resultClause);
      }
      emitKernelV1("truth_conflict", kernelFields);
      break;
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
      {
        std::vector<std::string> kernelFields;
        MegalodonKernelSyntax::RenderedKernelUrrTrace urrTrace;
        if (urr->mainParent != nullptr) {
          urrTrace.hasMainParent = true;
          urrTrace.mainParent =
            MegalodonKernelSyntax::unitRef("u" + std::to_string(urr->mainParent->number()));
        }
        for (std::size_t traceIndex = 0; traceIndex < urr->steps.size(); ++traceIndex) {
          const auto& trace = urr->steps[traceIndex];
          MegalodonKernelSyntax::RenderedKernelUrrTraceStep traceStep;
          traceStep.index = traceIndex;
          if (trace.unitParent != nullptr) {
            traceStep.hasUnitParent = true;
            traceStep.unitParent =
              MegalodonKernelSyntax::unitRef("u" + std::to_string(trace.unitParent->number()));
            std::string clause;
            if (clauseSexprForKernel(trace.unitParent, clause)) {
              traceStep.hasUnitParentClause = true;
              traceStep.unitParentClause = MegalodonKernelSyntax::clause(clause);
            }
          }
          std::string rendered;
          if (literalSexprForKernel(trace.selected, rendered)) {
            traceStep.hasSelected = true;
            traceStep.selected = MegalodonKernelSyntax::literal(rendered);
          }
          if (literalSexprForKernel(trace.selectedSubstituted, rendered)) {
            traceStep.hasSelectedSubstituted = true;
            traceStep.selectedSubstituted = MegalodonKernelSyntax::literal(rendered);
          }
          if (literalSexprForKernel(trace.unitSubstituted, rendered)) {
            traceStep.hasUnitSubstituted = true;
            traceStep.unitSubstituted = MegalodonKernelSyntax::literal(rendered);
          }
          if (literalVectorClauseSexprForKernel(trace.remainingAfter, rendered)) {
            traceStep.hasRemainingAfter = true;
            traceStep.remainingAfter = MegalodonKernelSyntax::clause(rendered);
          }
          urrTrace.steps.push_back(traceStep);
        }
        std::string remaining;
        if (literalVectorClauseSexprForKernel(urr->remaining, remaining)) {
          urrTrace.hasRemaining = true;
          urrTrace.remaining = MegalodonKernelSyntax::clause(remaining);
        }
        std::string primitiveExpansion;
        std::vector<MegalodonKernelSyntax::PrimitiveStep> primitiveSteps;
        const std::string unitPrefix = "u" + std::to_string(u->number());
        const bool hasResolvePrimitiveExpansion =
          certificateUnitResultingResolutionStepsSexpr(
            u,
            primitiveExpansion,
            false,
            &primitiveSteps)
          && primitiveExpansion.find("(unit_resulting_resolution ") == std::string::npos
          && primitiveExpansion.find("(resolve \"" + unitPrefix + "_resolve") != std::string::npos;
        if (hasResolvePrimitiveExpansion
          && MegalodonKernelSyntax::appendPrimitiveExpansionChainFields(
            kernelFields,
            primitiveSteps,
            unitPrefix)) {
          emitKernelV1(
            "unit_resulting_resolution",
            kernelFields,
            false,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            nullptr,
            &urrTrace);
        }
      }
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

  if (u->isClause()
    && extra == nullptr
    && (
      u->inference().rule() == Kernel::InferenceRule::EQUALITY_RESOLUTION
      || u->inference().rule() == Kernel::InferenceRule::EQUALITY_RESOLUTION_WITH_DELETION
      || u->inference().rule() == Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL
    )) {
    std::string primitiveExpansion;
    if (certificateEqualityResolutionStepSexpr(u, info, primitiveExpansion)) {
      std::vector<std::string> kernelFields;
      if (parentClauses.size() == 1) {
        for (unsigned literalIndex = 0; literalIndex < parentClauses[0]->length(); ++literalIndex) {
          Kernel::Literal* literal = (*parentClauses[0])[literalIndex];
          if (literal != nullptr && literal->isEquality() && !literal->isPositive()) {
            addKernelLiteralFields(kernelFields, "selected", literal, 0);
            break;
          }
        }
      }
      emitKernelV1("equality_resolution", kernelFields);
    }
  }

  if (extra == nullptr) {
    return;
  }

  switch (u->inference().rule()) {
    case Kernel::InferenceRule::SUPERPOSITION:
    case Kernel::InferenceRule::EQUALITY_FACTORING: {
      const auto* rewrite = static_cast<const Inferences::TwoLiteralRewriteInferenceExtra*>(extra);
      {
        std::vector<std::string> kernelFields;
        addKernelLiteralFields(kernelFields, "selected", rewrite->selected.selectedLiteral.selectedLiteral, 0);
        addKernelLiteralFields(kernelFields, "other", rewrite->selected.otherLiteral, 1);
        addKernelTermField(kernelFields, "rewrite_lhs", rewrite->rewrite.lhs);
        addKernelTermField(kernelFields, "rewrite_redex", rewrite->rewrite.rewritten);
        if (u->inference().rule() == Kernel::InferenceRule::SUPERPOSITION) {
          addKernelSuperpositionRewriteFields(
            kernelFields,
            rewrite->selected.selectedLiteral.selectedLiteral,
            rewrite->selected.otherLiteral);
        }
        emitKernelV1(
          u->inference().rule() == Kernel::InferenceRule::SUPERPOSITION
            ? "superposition"
            : "equality_factoring",
          kernelFields,
          true);
      }
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
      {
        std::vector<std::string> kernelFields;
        addKernelLiteralFields(kernelFields, "selected", selected->selectedLiteral.selectedLiteral, 0);
        addKernelLiteralFields(kernelFields, "other", selected->otherLiteral, 1);
        if (selected->synthesisExtra.condition != nullptr) {
          addKernelLiteralFields(kernelFields, "condition", selected->synthesisExtra.condition);
        }
        if (selected->synthesisExtra.thenLit != nullptr) {
          addKernelLiteralFields(kernelFields, "then", selected->synthesisExtra.thenLit);
        }
        if (selected->synthesisExtra.elseLit != nullptr) {
          addKernelLiteralFields(kernelFields, "else", selected->synthesisExtra.elseLit);
        }
        emitKernelV1(
          u->inference().rule() == Kernel::InferenceRule::RESOLUTION ? "resolution" : "factoring",
          kernelFields,
          true);
      }
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
      {
        std::vector<std::string> kernelFields;
        addKernelTermField(kernelFields, "rule_lhs", rewrite->lhs);
        addKernelTermField(kernelFields, "redex", rewrite->rewritten);
        if (rewrite->hasRhs) {
          addKernelTermField(kernelFields, "rule_rhs", rewrite->rhs);
        }
        if (rewrite->hasReplacement) {
          addKernelTermField(kernelFields, "replacement", rewrite->replacement);
        }
        if (info != nullptr && info->hasDemodulationRewrite) {
          addKernelTermField(kernelFields, "replay_rule_lhs", info->demodulationRuleLhs);
          addKernelTermField(kernelFields, "replay_rule_rhs", info->demodulationRuleRhs);
          addKernelTermField(kernelFields, "replay_redex", info->demodulationRedex);
          addKernelTermField(kernelFields, "replay_replacement", info->demodulationReplacement);
          addKernelDemodulationRewriteFields(kernelFields);
        }
        emitKernelV1("rewrite", kernelFields);
      }
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
      {
        std::vector<std::string> kernelFields;
        MegalodonKernelSyntax::RenderedKernelSubsumptionResolutionPivot subsumptionPivot;
        bool hasSubsumptionPivot = false;
        addKernelLiteralFields(kernelFields, "selected", selected->selectedLiteral, 0);
        if (parentClauses.size() == 2) {
          auto [selectedParentIndex, selectedLiteralIndex] = literalPosition(selected->selectedLiteral, 0);
          if (selectedParentIndex >= 0 && selectedLiteralIndex >= 0) {
            std::size_t mainParentIndex = static_cast<std::size_t>(selectedParentIndex);
            std::size_t sideParentIndex = mainParentIndex == 0 ? 1 : 0;
            subsumptionPivot.mainParentIndex = mainParentIndex;
            subsumptionPivot.sideParentIndex = sideParentIndex;
            hasSubsumptionPivot = true;
            SATSubsumption::SATSubsumptionAndResolution satSR;
            if (satSR.checkSubsumptionResolutionWithLiteral(
                  parentClauses[sideParentIndex],
                  parentClauses[mainParentIndex],
                  static_cast<unsigned>(selectedLiteralIndex))) {
              Kernel::Substitution substitution = satSR.getBindingsForSubsumptionResolutionWithLiteral();
              std::string sideSubstitution;
              if (substitutionSexprForKernel(substitution, sideSubstitution)) {
                subsumptionPivot.hasSideSubstitution = true;
                subsumptionPivot.sideSubstitution =
                  MegalodonKernelSyntax::substitution(sideSubstitution);
              }
              for (unsigned sideLiteralIndex = 0;
                   sideLiteralIndex < parentClauses[sideParentIndex]->length();
                   ++sideLiteralIndex) {
                Kernel::Literal* sideLiteral = (*parentClauses[sideParentIndex])[sideLiteralIndex];
                Kernel::Literal* sideSubstituted = Kernel::SubstHelper::apply(sideLiteral, substitution);
                if (selected->selectedLiteral->isPositive() == sideSubstituted->isPositive()) {
                  continue;
                }
                std::string selectedAtom;
                std::string sideAtom;
                if (!certificateAtomSexpr(selected->selectedLiteral, selectedAtom)
                  || !certificateAtomSexpr(sideSubstituted, sideAtom)) {
                  continue;
                }
                bool matchesBySymmetry = false;
                if (selectedAtom != sideAtom) {
                  if (!sideSubstituted->isEquality()) {
                    continue;
                  }
                  std::string lhs;
                  std::string rhs;
                  if (!termSexprForKernel(*sideSubstituted->nthArgument(1), lhs)
                    || !termSexprForKernel(*sideSubstituted->nthArgument(0), rhs)) {
                    continue;
                  }
                  sideAtom = "(AP (AP (TMH \"=\") " + lhs + ") " + rhs + ")";
                  if (selectedAtom != sideAtom) {
                    continue;
                  }
                  matchesBySymmetry = true;
                }
                std::string sidePivot;
                std::string sidePivotSubstituted;
                if (literalSexprForKernel(sideLiteral, sidePivot)) {
                  subsumptionPivot.hasSidePivot = true;
                  subsumptionPivot.sidePivot = MegalodonKernelSyntax::literal(sidePivot);
                }
                subsumptionPivot.hasSidePivotLocation = true;
                subsumptionPivot.sidePivotParentIndex = sideParentIndex;
                subsumptionPivot.sidePivotLiteralIndex = sideLiteralIndex;
                subsumptionPivot.sidePivotParentUnit =
                  MegalodonKernelSyntax::unitRef("u" + std::to_string(parentClauses[sideParentIndex]->number()));
                if (literalSexprForKernel(sideSubstituted, sidePivotSubstituted)) {
                  subsumptionPivot.hasSidePivotSubstituted = true;
                  subsumptionPivot.sidePivotSubstituted =
                    MegalodonKernelSyntax::literal(sidePivotSubstituted);
                }
                if (matchesBySymmetry) {
                  subsumptionPivot.sidePivotMatchesBySymmetry = true;
                }
                break;
              }
            }
          }
        }
        if (u->inference().rule() == Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
          || u->inference().rule() == Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION) {
          std::string primitiveExpansion;
          std::vector<MegalodonKernelSyntax::PrimitiveStep> primitiveSteps;
          if (certificateSubstitutedResolutionStepsSexpr(
                u,
                info,
                primitiveExpansion,
                &primitiveSteps)
            && MegalodonKernelSyntax::appendPrimitiveExpansionChainFields(
              kernelFields,
              primitiveSteps,
              "u" + std::to_string(u->number()))) {
          } else if (certificateNativeStepSexpr(u, info, primitiveExpansion)) {
            MegalodonKernelSyntax::appendPrimitiveExpansionChainFields(
              kernelFields,
              primitiveExpansion,
              "subsumption_resolution");
          }
        }
        emitKernelV1(
          u->inference().rule() == Kernel::InferenceRule::EQUALITY_RESOLUTION
            ? "equality_resolution"
            : "subsumption_resolution",
          kernelFields,
          false,
          hasSubsumptionPivot ? &subsumptionPivot : nullptr);
      }
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

std::string MegalodonChecker::certificateFallbackSourceJson(Kernel::Unit* u)
{
  Kernel::InferenceRule rule = u->inference().rule();
  bool hasParents = u->getParents().hasNext();
  std::string sourceKind = hasParents ? "vampire_unexpanded_derived_clause" : "vampire_input_clause";
  switch (rule) {
    case Kernel::InferenceRule::CLAUSIFY:
      sourceKind = "vampire_cnf_clause";
      break;
    case Kernel::InferenceRule::AVATAR_COMPONENT:
      sourceKind = "vampire_avatar_component_clause";
      break;
    case Kernel::InferenceRule::SKOLEMIZE:
      sourceKind = "vampire_skolemized_formula";
      break;
    default:
      break;
  }

  std::ostringstream source;
  source << "{\"kind\":" << quote(sourceKind)
         << ",\"name\":" << quote("u" + std::to_string(u->number()))
         << ",\"vampire_rule\":" << quote(Kernel::ruleName(rule))
         << ",\"replay_kind\":" << quote(replayKind(rule))
         << ",\"target_unit_kind\":" << quote(unitKind(u))
         << ",\"vampire_parents\":[";

  bool firstParent = true;
  for (Kernel::Unit* parent : iterTraits(u->getParents())) {
    if (!firstParent) {
      source << ',';
    }
    firstParent = false;
    source << quote("u" + std::to_string(parent->number()));
  }
  source << "],\"vampire_clause_parents\":[";

  bool firstClauseParent = true;
  for (Kernel::Unit* parent : iterTraits(u->getParents())) {
    if (!parent->isClause()) {
      continue;
    }
    if (!firstClauseParent) {
      source << ',';
    }
    firstClauseParent = false;
    source << quote("u" + std::to_string(parent->number()));
  }
  source << "]";

  if (u->isClause()) {
    std::string targetClause;
    if (certificateClauseJson(u->asClause(), targetClause)) {
      source << ",\"target_clause\":" << targetClause;
    }
  }

  if (rule == Kernel::InferenceRule::CLAUSIFY && u->isClause()) {
    source << ",\"cnf\":{\"rule\":" << quote(Kernel::ruleName(rule));
    UnitIterator parentIterator = u->getParents();
    if (parentIterator.hasNext()) {
      Kernel::Unit* parent = parentIterator.next();
      source << ",\"parent\":" << quote("u" + std::to_string(parent->number()))
             << ",\"parent_kind\":" << quote(unitKind(parent));
      const auto* parentExtra = env.proofExtra.find(parent);
      if (parentExtra != nullptr) {
        const auto* cnfExtra = static_cast<const Inferences::CNFTransformationInferenceExtra*>(parentExtra);
        source << ",\"parent_clause_count\":" << cnfExtra->number;
      }
    }
    const auto* extra = env.proofExtra.find(u);
    if (extra != nullptr) {
      const auto* clauseExtra = static_cast<const Inferences::CNFClauseInferenceExtra*>(extra);
      source << ",\"clause_parent_unit\":" << quote("u" + std::to_string(clauseExtra->parentNumber))
             << ",\"clause_index\":" << clauseExtra->index
             << ",\"clause_count\":" << clauseExtra->count;
    }
    source << "}";
  }

  source << "}";
  return source.str();
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
  _usesEquality = true;
  _equalitySorts.insert(sortText);
  return true;
}

std::string MegalodonChecker::sortSymbolSuffix(const std::string& sort) const
{
  std::string normalized;
  for (std::size_t i = 0; i < sort.size(); ++i) {
    if (i + 1 < sort.size() && sort[i] == '-' && sort[i + 1] == '>') {
      normalized += "_to_";
      ++i;
    } else if (sort[i] == '(') {
      normalized += "lp_";
    } else if (sort[i] == ')') {
      normalized += "_rp";
    } else if (std::isalnum(static_cast<unsigned char>(sort[i])) || sort[i] == '_') {
      normalized += sort[i];
    } else if (!normalized.empty() && normalized.back() != '_') {
      normalized += '_';
    }
  }
  std::string compact;
  bool previousUnderscore = false;
  for (char ch : normalized) {
    if (ch == '_') {
      if (!previousUnderscore) {
        compact += ch;
      }
      previousUnderscore = true;
    } else {
      compact += ch;
      previousUnderscore = false;
    }
  }
  while (!compact.empty() && compact.front() == '_') {
    compact.erase(compact.begin());
  }
  while (!compact.empty() && compact.back() == '_') {
    compact.pop_back();
  }
  return compact.empty() ? "set" : compact;
}

std::string MegalodonChecker::equalityNameForSort(const std::string& sort) const
{
  if (sort == "set") {
    return "eq";
  }
  if (sort == "prop") {
    return "vampire_eq_prop";
  }
  return "vampire_eq_" + sortSymbolSuffix(sort);
}

std::string MegalodonChecker::equalityDefinition(const std::string& sortText) const
{
  if (sortText == "set") {
    return "Definition eq : set->set->prop := fun x y:set => forall Q:set->set->prop, Q x y -> Q y x.";
  }
  std::string argumentSort = sortText.find("->") == std::string::npos ? sortText : parenthesize(sortText);
  return "Definition " + equalityNameForSort(sortText) + " : " + argumentSort + "->" + argumentSort
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
        _equalitySorts.insert("set");
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
        if (literal->nthArgument(i)->isApplication()
          || (literal->nthArgument(i)->isTerm()
            && (literal->nthArgument(i)->term()->isSpecial()
              || literal->nthArgument(i)->term()->numTermArguments() > 0))) {
          arg = parenthesize(arg);
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
    if (equalitySort == "set") {
      result = lhs + " = " + rhs;
    } else {
      result = equalityNameForSort(equalitySort) + " " + parenthesize(lhs) + " " + parenthesize(rhs);
    }
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
    if (literal->nthArgument(i)->isApplication()
      || (literal->nthArgument(i)->isTerm()
        && (literal->nthArgument(i)->term()->isSpecial()
          || literal->nthArgument(i)->term()->numTermArguments() > 0))) {
      arg = parenthesize(arg);
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

bool MegalodonChecker::certificateSplitLiteralJson(unsigned split, std::string& result)
{
  std::string rawName = Saturation::Splitter::getFormulaStringFromName(split, true);
  bool negative = false;
  if (!rawName.empty() && rawName[0] == '~') {
    negative = true;
    rawName = rawName.substr(1);
  } else if (rawName.rfind("¬", 0) == 0) {
    negative = true;
    rawName = rawName.substr(2);
  }
  result = std::string("{\"polarity\":")
    + (negative ? "false" : "true")
    + ",\"atom\":{\"pred\":"
    + quote(sanitizeMegalodonName(rawName, "split"))
    + ",\"args\":[]}}";
  return true;
}

bool MegalodonChecker::appendCertificateSplitLiteralsJson(Kernel::Clause* clause, std::vector<std::string>& literals)
{
  if (!clause->splits() || clause->splits()->isEmpty()) {
    return true;
  }
  for (unsigned split : iterTraits(clause->splits()->iter())) {
    std::string rendered;
    if (!certificateSplitLiteralJson(split, rendered)) {
      return false;
    }
    literals.push_back(rendered);
  }
  return true;
}

bool MegalodonChecker::appendCertificateClauseLiteralsJson(Kernel::Clause* clause, std::vector<std::string>& literals)
{
  for (Kernel::Literal* literal : clause->iterLits()) {
    std::string rendered;
    if (!certificateLiteralJson(literal, rendered)) {
      return false;
    }
    literals.push_back(rendered);
  }
  return appendCertificateSplitLiteralsJson(clause, literals);
}

bool MegalodonChecker::appendCertificateSubstitutedClauseLiteralsPreservingEqualityJson(
  Kernel::Clause* clause,
  const Kernel::Substitution& substitution,
  std::vector<std::string>& literals)
{
  for (Kernel::Literal* literal : clause->iterLits()) {
    std::string rendered;
    if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, rendered)) {
      return false;
    }
    literals.push_back(rendered);
  }
  return appendCertificateSplitLiteralsJson(clause, literals);
}

bool MegalodonChecker::certificateClauseJson(Kernel::Clause* clause, std::string& result)
{
  std::vector<std::string> literals;
  if (!appendCertificateClauseLiteralsJson(clause, literals)) {
    return false;
  }
  std::ostringstream out;
  out << '[';
  for (std::size_t i = 0; i < literals.size(); ++i) {
    if (i != 0) {
      out << ',';
    }
    out << literals[i];
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
  std::vector<std::string> literals;
  if (!appendCertificateSubstitutedClauseLiteralsPreservingEqualityJson(clause, substitution, literals)) {
    return false;
  }
  std::ostringstream out;
  out << '[';
  for (std::size_t i = 0; i < literals.size(); ++i) {
    if (i != 0) {
      out << ',';
    }
    out << literals[i];
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
  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
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
    return excludedOne && appendCertificateSplitLiteralsJson(clause, literals);
  };
  auto renderedClause = [&](Kernel::Clause* clause, std::vector<std::string>& literals) {
    return appendCertificateClauseLiteralsJson(clause, literals);
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
    unsigned leftPivotIndex = 0;
    unsigned rightPivotIndex = 0;
    if (!literalIndex(parents[0], leftPivot, leftPivotIndex)
      || !literalIndex(parents[1], rightPivot, rightPivotIndex)
      || !certificateLiteralJson(leftPivot, pivot)) {
      return false;
    }
    stepJson = "{\"rule\":\"resolve\","
      "\"parents\":["
      + quote("u" + std::to_string(parents[0]->number())) + ","
      + quote("u" + std::to_string(parents[1]->number())) + "],"
      "\"left_pivot_index\":" + std::to_string(leftPivotIndex) + ","
      "\"right_pivot_index\":" + std::to_string(rightPivotIndex) + ","
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
    if (!appendCertificateSplitLiteralsJson(parent, expected)) {
      return false;
    }
    std::sort(expected.begin(), expected.end());
    expected.erase(std::unique(expected.begin(), expected.end()), expected.end());
    return true;
  };
  auto normalizedActualClause = [&](std::vector<std::string>& actual) {
    if (!appendCertificateClauseLiteralsJson(unit->asClause(), actual)) {
      return false;
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
    std::vector<std::string> expected;
    std::vector<std::pair<std::string, std::string>> symmetryCandidates;
    std::vector<std::string> actual;
    if (!substitutedConclusionWithout(selectedLiteral, expected, symmetryCandidates)
      || !normalizedActualClause(actual)) {
      return false;
    }

    std::string literal;
    unsigned literalIndex = 0;
    bool foundLiteral = false;
    for (unsigned i = 0; i < parent->length(); ++i) {
      if ((*parent)[i] == selectedLiteral) {
        literalIndex = i;
        foundLiteral = true;
        break;
      }
    }
    if (!foundLiteral || !certificateLiteralJson(selectedLiteral, literal)) {
      return false;
    }
    std::string substitution;
    if (!certificateSubstitutionJson(*selectedSubstitution, substitution)) {
      return false;
    }

    std::string stepBase = "u" + std::to_string(unit->number());
    if (!isNegativeReflexiveEquality(selectedLiteral)) {
      std::vector<std::string> constraints;
      std::vector<std::string> remainingActual = actual;
      for (const std::string& literalJson : expected) {
        auto literalIt = std::find(remainingActual.begin(), remainingActual.end(), literalJson);
        if (literalIt == remainingActual.end()) {
          return false;
        }
        remainingActual.erase(literalIt);
      }
      constraints = remainingActual;
      if (constraints.empty()) {
        return false;
      }
      result =
        "{\"rule\":\"equality_resolution_constraints\","
      "\"parents\":["
      + quote("u" + std::to_string(parent->number())) + "],"
      "\"literal_index\":" + std::to_string(literalIndex) + ","
      "\"literal\":" + literal + ","
      "\"substitution\":" + substitution + ","
      "\"constraints\":" + jsonArray(constraints) + ","
        "\"clause\":" + jsonArray(actual) + "}";
      return true;
    }

    std::string equalityResolutionStep =
      "{\"rule\":\"equality_resolution\","
      "\"parents\":["
      + quote("u" + std::to_string(parent->number())) + "],"
      "\"literal_index\":" + std::to_string(literalIndex) + ","
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
      "\"literal_index\":" + std::to_string(literalIndex) + ","
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

bool MegalodonChecker::certificateTruthConflictResolutionStepJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation* replayInfo,
  std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || rule != Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL) {
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
  auto isTruthConstant = [](const std::string& rendered, const std::string& name) {
    return rendered == "{\"const\":\"" + name + "\"}";
  };
  auto isPositiveTruthConflict = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isPositive()) {
      return false;
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(literal, *selectedSubstitution);
    std::string lhs;
    std::string rhs;
    if (!certificateTermJson(*substituted->nthArgument(0), lhs)
      || !certificateTermJson(*substituted->nthArgument(1), rhs)) {
      return false;
    }
    return (isTruthConstant(lhs, "f__true") && isTruthConstant(rhs, "f__false"))
      || (isTruthConstant(lhs, "f__false") && isTruthConstant(rhs, "f__true"));
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
    if (!isPositiveTruthConflict(selectedLiteral)) {
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
    std::string substitution;
    if (!certificateLiteralJson(selectedLiteral, literal)
      || !certificateSubstitutionJson(*selectedSubstitution, substitution)) {
      return false;
    }

    std::string stepBase = "u" + std::to_string(unit->number());
    std::string truthConflictStep =
      "{\"rule\":\"truth_conflict_resolution\","
      "\"parents\":["
      + quote("u" + std::to_string(parent->number())) + "],"
      "\"literal\":" + literal + ","
      "\"substitution\":" + substitution + "}";
    if (expected == actual) {
      result = truthConflictStep;
      return true;
    }

    std::vector<std::pair<std::string, std::string>> flips;
    if (!canNormalizeBySymmetry(expected, actual, symmetryCandidates, flips)) {
      return false;
    }

    std::vector<std::string> steps;
    std::string currentStepId = stepBase + "_truth_conflict";
    steps.push_back(
      "{\"id\":" + quote(currentStepId) + ","
      "\"rule\":\"truth_conflict_resolution\","
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

  for (Kernel::Literal* literal : parent->iterLits()) {
    if (emitStep(literal)) {
      return true;
    }
  }
  return false;
}

bool MegalodonChecker::certificateTrivialInequalityRemovalStepsJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::TRIVIAL_INEQUALITY_REMOVAL) {
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
    }
    normalize(literals);
    return true;
  };
  auto isTruthConstant = [](const std::string& rendered, const std::string& name) {
    return rendered == "{\"const\":\"" + name + "\"}";
  };
  auto isNegativeReflexiveEquality = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isNegative()) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    return certificateTermJson(*literal->nthArgument(0), lhs)
      && certificateTermJson(*literal->nthArgument(1), rhs)
      && lhs == rhs;
  };
  auto isPositiveTruthConflict = [&](Kernel::Literal* literal) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isPositive()) {
      return false;
    }
    std::string lhs;
    std::string rhs;
    if (!certificateTermJson(*literal->nthArgument(0), lhs)
      || !certificateTermJson(*literal->nthArgument(1), rhs)) {
      return false;
    }
    return (isTruthConstant(lhs, "f__true") && isTruthConstant(rhs, "f__false"))
      || (isTruthConstant(lhs, "f__false") && isTruthConstant(rhs, "f__true"));
  };

  std::vector<std::string> current;
  std::vector<std::string> target;
  if (!normalizedClause(parent, current)
    || !normalizedClause(unit->asClause(), target)) {
    return false;
  }
  if (current == target) {
    return false;
  }

  struct RemovedLiteral {
    std::string rule;
    std::string literalJson;
  };
  std::vector<RemovedLiteral> removals;
  for (Kernel::Literal* literal : parent->iterLits()) {
    std::string literalJson;
    if (!certificateLiteralJson(literal, literalJson)) {
      return false;
    }
    if (std::find(current.begin(), current.end(), literalJson) == current.end()
      || std::find(target.begin(), target.end(), literalJson) != target.end()) {
      continue;
    }
    if (isPositiveTruthConflict(literal)) {
      removals.push_back({"truth_conflict_resolution", literalJson});
    } else if (isNegativeReflexiveEquality(literal)) {
      removals.push_back({"equality_resolution", literalJson});
    } else {
      return false;
    }
  }
  if (removals.empty()) {
    return false;
  }

  std::vector<std::string> steps;
  std::string parentId = "u" + std::to_string(parent->number());
  std::string stepBase = "u" + std::to_string(unit->number());
  for (std::size_t index = 0; index < removals.size(); ++index) {
    const RemovedLiteral& removed = removals[index];
    auto literalIt = std::find(current.begin(), current.end(), removed.literalJson);
    if (literalIt == current.end()) {
      return false;
    }
    current.erase(literalIt);
    normalize(current);
    std::string stepId = index + 1 == removals.size()
      ? stepBase
      : stepBase + "_trivial" + std::to_string(index);
    steps.push_back(
      "{\"id\":" + quote(stepId) + ","
      "\"rule\":" + quote(removed.rule) + ","
      "\"parents\":[" + quote(parentId) + "],"
      "\"literal\":" + removed.literalJson + ","
      "\"substitution\":{},"
      "\"clause\":" + jsonArray(current) + "}");
    parentId = stepId;
  }

  if (current != target) {
    return false;
  }
  result = jsonArray(steps);
  return true;
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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

  bool foundDuplicate = false;
  unsigned leftLiteralIndex = 0;
  unsigned rightLiteralIndex = 0;
  for (unsigned left = 0; left < parent->length() && !foundDuplicate; ++left) {
    std::string leftLiteral;
    if (!certificateLiteralJson((*parent)[left], leftLiteral)) {
      return false;
    }
    for (unsigned right = left + 1; right < parent->length(); ++right) {
      std::string rightLiteral;
      if (!certificateLiteralJson((*parent)[right], rightLiteral)) {
        return false;
      }
      if (leftLiteral == rightLiteral) {
        leftLiteralIndex = left;
        rightLiteralIndex = right;
        foundDuplicate = true;
        break;
      }
    }
  }
  if (!foundDuplicate) {
    return false;
  }

  result = "{\"rule\":\"factor\","
    "\"parents\":["
    + quote("u" + std::to_string(parent->number())) + "],"
    "\"left_literal_index\":" + std::to_string(leftLiteralIndex) + ","
    "\"right_literal_index\":" + std::to_string(rightLiteralIndex) + "}";
  return true;
}

bool MegalodonChecker::certificateCondensationStepsJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::CONDENSATION) {
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
  Kernel::Clause* child = unit->asClause();
  if (parent->length() <= child->length()) {
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };
  auto substitutedParentLiterals = [&](const Kernel::Substitution& substitution, std::vector<std::string>& literals, std::vector<std::pair<std::string, std::string>>& symmetryCandidates) {
    for (Kernel::Literal* literal : parent->iterLits()) {
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
    if (!appendCertificateSplitLiteralsJson(parent, literals)) {
      return false;
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };

  std::vector<std::string> actual;
  if (!normalizedClause(child, actual)) {
    return false;
  }

  auto matchTerm = [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, std::map<unsigned, Kernel::TermList>& bindings) -> bool {
    if (pattern.isVar()) {
      auto existing = bindings.find(pattern.var());
      if (existing == bindings.end()) {
        bindings.emplace(pattern.var(), target);
        return true;
      }
      return existing->second == target;
    }
    if (!pattern.isTerm() || !target.isTerm()) {
      return pattern == target;
    }
    Kernel::Term* patternTerm = pattern.term();
    Kernel::Term* targetTerm = target.term();
    if (patternTerm->functor() != targetTerm->functor()
      || patternTerm->arity() != targetTerm->arity()) {
      return false;
    }
    for (unsigned index = 0; index < patternTerm->arity(); ++index) {
      if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), bindings)) {
        return false;
      }
    }
    return true;
  };
  auto matchLiteralOriented = [&](Kernel::Literal* pattern, Kernel::Literal* target, bool reverseEquality, std::map<unsigned, Kernel::TermList>& bindings) {
    if (pattern->polarity() != target->polarity()) {
      return false;
    }
    if (pattern->isEquality() != target->isEquality()) {
      return false;
    }
    if (pattern->isEquality()) {
      if (!matchTerm(matchTerm,
          Kernel::SortHelper::getEqualityArgumentSort(pattern),
          Kernel::SortHelper::getEqualityArgumentSort(target),
          bindings)) {
        return false;
      }
      Kernel::TermList targetLeft = *target->nthArgument(reverseEquality ? 1 : 0);
      Kernel::TermList targetRight = *target->nthArgument(reverseEquality ? 0 : 1);
      return matchTerm(matchTerm, *pattern->nthArgument(0), targetLeft, bindings)
        && matchTerm(matchTerm, *pattern->nthArgument(1), targetRight, bindings);
    }
    if (pattern->functor() != target->functor()
      || pattern->arity() != target->arity()) {
      return false;
    }
    for (unsigned index = 0; index < pattern->arity(); ++index) {
      if (!matchTerm(matchTerm, *pattern->nthArgument(index), *target->nthArgument(index), bindings)) {
        return false;
      }
    }
    return true;
  };
  auto matchLiteral = [&](Kernel::Literal* pattern, Kernel::Literal* target, std::map<unsigned, Kernel::TermList>& bindings) {
    std::map<unsigned, Kernel::TermList> trial = bindings;
    if (matchLiteralOriented(pattern, target, false, trial)) {
      bindings = std::move(trial);
      return true;
    }
    if (pattern->isEquality()) {
      trial = bindings;
      if (matchLiteralOriented(pattern, target, true, trial)) {
        bindings = std::move(trial);
        return true;
      }
    }
    return false;
  };

  for (unsigned omitted = 0; omitted < parent->length(); ++omitted) {
    std::vector<Kernel::Literal*> baseLiterals;
    baseLiterals.reserve(parent->length() - 1);

    for (unsigned parentIndex = 0; parentIndex < parent->length(); ++parentIndex) {
      if (parentIndex == omitted) {
        continue;
      }
      Kernel::Literal* literal = (*parent)[parentIndex];
      baseLiterals.push_back(literal);
    }

    std::function<bool(std::size_t, std::map<unsigned, Kernel::TermList>&)> matchRest =
      [&](std::size_t baseIndex, std::map<unsigned, Kernel::TermList>& bindings) {
        if (baseIndex == baseLiterals.size()) {
          return true;
        }
        Kernel::Literal* pattern = baseLiterals[baseIndex];
        for (Kernel::Literal* target : child->iterLits()) {
          std::map<unsigned, Kernel::TermList> trial = bindings;
          if (!matchLiteral(pattern, target, trial)) {
            continue;
          }
          if (matchRest(baseIndex + 1, trial)) {
            bindings = std::move(trial);
            return true;
          }
        }
        return false;
      };

    std::map<unsigned, Kernel::TermList> bindings;
    if (!matchRest(0, bindings)) {
      continue;
    }

    Kernel::Substitution substitution;
    for (const auto& binding : bindings) {
      substitution.rebind(binding.first, binding.second);
    }
    std::vector<std::pair<std::string, std::string>> symmetryCandidates;
    std::vector<std::string> normalizedSubstituted;
    if (!substitutedParentLiterals(substitution, normalizedSubstituted, symmetryCandidates)) {
      continue;
    }
    std::vector<std::pair<std::string, std::string>> finalSymmetryFlips;
    std::vector<std::string> currentClause = normalizedSubstituted;
    for (std::size_t guard = 0; currentClause != actual && guard < symmetryCandidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : symmetryCandidates) {
        if (std::find(actual.begin(), actual.end(), candidate.second) == actual.end()) {
          continue;
        }
        auto currentIt = std::find(currentClause.begin(), currentClause.end(), candidate.first);
        if (currentIt == currentClause.end()) {
          continue;
        }
        *currentIt = candidate.second;
        std::sort(currentClause.begin(), currentClause.end());
        currentClause.erase(std::unique(currentClause.begin(), currentClause.end()), currentClause.end());
        finalSymmetryFlips.push_back(candidate);
        changed = true;
        break;
      }
      if (!changed) {
        break;
      }
    }
    if (currentClause != actual) {
      continue;
    }

    std::string substitutionJson;
    std::string substitutedClauseJson;
    std::string conclusionJson;
    if (!certificateSubstitutionJson(substitution, substitutionJson)
      || !certificateSubstitutedClausePreservingEqualityJson(parent, substitution, substitutedClauseJson)
      || !certificateClauseJson(child, conclusionJson)) {
      return false;
    }

    std::string stepBase = "u" + std::to_string(unit->number());
    std::string parentId = "u" + std::to_string(parent->number());
    std::vector<std::string> steps;
    if (substitutionJson != "{}") {
      std::string substituteId = stepBase + "_subst0";
      steps.push_back(
        "{\"id\":" + quote(substituteId) + ","
        "\"rule\":\"substitute\","
        "\"parents\":[" + quote(parentId) + "],"
        "\"substitution\":" + substitutionJson + ","
        "\"clause\":" + substitutedClauseJson + "}");
      parentId = substituteId;
    }
    currentClause = normalizedSubstituted;
    for (std::size_t index = 0; index < finalSymmetryFlips.size(); ++index) {
      const auto& flip = finalSymmetryFlips[index];
      auto currentIt = std::find(currentClause.begin(), currentClause.end(), flip.first);
      if (currentIt == currentClause.end()) {
        return false;
      }
      *currentIt = flip.second;
      std::sort(currentClause.begin(), currentClause.end());
      currentClause.erase(std::unique(currentClause.begin(), currentClause.end()), currentClause.end());
      std::string symmetryStepId = stepBase + "_symmetry" + std::to_string(index);
      steps.push_back(
        "{\"id\":" + quote(symmetryStepId) + ","
        "\"rule\":\"equality_symmetry\","
        "\"parents\":[" + quote(parentId) + "],"
        "\"literal\":" + flip.first + ","
        "\"clause\":" + jsonArray(currentClause) + "}");
      parentId = symmetryStepId;
    }
    steps.push_back(
      "{\"id\":" + quote(stepBase) + ","
      "\"rule\":\"factor\","
      "\"parents\":[" + quote(parentId) + "],"
      "\"clause\":" + conclusionJson + "}");
    result = jsonArray(steps);
    return true;
  }

  return false;
}

bool MegalodonChecker::certificateAvatarRefutationStepJson(Kernel::Unit* unit, std::string& result)
{
  const Kernel::InferenceRule& rule = unit->inference().rule();
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::AVATAR_REFUTATION
      && rule != Kernel::InferenceRule::AVATAR_REFUTATION_SMT
    )
    || unit->asClause()->length() != 0) {
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

  std::vector<std::string> parentIds;
  std::vector<std::string> satClauses;
  auto appendSatClause = [&](SAT::SATClause* clause) {
    std::vector<std::string> literals;
    for (SATLiteral literal : clause->iter()) {
      std::ostringstream lit;
      lit << "{\"var\":" << literal.var()
          << ",\"polarity\":" << (literal.positive() ? "true" : "false")
          << "}";
      literals.push_back(lit.str());
    }
    satClauses.push_back(jsonArray(literals));
  };

  if (SAT::SATClause* refutation = unit->inference().satPremise()) {
    SAT::SATInference::visitFOConversions(refutation, [&](SAT::SATClause* clause) {
      Kernel::Unit* origin = clause->inference()->foConversion()->getOrigin();
      parentIds.push_back(quote("u" + std::to_string(origin->number())));
      appendSatClause(clause);
    });
  }

  if (parentIds.empty()) {
    for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
      const auto* extra = env.proofExtra.find(parent);
      if (extra == nullptr) {
        continue;
      }
      const auto* satExtra = static_cast<const Indexing::SATClauseExtra*>(extra);
      if (satExtra->clause == nullptr) {
        continue;
      }
      parentIds.push_back(quote("u" + std::to_string(parent->number())));
      appendSatClause(satExtra->clause);
    }
  }
  if (parentIds.empty()) {
    return false;
  }

  result =
    "{\"rule\":\"avatar_refutation\","
    "\"parents\":" + jsonArray(parentIds) + ","
    "\"sat_clauses\":" + jsonArray(satClauses) + ","
    "\"clause\":[]}";
  return true;
}

bool MegalodonChecker::certificateDefinitionRewriteChainStepJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || (
      unit->inference().rule() != Kernel::InferenceRule::DEFINITION_FOLDING_TWEE
      && unit->inference().rule() != Kernel::InferenceRule::DEFINITION_UNFOLDING
      && unit->inference().rule() != Kernel::InferenceRule::PREDICATE_DEFINITION_UNFOLDING
    )) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.empty() || !parents[0]->isClause()) {
    return false;
  }

  const auto* extra = env.proofExtra.find(unit);
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
  std::function<bool(Kernel::TermList, Kernel::TermList, std::map<unsigned, Kernel::TermList>&)> matchTermPattern =
    [&](Kernel::TermList pattern, Kernel::TermList target, std::map<unsigned, Kernel::TermList>& substitution) -> bool {
      if (pattern.isVar()) {
        auto found = substitution.find(pattern.var());
        if (found == substitution.end()) {
          substitution.emplace(pattern.var(), target);
          return true;
        }
        return found->second == target;
      }
      if (pattern == target) {
        return true;
      }
      if (target.isVar()) {
        return false;
      }
      if (pattern.isApplication() || target.isApplication()) {
        return pattern.isApplication()
          && target.isApplication()
          && matchTermPattern(pattern.lhs(), target.lhs(), substitution)
          && matchTermPattern(pattern.rhs(), target.rhs(), substitution);
      }
      Kernel::Term* patternTerm = pattern.term();
      Kernel::Term* targetTerm = target.term();
      if (patternTerm->functor() != targetTerm->functor()
        || patternTerm->arity() != targetTerm->arity()) {
        return false;
      }
      for (unsigned i = 0; i < patternTerm->arity(); ++i) {
        if (!matchTermPattern(*patternTerm->nthArgument(i), *targetTerm->nthArgument(i), substitution)) {
          return false;
        }
      }
      return true;
    };
  std::function<bool(Kernel::TermList, const std::map<unsigned, Kernel::TermList>&, Kernel::TermList&)> instantiateTermPattern =
    [&](Kernel::TermList pattern, const std::map<unsigned, Kernel::TermList>& substitution, Kernel::TermList& result) -> bool {
      if (pattern.isVar()) {
        auto found = substitution.find(pattern.var());
        result = found == substitution.end() ? pattern : found->second;
        return true;
      }
      if (pattern.isApplication()) {
        Kernel::TermList lhs;
        Kernel::TermList rhs;
        if (!instantiateTermPattern(pattern.lhs(), substitution, lhs)
          || !instantiateTermPattern(pattern.rhs(), substitution, rhs)) {
          return false;
        }
        return safeHolApplication(
          *pattern.term()->nthArgument(0),
          *pattern.term()->nthArgument(1),
          lhs,
          rhs,
          result);
      }
      Kernel::Term* patternTerm = pattern.term();
      Stack<Kernel::TermList> args;
      for (unsigned i = 0; i < patternTerm->arity(); ++i) {
        Kernel::TermList arg;
        if (!instantiateTermPattern(*patternTerm->nthArgument(i), substitution, arg)) {
          return false;
        }
        args.push(arg);
      }
      result = pattern.term()->isSort()
        ? Kernel::TermList(Kernel::AtomicSort::create(static_cast<Kernel::AtomicSort*>(patternTerm), args.begin()))
        : Kernel::TermList(Kernel::Term::create(patternTerm, args.begin()));
      return true;
    };
  struct DefinitionRewriteMatch {
    std::vector<unsigned> position;
    std::map<unsigned, Kernel::TermList> substitution;
  };
  auto collectTermPatternMatches = [&](auto&& self, Kernel::TermList term, Kernel::TermList pattern, std::vector<unsigned>& current, std::vector<DefinitionRewriteMatch>& matches) -> void {
    std::map<unsigned, Kernel::TermList> substitution;
    if (matchTermPattern(pattern, term, substitution)) {
      matches.push_back({current, substitution});
    }
    if (term.isVar()) {
      return;
    }
    if (term.isApplication()) {
      current.push_back(0);
      self(self, term.lhs(), pattern, current, matches);
      current.pop_back();
      current.push_back(1);
      self(self, term.rhs(), pattern, current, matches);
      current.pop_back();
      return;
    }
    Kernel::Term* termPtr = term.term();
    for (unsigned i = 0; i < termPtr->numTermArguments(); ++i) {
      current.push_back(i);
      self(self, termPtr->termArg(i), pattern, current, matches);
      current.pop_back();
    }
  };
  std::function<bool(Kernel::TermList, const std::vector<unsigned>&, std::size_t, Kernel::TermList, Kernel::TermList&)> replaceTermAtPosition =
    [&](Kernel::TermList term, const std::vector<unsigned>& position, std::size_t depth, Kernel::TermList replacement, Kernel::TermList& result) -> bool {
      if (depth == position.size()) {
        result = replacement;
        return true;
      }
      if (term.isVar()) {
        return false;
      }
      unsigned childIndex = position[depth];
      if (term.isApplication()) {
        Kernel::TermList lhs = term.lhs();
        Kernel::TermList rhs = term.rhs();
        Kernel::TermList rewritten;
        if (childIndex == 0) {
          if (!replaceTermAtPosition(lhs, position, depth + 1, replacement, rewritten)) {
            return false;
          }
          return safeHolApplication(
            *term.term()->nthArgument(0),
            *term.term()->nthArgument(1),
            rewritten,
            rhs,
            result);
        }
        if (childIndex == 1) {
          if (!replaceTermAtPosition(rhs, position, depth + 1, replacement, rewritten)) {
            return false;
          }
          return safeHolApplication(
            *term.term()->nthArgument(0),
            *term.term()->nthArgument(1),
            lhs,
            rewritten,
            result);
        }
        return false;
      }
      Kernel::Term* termPtr = term.term();
      if (childIndex >= termPtr->numTermArguments()) {
        return false;
      }
      Stack<Kernel::TermList> args;
      for (unsigned i = 0; i < termPtr->arity(); ++i) {
        args.push(*termPtr->nthArgument(i));
      }
      Kernel::TermList rewritten;
      unsigned argumentIndex = termPtr->numTypeArguments() + childIndex;
      if (!replaceTermAtPosition(args[argumentIndex], position, depth + 1, replacement, rewritten)) {
        return false;
      }
      args[argumentIndex] = rewritten;
      result = term.term()->isSort()
        ? Kernel::TermList(Kernel::AtomicSort::create(static_cast<Kernel::AtomicSort*>(termPtr), args.begin()))
        : Kernel::TermList(Kernel::Term::create(termPtr, args.begin()));
      return true;
    };
  auto rewriteLiteralAtPosition = [&](Kernel::Literal* literal, const std::vector<unsigned>& position, Kernel::TermList replacement, Kernel::Literal*& rewritten) {
    if (position.empty() || position[0] >= literal->arity()) {
      return false;
    }
    Stack<Kernel::TermList> args;
    for (unsigned i = 0; i < literal->arity(); ++i) {
      args.push(*literal->nthArgument(i));
    }
    Kernel::TermList rewrittenArgument;
    std::vector<unsigned> argumentPosition(position.begin() + 1, position.end());
    if (!replaceTermAtPosition(args[position[0]], argumentPosition, 0, replacement, rewrittenArgument)) {
      return false;
    }
    args[position[0]] = rewrittenArgument;
    rewritten = Kernel::Literal::create(literal, args.begin());
    return true;
  };
  auto appendEqualityDefinitionRewrite = [&](Kernel::Clause* definitionParent, std::size_t parentIndex, std::vector<std::string>& rewrites) {
    for (Kernel::Literal* literal : definitionParent->iterLits()) {
      if (!literal->isEquality() || !literal->isPositive() || literal->arity() != 2) {
        continue;
      }
      std::string from;
      std::string to;
      if (!certificateTermJson(*literal->nthArgument(0), from)
        || !certificateTermJson(*literal->nthArgument(1), to)) {
        return false;
      }
      rewrites.push_back(
        "{\"from\":" + from
        + ",\"to\":" + to
        + ",\"parent\":" + quote("u" + std::to_string(parents[parentIndex]->number()))
        + "}");
      return true;
    }
    return false;
  };
  auto appendPositionedEqualityDefinitionRewrite =
    [&](Kernel::Clause* definitionParent, std::size_t parentIndex, std::vector<Kernel::Literal*>& currentClause, std::vector<std::string>& rewrites) {
      for (Kernel::Literal* literal : definitionParent->iterLits()) {
        if (!literal->isEquality() || !literal->isPositive() || literal->arity() != 2) {
          continue;
        }
        Kernel::TermList fromTerm = *literal->nthArgument(0);
        Kernel::TermList toTerm = *literal->nthArgument(1);
        for (std::size_t literalIndex = 0; literalIndex < currentClause.size(); ++literalIndex) {
          Kernel::Literal* current = currentClause[literalIndex];
          for (unsigned argumentIndex = 0; argumentIndex < current->arity(); ++argumentIndex) {
            std::vector<unsigned> prefix;
            prefix.push_back(argumentIndex);
            std::vector<DefinitionRewriteMatch> matches;
            collectTermPatternMatches(collectTermPatternMatches, *current->nthArgument(argumentIndex), fromTerm, prefix, matches);
            if (matches.empty()) {
              continue;
            }
            const DefinitionRewriteMatch& match = matches.front();
            Kernel::TermList instantiatedFrom;
            Kernel::TermList instantiatedTo;
            if (!instantiateTermPattern(fromTerm, match.substitution, instantiatedFrom)
              || !instantiateTermPattern(toTerm, match.substitution, instantiatedTo)) {
              return false;
            }
            Kernel::Literal* rewrittenLiteral = nullptr;
            if (!rewriteLiteralAtPosition(current, match.position, instantiatedTo, rewrittenLiteral)) {
              return false;
            }
            std::string from;
            std::string to;
            if (!certificateTermJson(instantiatedFrom, from) || !certificateTermJson(instantiatedTo, to)) {
              return false;
            }
            currentClause[literalIndex] = rewrittenLiteral;
            std::vector<std::string> intermediateLiterals;
            for (Kernel::Literal* intermediateLiteral : currentClause) {
              std::string intermediateLiteralJson;
              if (!certificateLiteralJson(intermediateLiteral, intermediateLiteralJson)) {
                return false;
              }
              intermediateLiterals.push_back(intermediateLiteralJson);
            }
            rewrites.push_back(
              "{\"from\":" + from
              + ",\"to\":" + to
              + ",\"parent\":" + quote("u" + std::to_string(parents[parentIndex]->number()))
              + ",\"literal\":" + std::to_string(literalIndex)
              + ",\"position\":" + positionJson(match.position)
              + ",\"clause\":" + jsonArray(intermediateLiterals)
              + "}");
            return true;
          }
        }
        return false;
      }
      return false;
    };

  std::vector<std::string> parentIds;
  for (Kernel::Unit* parent : parents) {
    parentIds.push_back(quote("u" + std::to_string(parent->number())));
  }

  std::vector<std::string> rewrites;
  if (unit->inference().rule() == Kernel::InferenceRule::DEFINITION_FOLDING_TWEE) {
    if (extra == nullptr) {
      return false;
    }
    const auto* foldingExtra = static_cast<const TweeDefinitionFoldingExtra*>(extra);
    if (foldingExtra->steps.empty()) {
      return false;
    }
    for (std::size_t stepIndex = 0; stepIndex < foldingExtra->steps.size(); ++stepIndex) {
      const auto& step = foldingExtra->steps[stepIndex];
      std::string lhs;
      std::string rhs;
      if (!certificateTermJson(step.from, lhs) || !certificateTermJson(step.to, rhs)) {
        return false;
      }
      std::ostringstream position;
      position << '[';
      for (std::size_t positionIndex = 0; positionIndex < step.position.size(); ++positionIndex) {
        if (positionIndex) {
          position << ',';
        }
        position << step.position[positionIndex];
      }
      position << ']';
      std::string parentField;
      if (parents.size() == foldingExtra->steps.size() + 1) {
        std::size_t parentIndex = parents.size() - 1 - stepIndex;
        parentField = ",\"parent\":" + quote("u" + std::to_string(parents[parentIndex]->number()));
      }
      rewrites.push_back(
        "{\"from\":" + lhs
        + ",\"to\":" + rhs
        + parentField
        + ",\"literal\":" + std::to_string(step.literal)
        + ",\"position\":" + position.str()
        + "}");
    }
  } else {
    std::vector<Kernel::Literal*> currentClause;
    for (Kernel::Literal* literal : parents[0]->asClause()->iterLits()) {
      currentClause.push_back(literal);
    }
    for (std::size_t parentIndex = 1; parentIndex < parents.size(); ++parentIndex) {
      if (!parents[parentIndex]->isClause()
        || !appendPositionedEqualityDefinitionRewrite(parents[parentIndex]->asClause(), parentIndex, currentClause, rewrites)) {
        rewrites.clear();
        for (std::size_t fallbackParentIndex = 1; fallbackParentIndex < parents.size(); ++fallbackParentIndex) {
          if (!parents[fallbackParentIndex]->isClause()
            || !appendEqualityDefinitionRewrite(parents[fallbackParentIndex]->asClause(), fallbackParentIndex, rewrites)) {
            return false;
          }
        }
        break;
      }
    }
    if (!rewrites.empty() && rewrites.size() == parents.size() - 1) {
      std::vector<std::string> expectedLiterals;
      for (Kernel::Literal* literal : currentClause) {
        std::string literalJson;
        if (!certificateLiteralJson(literal, literalJson)) {
          return false;
        }
        expectedLiterals.push_back(literalJson);
      }
      std::vector<std::string> actualLiterals;
      for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
        std::string literalJson;
        if (!certificateLiteralJson(literal, literalJson)) {
          return false;
        }
        actualLiterals.push_back(literalJson);
      }
      std::sort(expectedLiterals.begin(), expectedLiterals.end());
      expectedLiterals.erase(std::unique(expectedLiterals.begin(), expectedLiterals.end()), expectedLiterals.end());
      std::sort(actualLiterals.begin(), actualLiterals.end());
      actualLiterals.erase(std::unique(actualLiterals.begin(), actualLiterals.end()), actualLiterals.end());
      if (expectedLiterals != actualLiterals) {
        rewrites.clear();
        for (std::size_t fallbackParentIndex = 1; fallbackParentIndex < parents.size(); ++fallbackParentIndex) {
          if (!parents[fallbackParentIndex]->isClause()
            || !appendEqualityDefinitionRewrite(parents[fallbackParentIndex]->asClause(), fallbackParentIndex, rewrites)) {
            return false;
          }
        }
      }
    }
  }
  if (rewrites.empty()) {
    return false;
  }

  std::string sourceClause;
  std::string conclusionClause;
  if (!certificateClauseJson(parents[0]->asClause(), sourceClause)
    || !certificateClauseJson(unit->asClause(), conclusionClause)) {
    return false;
  }

  result =
    "{\"rule\":\"definition_rewrite_chain\","
    "\"parents\":" + jsonArray(parentIds) + ","
    "\"source_clause\":" + sourceClause + ","
    "\"rewrites\":" + jsonArray(rewrites) + ","
    "\"clause\":" + conclusionClause + "}";
  return true;
}

bool MegalodonChecker::certificateBoolSimplificationStepJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause() || unit->inference().rule() != Kernel::InferenceRule::BOOL_SIMP) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.size() != 1 || !parents[0]->isClause()) {
    return false;
  }

  Kernel::Clause* sourceClause = parents[0]->asClause();
  Kernel::Clause* targetClause = unit->asClause();
  if (sourceClause->length() != targetClause->length()) {
    return false;
  }

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

  auto sameApplicationSpine = [](Kernel::TermList source, Kernel::TermList target) {
    if (!source.isApplication() || !target.isApplication()) {
      return false;
    }
    Kernel::TermStack sourceArgs;
    Kernel::TermStack targetArgs;
    Kernel::TermList sourceHead = HOL::getHeadAndArgs(source, sourceArgs);
    Kernel::TermList targetHead = HOL::getHeadAndArgs(target, targetArgs);
    return sourceHead == targetHead && sourceArgs.size() == targetArgs.size();
  };
  std::function<bool(Kernel::TermList, Kernel::TermList, std::vector<unsigned>&, Kernel::TermList&, Kernel::TermList&)> termDiff =
    [&](Kernel::TermList source, Kernel::TermList target, std::vector<unsigned>& position, Kernel::TermList& from, Kernel::TermList& to) -> bool {
      if (source == target) {
        return false;
      }
      if (source.isVar()) {
        return false;
      }
      if (source.isApplication() || target.isApplication()) {
        if (!source.isApplication() || !target.isApplication() || !sameApplicationSpine(source, target)) {
          if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
            from = source;
            to = target;
            return true;
          }
          return false;
        }
        std::vector<unsigned> lhsPosition;
        Kernel::TermList lhsFrom;
        Kernel::TermList lhsTo;
        if (termDiff(source.lhs(), target.lhs(), lhsPosition, lhsFrom, lhsTo)) {
          position.push_back(0);
          position.insert(position.end(), lhsPosition.begin(), lhsPosition.end());
          from = lhsFrom;
          to = lhsTo;
          return true;
        }
        std::vector<unsigned> rhsPosition;
        Kernel::TermList rhsFrom;
        Kernel::TermList rhsTo;
        if (termDiff(source.rhs(), target.rhs(), rhsPosition, rhsFrom, rhsTo)) {
          position.push_back(1);
          position.insert(position.end(), rhsPosition.begin(), rhsPosition.end());
          from = rhsFrom;
          to = rhsTo;
          return true;
        }
        if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
          from = source;
          to = target;
          return true;
        }
        return false;
      }
      if (target.isVar()) {
        if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
          from = source;
          to = target;
          return true;
        }
        return false;
      }
      Kernel::Term* sourceTerm = source.term();
      Kernel::Term* targetTerm = target.term();
      if (sourceTerm->functor() != targetTerm->functor()
        || sourceTerm->arity() != targetTerm->arity()) {
        if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
          from = source;
          to = target;
          return true;
        }
        return false;
      }
      bool found = false;
      for (unsigned i = 0; i < sourceTerm->numTermArguments(); ++i) {
        std::vector<unsigned> childPosition;
        Kernel::TermList childFrom;
        Kernel::TermList childTo;
        if (!termDiff(sourceTerm->termArg(i), targetTerm->termArg(i), childPosition, childFrom, childTo)) {
          continue;
        }
        if (found) {
          return false;
        }
        found = true;
        position.push_back(i);
        position.insert(position.end(), childPosition.begin(), childPosition.end());
        from = childFrom;
        to = childTo;
      }
      if (found) {
        return true;
      }
      if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
        from = source;
        to = target;
        return true;
      }
      return false;
    };

  std::size_t changedLiteral = sourceClause->length();
  std::vector<unsigned> position;
  Kernel::TermList from;
  Kernel::TermList to;
  for (unsigned literalIndex = 0; literalIndex < sourceClause->length(); ++literalIndex) {
    Kernel::Literal* sourceLiteral = (*sourceClause)[literalIndex];
    Kernel::Literal* targetLiteral = (*targetClause)[literalIndex];
    std::string sourceJson;
    std::string targetJson;
    if (!certificateLiteralJson(sourceLiteral, sourceJson) || !certificateLiteralJson(targetLiteral, targetJson)) {
      return false;
    }
    if (sourceJson == targetJson) {
      continue;
    }
    if (changedLiteral != sourceClause->length()
      || sourceLiteral->functor() != targetLiteral->functor()
      || sourceLiteral->arity() != targetLiteral->arity()
      || sourceLiteral->polarity() != targetLiteral->polarity()) {
      return false;
    }
    bool found = false;
    for (unsigned argumentIndex = 0; argumentIndex < sourceLiteral->arity(); ++argumentIndex) {
      std::vector<unsigned> argumentPosition;
      Kernel::TermList argumentFrom;
      Kernel::TermList argumentTo;
      if (!termDiff(*sourceLiteral->nthArgument(argumentIndex), *targetLiteral->nthArgument(argumentIndex), argumentPosition, argumentFrom, argumentTo)) {
        continue;
      }
      if (found) {
        return false;
      }
      found = true;
      position.push_back(argumentIndex);
      position.insert(position.end(), argumentPosition.begin(), argumentPosition.end());
      from = argumentFrom;
      to = argumentTo;
    }
    if (!found) {
      return false;
    }
    changedLiteral = literalIndex;
  }
  if (changedLiteral == sourceClause->length()) {
    return false;
  }

  std::string fromJson;
  std::string toJson;
  std::string targetJson;
  std::string rewrittenTargetJson;
  std::string clauseJson;
  if (!certificateTermJson(from, fromJson)
    || !certificateTermJson(to, toJson)
    || !certificateLiteralJson((*sourceClause)[changedLiteral], targetJson)
    || !certificateLiteralJson((*targetClause)[changedLiteral], rewrittenTargetJson)
    || !certificateClauseJson(targetClause, clauseJson)) {
    return false;
  }

  result =
    "{\"rule\":\"bool_simplify\","
    "\"parents\":[" + quote("u" + std::to_string(parents[0]->number())) + "],"
    "\"from\":" + fromJson + ","
    "\"to\":" + toJson + ","
    "\"target\":" + targetJson + ","
    "\"rewritten_target\":" + rewrittenTargetJson + ","
    "\"literal\":" + std::to_string(changedLiteral) + ","
    "\"position\":" + positionJson(position) + ","
    "\"clause\":" + clauseJson + "}";
  return true;
}

bool MegalodonChecker::certificateBoolSimplificationStepSexpr(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.size() != 1 || !parents[0]->isClause()) {
    return false;
  }

  Kernel::Clause* sourceClause = parents[0]->asClause();
  Kernel::Clause* targetClause = unit->asClause();
  if (sourceClause->length() != targetClause->length()) {
    return false;
  }

  auto sameApplicationSpine = [](Kernel::TermList source, Kernel::TermList target) {
    if (!source.isApplication() || !target.isApplication()) {
      return false;
    }
    Kernel::TermStack sourceArgs;
    Kernel::TermStack targetArgs;
    Kernel::TermList sourceHead = HOL::getHeadAndArgs(source, sourceArgs);
    Kernel::TermList targetHead = HOL::getHeadAndArgs(target, targetArgs);
    return sourceHead == targetHead && sourceArgs.size() == targetArgs.size();
  };
  auto sameRenderedTerm = [&](Kernel::TermList source, Kernel::TermList target) {
    std::string sourceSexpr;
    std::string targetSexpr;
    return certificateTermSexpr(source, sourceSexpr)
      && certificateTermSexpr(target, targetSexpr)
      && sourceSexpr == targetSexpr;
  };

  std::function<bool(Kernel::TermList, Kernel::TermList, std::vector<unsigned>&, Kernel::TermList&, Kernel::TermList&)> termDiff =
    [&](Kernel::TermList source, Kernel::TermList target, std::vector<unsigned>& position, Kernel::TermList& from, Kernel::TermList& to) -> bool {
      if (source == target) {
        return false;
      }
      if (source.isVar()) {
        return false;
      }
      if (source.isApplication() || target.isApplication()) {
        if (!source.isApplication() || !target.isApplication() || !sameApplicationSpine(source, target)) {
          if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
            from = source;
            to = target;
            return true;
          }
          return false;
        }
        std::vector<unsigned> lhsPosition;
        Kernel::TermList lhsFrom;
        Kernel::TermList lhsTo;
        if (termDiff(source.lhs(), target.lhs(), lhsPosition, lhsFrom, lhsTo)) {
          position.push_back(0);
          position.insert(position.end(), lhsPosition.begin(), lhsPosition.end());
          from = lhsFrom;
          to = lhsTo;
          return true;
        }
        std::vector<unsigned> rhsPosition;
        Kernel::TermList rhsFrom;
        Kernel::TermList rhsTo;
        if (termDiff(source.rhs(), target.rhs(), rhsPosition, rhsFrom, rhsTo)) {
          position.push_back(1);
          position.insert(position.end(), rhsPosition.begin(), rhsPosition.end());
          from = rhsFrom;
          to = rhsTo;
          return true;
        }
        if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
          from = source;
          to = target;
          return true;
        }
        return false;
      }
      if (target.isVar()) {
        if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
          from = source;
          to = target;
          return true;
        }
        return false;
      }
      Kernel::Term* sourceTerm = source.term();
      Kernel::Term* targetTerm = target.term();
      if (sourceTerm->functor() != targetTerm->functor()
        || sourceTerm->arity() != targetTerm->arity()) {
        if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
          from = source;
          to = target;
          return true;
        }
        return false;
      }
      bool found = false;
      for (unsigned i = 0; i < sourceTerm->numTermArguments(); ++i) {
        std::vector<unsigned> childPosition;
        Kernel::TermList childFrom;
        Kernel::TermList childTo;
        if (!termDiff(sourceTerm->termArg(i), targetTerm->termArg(i), childPosition, childFrom, childTo)) {
          continue;
        }
        if (found) {
          return false;
        }
        found = true;
        position.push_back(i);
        position.insert(position.end(), childPosition.begin(), childPosition.end());
        from = childFrom;
        to = childTo;
      }
      if (found) {
        return true;
      }
      if (Kernel::SortHelper::getResultSort(source.term()).isBoolSort()) {
        from = source;
        to = target;
        return true;
      }
      return false;
    };

  std::size_t changedLiteral = sourceClause->length();
  std::vector<unsigned> position;
  Kernel::TermList from;
  Kernel::TermList to;
  for (unsigned literalIndex = 0; literalIndex < sourceClause->length(); ++literalIndex) {
    Kernel::Literal* sourceLiteral = (*sourceClause)[literalIndex];
    Kernel::Literal* targetLiteral = (*targetClause)[literalIndex];
    std::string sourceSexpr;
    std::string targetSexpr;
    if (!certificateLiteralSexpr(sourceLiteral, sourceSexpr) || !certificateLiteralSexpr(targetLiteral, targetSexpr)) {
      return false;
    }
    if (sourceSexpr == targetSexpr) {
      continue;
    }
    if (changedLiteral != sourceClause->length()) {
      return false;
    }
    Kernel::Literal* sourcePositive = sourceLiteral->isPositive()
      ? sourceLiteral
      : Kernel::Literal::complementaryLiteral(sourceLiteral);
    Kernel::Literal* targetPositive = targetLiteral->isPositive()
      ? targetLiteral
      : Kernel::Literal::complementaryLiteral(targetLiteral);
    if (sourceLiteral->polarity() == targetLiteral->polarity()
      && sourcePositive->isEquality()
      && targetPositive->isEquality()
      && sourcePositive->arity() == 2
      && targetPositive->arity() == 2) {
      int swappedChangedSide = -1;
      std::vector<unsigned> swappedPosition;
      Kernel::TermList swappedFrom;
      Kernel::TermList swappedTo;
      bool swappedMatch = true;
      for (unsigned sourceSide = 0; sourceSide < 2; ++sourceSide) {
        unsigned targetSide = 1 - sourceSide;
        Kernel::TermList sourceTerm = *sourcePositive->nthArgument(sourceSide);
        Kernel::TermList targetTerm = *targetPositive->nthArgument(targetSide);
        if (sameRenderedTerm(sourceTerm, targetTerm)) {
          continue;
        }
        std::vector<unsigned> sidePosition;
        Kernel::TermList sideFrom;
        Kernel::TermList sideTo;
        if (swappedChangedSide != -1 || !termDiff(sourceTerm, targetTerm, sidePosition, sideFrom, sideTo)) {
          swappedMatch = false;
          break;
        }
        swappedChangedSide = static_cast<int>(sourceSide);
        swappedPosition.push_back(sourceSide);
        swappedPosition.insert(swappedPosition.end(), sidePosition.begin(), sidePosition.end());
        swappedFrom = sideFrom;
        swappedTo = sideTo;
      }
      if (swappedMatch && swappedChangedSide != -1) {
        Kernel::TermList intermediateLeft = swappedChangedSide == 0
          ? *targetPositive->nthArgument(1)
          : *sourcePositive->nthArgument(0);
        Kernel::TermList intermediateRight = swappedChangedSide == 1
          ? *targetPositive->nthArgument(0)
          : *sourcePositive->nthArgument(1);
        Kernel::Literal* intermediateLiteral = Kernel::Literal::createEquality(
          sourceLiteral->isPositive(),
          intermediateLeft,
          intermediateRight,
          Kernel::SortHelper::getEqualityArgumentSort(sourcePositive));

        std::ostringstream intermediateClause;
        intermediateClause << "(clause";
        for (unsigned i = 0; i < sourceClause->length(); ++i) {
          std::string renderedLiteral;
          if (!certificateLiteralSexpr(i == literalIndex ? intermediateLiteral : (*sourceClause)[i], renderedLiteral)) {
            return false;
          }
          intermediateClause << ' ' << renderedLiteral;
        }
        intermediateClause << ')';

        std::string fromSexpr;
        std::string toSexpr;
        std::string targetClauseSexpr;
        if (!certificateTermSexpr(swappedFrom, fromSexpr)
          || !certificateTermSexpr(swappedTo, toSexpr)
          || !certificateClauseSexpr(targetClause, targetClauseSexpr)) {
          return false;
        }

        std::string intermediateId = "u" + std::to_string(unit->number()) + "_bool_simplify0";
        std::string stepId = intermediateClause.str() == targetClauseSexpr
          ? "u" + std::to_string(unit->number())
          : intermediateId;
        result =
          "  (bool_simplify \"" + stepId
          + "\" (parent \"u" + std::to_string(parents[0]->number()) + "\")"
          + " (literal " + std::to_string(literalIndex) + ") "
          + certificatePositionSexpr(swappedPosition)
          + " (from " + fromSexpr + ")"
          + " (to " + toSexpr + ")"
          + " (result " + intermediateClause.str() + "))";
        if (stepId == intermediateId) {
          result +=
            "\n  (equality_symmetry \"u" + std::to_string(unit->number())
            + "\" (parent \"" + intermediateId + "\")"
            + " (literal " + std::to_string(literalIndex) + ")"
            + " (result " + targetClauseSexpr + "))";
        }
        return true;
      }
    }
    if (sourceLiteral->functor() != targetLiteral->functor()
      || sourceLiteral->arity() != targetLiteral->arity()
      || sourceLiteral->polarity() != targetLiteral->polarity()) {
      return false;
    }
    bool found = false;
    for (unsigned argumentIndex = 0; argumentIndex < sourceLiteral->arity(); ++argumentIndex) {
      std::vector<unsigned> argumentPosition;
      Kernel::TermList argumentFrom;
      Kernel::TermList argumentTo;
      if (!termDiff(*sourceLiteral->nthArgument(argumentIndex), *targetLiteral->nthArgument(argumentIndex), argumentPosition, argumentFrom, argumentTo)) {
        continue;
      }
      if (found) {
        return false;
      }
      found = true;
      position.push_back(argumentIndex);
      position.insert(position.end(), argumentPosition.begin(), argumentPosition.end());
      from = argumentFrom;
      to = argumentTo;
    }
    if (!found) {
      return false;
    }
    changedLiteral = literalIndex;
  }
  if (changedLiteral == sourceClause->length()) {
    return false;
  }

  std::string fromSexpr;
  std::string toSexpr;
  std::string resultClause;
  if (!certificateTermSexpr(from, fromSexpr)
    || !certificateTermSexpr(to, toSexpr)
    || !certificateClauseSexpr(targetClause, resultClause)) {
    return false;
  }

  result =
    "  (bool_simplify \"u" + std::to_string(unit->number())
    + "\" (parent \"u" + std::to_string(parents[0]->number()) + "\")"
    + " (literal " + std::to_string(changedLiteral) + ") "
    + certificatePositionSexpr(position)
    + " (from " + fromSexpr + ")"
    + " (to " + toSexpr + ")"
    + " (result " + resultClause + "))";
  return true;
}

bool MegalodonChecker::certificateInequalitySplittingStepJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::INEQUALITY_SPLITTING) {
    return false;
  }

  std::vector<Kernel::Unit*> parents;
  for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
    parents.push_back(parent);
  }
  if (parents.size() < 2 || !parents[0]->isClause()) {
    return false;
  }
  for (std::size_t i = 1; i < parents.size(); ++i) {
    if (!parents[i]->isClause()
      || parents[i]->inference().rule() != Kernel::InferenceRule::INEQUALITY_SPLITTING_NAME_INTRODUCTION
      || parents[i]->asClause()->length() != 1) {
      return false;
    }
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
  auto isFoolConstant = [](Kernel::TermList term, bool value) {
    return term.isTerm()
      && !term.term()->isSpecial()
      && env.signature->isFoolConstantSymbol(value, term.term()->functor());
  };
  auto boolNameLiteralTerm = [&](Kernel::Literal* literal, bool value, Kernel::TermList& namedTerm) {
    if (literal == nullptr
      || !literal->isEquality()
      || !literal->isPositive()
      || Kernel::SortHelper::getEqualityArgumentSort(literal) != Kernel::AtomicSort::boolSort()) {
      return false;
    }
    Kernel::TermList left = *literal->nthArgument(0);
    Kernel::TermList right = *literal->nthArgument(1);
    if (isFoolConstant(left, value)) {
      namedTerm = right;
      return true;
    }
    if (isFoolConstant(right, value)) {
      namedTerm = left;
      return true;
    }
    return false;
  };
  auto applicationHeadAndArg = [](Kernel::TermList term, Kernel::TermList& head, Kernel::TermList& arg) {
    if (!term.isApplication()) {
      return false;
    }
    head = term.lhs();
    arg = term.rhs();
    return true;
  };
  auto replacementInConclusion = [&](Kernel::TermList head, Kernel::TermList argument, Kernel::Literal*& replacement) {
    for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
      Kernel::TermList namedTerm;
      Kernel::TermList candidateHead;
      Kernel::TermList candidateArg;
      if (boolNameLiteralTerm(literal, true, namedTerm)
        && applicationHeadAndArg(namedTerm, candidateHead, candidateArg)
        && candidateHead == head
        && candidateArg == argument) {
        replacement = literal;
        return true;
      }
    }
    return false;
  };

  Kernel::Clause* sourceClause = parents[0]->asClause();
  std::set<Kernel::Literal*> usedSourceLiterals;
  std::set<Kernel::Literal*> usedReplacementLiterals;
  std::vector<std::string> splitItems;
  for (std::size_t parentIndex = 1; parentIndex < parents.size(); ++parentIndex) {
    Kernel::Literal* nameLiteral = (*parents[parentIndex]->asClause())[0];
    Kernel::TermList namedTerm;
    Kernel::TermList nameHead;
    Kernel::TermList splitTerm;
    if (!boolNameLiteralTerm(nameLiteral, false, namedTerm)
      || !applicationHeadAndArg(namedTerm, nameHead, splitTerm)) {
      return false;
    }

    Kernel::Literal* selected = nullptr;
    Kernel::Literal* replacement = nullptr;
    for (Kernel::Literal* sourceLiteral : sourceClause->iterLits()) {
      if (usedSourceLiterals.find(sourceLiteral) != usedSourceLiterals.end()
        || !sourceLiteral->isEquality()
        || sourceLiteral->isPositive()) {
        continue;
      }
      Kernel::TermList left = *sourceLiteral->nthArgument(0);
      Kernel::TermList right = *sourceLiteral->nthArgument(1);
      Kernel::TermList otherSide;
      if (left == splitTerm) {
        otherSide = right;
      } else if (right == splitTerm) {
        otherSide = left;
      } else {
        continue;
      }
      Kernel::Literal* candidateReplacement = nullptr;
      if (!replacementInConclusion(nameHead, otherSide, candidateReplacement)
        || usedReplacementLiterals.find(candidateReplacement) != usedReplacementLiterals.end()) {
        continue;
      }
      selected = sourceLiteral;
      replacement = candidateReplacement;
      break;
    }
    if (selected == nullptr || replacement == nullptr) {
      return false;
    }
    usedSourceLiterals.insert(selected);
    usedReplacementLiterals.insert(replacement);

    std::string selectedJson;
    std::string nameLiteralJson;
    std::string replacementJson;
    if (!certificateLiteralJson(selected, selectedJson)
      || !certificateLiteralJson(nameLiteral, nameLiteralJson)
      || !certificateLiteralJson(replacement, replacementJson)) {
      return false;
    }
    splitItems.push_back(
      "{\"name_parent\":" + quote("u" + std::to_string(parents[parentIndex]->number())) + ","
      "\"source\":" + selectedJson + ","
      "\"name_literal\":" + nameLiteralJson + ","
      "\"replacement\":" + replacementJson + "}");
  }

  std::vector<std::string> expectedLiterals;
  for (Kernel::Literal* literal : sourceClause->iterLits()) {
    if (usedSourceLiterals.find(literal) != usedSourceLiterals.end()) {
      continue;
    }
    std::string literalJson;
    if (!certificateLiteralJson(literal, literalJson)) {
      return false;
    }
    expectedLiterals.push_back(literalJson);
  }
  for (Kernel::Literal* literal : usedReplacementLiterals) {
    std::string literalJson;
    if (!certificateLiteralJson(literal, literalJson)) {
      return false;
    }
    expectedLiterals.push_back(literalJson);
  }
  std::sort(expectedLiterals.begin(), expectedLiterals.end());
  expectedLiterals.erase(std::unique(expectedLiterals.begin(), expectedLiterals.end()), expectedLiterals.end());
  std::vector<std::string> actualLiterals;
  for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
    std::string literalJson;
    if (!certificateLiteralJson(literal, literalJson)) {
      return false;
    }
    actualLiterals.push_back(literalJson);
  }
  std::sort(actualLiterals.begin(), actualLiterals.end());
  actualLiterals.erase(std::unique(actualLiterals.begin(), actualLiterals.end()), actualLiterals.end());
  if (expectedLiterals != actualLiterals) {
    return false;
  }

  std::vector<std::string> parentIds;
  for (Kernel::Unit* parent : parents) {
    parentIds.push_back(quote("u" + std::to_string(parent->number())));
  }
  std::string sourceClauseJson;
  std::string conclusionClauseJson;
  if (!certificateClauseJson(sourceClause, sourceClauseJson)
    || !certificateClauseJson(unit->asClause(), conclusionClauseJson)) {
    return false;
  }
  result =
    "{\"rule\":\"inequality_split\","
    "\"parents\":" + jsonArray(parentIds) + ","
    "\"source_clause\":" + sourceClauseJson + ","
    "\"splits\":" + jsonArray(splitItems) + ","
    "\"clause\":" + conclusionClauseJson + "}";
  return true;
}

bool MegalodonChecker::certificateExtensionalityResolutionStepsJson(Kernel::Unit* unit, std::string& result)
{
  if (!unit->isClause()
    || unit->inference().rule() != Kernel::InferenceRule::EXTENSIONALITY_RESOLUTION) {
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
  auto normalize = [](std::vector<std::string>& literals) {
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
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
  struct ExtensionalitySymmetryCandidate {
    bool extParent;
    std::string literal;
    std::string swapped;
  };
  auto appendSubstitutedClauseExcept = [&](
    std::vector<std::string>& literals,
    Kernel::Clause* clause,
    const Kernel::Substitution& substitution,
    Kernel::Literal* excluded,
    bool extParent,
    std::vector<ExtensionalitySymmetryCandidate>& symmetryCandidates) {
    bool skipped = false;
    for (Kernel::Literal* literal : clause->iterLits()) {
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
          symmetryCandidates.push_back({extParent, literalJson, swappedJson});
        }
      }
    }
    return skipped && appendCertificateSplitLiteralsJson(clause, literals);
  };
  auto normalizedActualClause = [&](std::vector<std::string>& literals) {
    for (Kernel::Literal* literal : unit->asClause()->iterLits()) {
      std::string literalJson;
      if (!certificateLiteralJson(literal, literalJson)) {
        return false;
      }
      literals.push_back(literalJson);
    }
    normalize(literals);
    return true;
  };
  auto tryBuildSubstitution = [&](Kernel::Literal* extLiteral, Kernel::Literal* otherLiteral, Kernel::Substitution& extSubstitution) {
    if (!extLiteral->isEquality()
      || !extLiteral->isPositive()
      || !otherLiteral->isEquality()
      || otherLiteral->isPositive()) {
      return false;
    }
    Kernel::TermList extLeft = *extLiteral->nthArgument(0);
    Kernel::TermList extRight = *extLiteral->nthArgument(1);
    if (!extLeft.isVar() || !extRight.isVar()) {
      return false;
    }
    extSubstitution.bind(extLeft.var(), *otherLiteral->nthArgument(0));
    extSubstitution.bind(extRight.var(), *otherLiteral->nthArgument(1));
    return true;
  };

  for (std::size_t extIndex = 0; extIndex < 2; ++extIndex) {
    std::size_t otherIndex = extIndex == 0 ? 1 : 0;
    Kernel::Clause* extParent = parents[extIndex];
    Kernel::Clause* otherParent = parents[otherIndex];
    Kernel::Substitution emptySubstitution;
    for (Kernel::Literal* extLiteral : extParent->iterLits()) {
      for (Kernel::Literal* otherLiteral : otherParent->iterLits()) {
        Kernel::Substitution extSubstitution;
        if (!tryBuildSubstitution(extLiteral, otherLiteral, extSubstitution)) {
          continue;
        }

        std::vector<std::string> expected;
        std::vector<std::string> actual;
        std::vector<ExtensionalitySymmetryCandidate> symmetryCandidates;
        if (!appendSubstitutedClauseExcept(expected, extParent, extSubstitution, extLiteral, true, symmetryCandidates)
          || !appendSubstitutedClauseExcept(expected, otherParent, emptySubstitution, otherLiteral, false, symmetryCandidates)
          || !normalizedActualClause(actual)) {
          continue;
        }
        normalize(expected);
        std::vector<ExtensionalitySymmetryCandidate> finalSymmetryFlips;
        for (std::size_t guard = 0; expected != actual && guard < symmetryCandidates.size(); ++guard) {
          bool changed = false;
          for (const auto& candidate : symmetryCandidates) {
            if (std::find(actual.begin(), actual.end(), candidate.swapped) == actual.end()) {
              continue;
            }
            auto currentIt = std::find(expected.begin(), expected.end(), candidate.literal);
            if (currentIt == expected.end()) {
              continue;
            }
            *currentIt = candidate.swapped;
            normalize(expected);
            finalSymmetryFlips.push_back(candidate);
            changed = true;
            break;
          }
          if (!changed) {
            break;
          }
        }
        if (expected != actual) {
          continue;
        }

        std::string substitutionJson;
        std::string substitutedExtClauseJson;
        std::string pivotJson;
        std::string conclusionJson;
        if (!certificateSubstitutionJson(extSubstitution, substitutionJson)
          || !certificateSubstitutedClausePreservingEqualityJson(extParent, extSubstitution, substitutedExtClauseJson)
          || !certificateSubstitutedLiteralPreservingEqualityJson(extLiteral, extSubstitution, pivotJson)
          || !certificateClauseJson(unit->asClause(), conclusionJson)) {
          return false;
        }

        std::string stepBase = "u" + std::to_string(unit->number());
        std::string extParentId = "u" + std::to_string(extParent->number());
        std::string otherParentId = "u" + std::to_string(otherParent->number());
        std::vector<std::string> steps;
        std::vector<std::string> currentExtClause;
        std::vector<std::string> currentOtherClause;
        if (substitutionJson != "{}") {
          std::string substituteId = stepBase + "_subst_ext";
          steps.push_back(
            "{\"id\":" + quote(substituteId) + ","
            "\"rule\":\"substitute\","
            "\"parents\":[" + quote(extParentId) + "],"
            "\"substitution\":" + substitutionJson + ","
            "\"clause\":" + substitutedExtClauseJson + "}");
          extParentId = substituteId;
        }
        for (Kernel::Literal* literal : extParent->iterLits()) {
          std::string literalJson;
          if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, extSubstitution, literalJson)) {
            return false;
          }
          currentExtClause.push_back(literalJson);
        }
        for (Kernel::Literal* literal : otherParent->iterLits()) {
          std::string literalJson;
          if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, emptySubstitution, literalJson)) {
            return false;
          }
          currentOtherClause.push_back(literalJson);
        }
        normalize(currentExtClause);
        normalize(currentOtherClause);
        std::size_t extSymmetryIndex = 0;
        std::size_t otherSymmetryIndex = 0;
        for (const auto& flip : finalSymmetryFlips) {
          std::vector<std::string>& currentClause = flip.extParent ? currentExtClause : currentOtherClause;
          auto currentIt = std::find(currentClause.begin(), currentClause.end(), flip.literal);
          if (currentIt == currentClause.end()) {
            return false;
          }
          *currentIt = flip.swapped;
          normalize(currentClause);
          std::string symmetryStepId;
          std::string* parentId;
          if (flip.extParent) {
            symmetryStepId = stepBase + "_symmetry_ext" + std::to_string(extSymmetryIndex++);
            parentId = &extParentId;
          } else {
            symmetryStepId = stepBase + "_symmetry_other" + std::to_string(otherSymmetryIndex++);
            parentId = &otherParentId;
          }
          steps.push_back(
            "{\"id\":" + quote(symmetryStepId) + ","
            "\"rule\":\"equality_symmetry\","
            "\"parents\":[" + quote(*parentId) + "],"
            "\"literal\":" + flip.literal + ","
            "\"clause\":" + jsonArray(currentClause) + "}");
          *parentId = symmetryStepId;
        }
        steps.push_back(
          "{\"id\":" + quote(stepBase) + ","
          "\"rule\":\"resolve\","
          "\"parents\":[" + quote(extParentId) + "," + quote(otherParentId) + "],"
          "\"pivot\":" + pivotJson + ","
          "\"clause\":" + conclusionJson + "}");
        result = jsonArray(steps);
        return true;
      }
    }
  }
  return false;
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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
  if (!appendCertificateSplitLiteralsJson(parent, expected)) {
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

bool MegalodonChecker::certificateParamodulateStepJson(
  Kernel::Unit* unit,
  const InferenceRecorder::InferenceInformation*,
  std::string& result)
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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
    return excludedOne && appendCertificateSplitLiteralsJson(clause, literals);
  };
  auto literalIndex = [](Kernel::Clause* clause, Kernel::Literal* literal, unsigned& index) {
    if (literal == nullptr) {
      return false;
    }
    for (unsigned i = 0; i < clause->length(); ++i) {
      if ((*clause)[i] == literal) {
        index = i;
        return true;
      }
    }
    return false;
  };
  auto nativeTopLevelPosition = [](Kernel::Literal* literal, unsigned position, std::string& rendered) {
    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    std::ostringstream out;
    out << '[';
    if (positive->isEquality()) {
      if (position == 0) {
        out << "0,1";
      } else if (position == 1) {
        out << '1';
      } else {
        return false;
      }
    } else {
      if (position >= positive->arity()) {
        return false;
      }
      for (unsigned i = 0; i < positive->arity() - 1 - position; ++i) {
        if (i != 0) {
          out << ',';
        }
        out << '0';
      }
      if (positive->arity() > 1 && position + 1 < positive->arity()) {
        out << ',';
      }
      out << '1';
    }
    out << ']';
    rendered = out.str();
    return true;
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
          unsigned equalityIndex = 0;
          unsigned targetIndex = 0;
          std::string nativePosition;
          if (!literalIndex(equalityParent, equality, equalityIndex)
            || !literalIndex(targetParent, target, targetIndex)
            || !nativeTopLevelPosition(target, position, nativePosition)
            || !certificateLiteralJson(target, targetJson)) {
            continue;
          }
          result = "{\"rule\":\"paramodulate\","
            "\"parents\":["
            + quote("u" + std::to_string(equalityParent->number())) + ","
            + quote("u" + std::to_string(targetParent->number())) + "],"
            "\"equality_index\":" + std::to_string(equalityIndex) + ","
            "\"target_index\":" + std::to_string(targetIndex) + ","
            "\"equality\":" + equalityJson + ","
            "\"from\":" + fromJson + ","
            "\"to\":" + toJson + ","
            "\"target\":" + targetJson + ","
            "\"position\":[" + std::to_string(position) + "],"
            "\"native_position\":" + nativePosition + ","
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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
    return excludedOne && appendCertificateSplitLiteralsJson(clause, literals);
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
  const auto* extra = env.proofExtra.find(unit);
  const auto* rewriteExtra = extra == nullptr
    ? nullptr
    : static_cast<const Inferences::RewriteInferenceExtra*>(extra);
  bool hasReplayRewrite = replayInfo != nullptr && replayInfo->hasDemodulationRewrite;
  bool hasProofExtraRewrite = rewriteExtra != nullptr && rewriteExtra->hasReplacement;
  std::size_t replaySubstitutionCount = replayInfo == nullptr
    ? 0
    : replayInfo->substitutionForBanksSub.size();
  std::vector<Kernel::Clause*> actualParents;
  if (unit->isClause()) {
    for (Kernel::Unit* parent : iterTraits(unit->getParents())) {
      if (parent->isClause()) {
        actualParents.push_back(parent->asClause());
      }
    }
  }
  bool useActualParents = !hasReplayRewrite && actualParents.size() == 2;
  std::vector<Kernel::Clause*> premises = useActualParents
    ? actualParents
    : (replayInfo == nullptr ? std::vector<Kernel::Clause*>() : replayInfo->premises);
  if (!unit->isClause()
    || (
      rule != Kernel::InferenceRule::FORWARD_DEMODULATION
      && rule != Kernel::InferenceRule::BACKWARD_DEMODULATION
	    )
    || (!hasReplayRewrite && !hasProofExtraRewrite)
	    || premises.size() != 2
	    || replaySubstitutionCount > 2) {
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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
    return skipped && appendCertificateSplitLiteralsJson(clause, literals);
  };
  auto substitutedClauseLiterals = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
    if (!appendCertificateSubstitutedClauseLiteralsPreservingEqualityJson(clause, substitution, literals)) {
      return false;
    }
    normalize(literals);
    return true;
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
    if (!appendCertificateSplitLiteralsJson(clause, literals)) {
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
  auto substitutedLiteralArgumentTerms = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::vector<Kernel::TermList>& arguments) {
    Kernel::Literal* indexed = literal->isEquality()
      ? literal
      : (literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal));
    unsigned arity = indexed->isEquality() ? 2 : indexed->arity();
    arguments.clear();
    arguments.reserve(arity);
    for (unsigned i = 0; i < arity; ++i) {
      arguments.push_back(Kernel::SubstHelper::apply(*indexed->nthArgument(i), substitution));
    }
    return true;
  };
  auto literalFromArgumentTermsJson = [&](Kernel::Literal* literal, const std::vector<Kernel::TermList>& arguments, std::string& rendered) {
    if (literal->isEquality()) {
      if (arguments.size() != 2) {
        return false;
      }
      return equalityLiteralFromTermsJson(literal, arguments[0], arguments[1], rendered);
    }

    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (arguments.size() != positive->arity()) {
      return false;
    }
    std::ostringstream atom;
    atom << "{\"pred\":" << quote(predicateName(positive->functor())) << ",\"args\":[";
    for (std::size_t i = 0; i < arguments.size(); ++i) {
      if (i != 0) {
        atom << ',';
      }
      std::string arg;
      if (!certificateTermJson(arguments[i], arg)) {
        return false;
      }
      atom << arg;
    }
    atom << "]}";
    rendered = "{\"polarity\":";
    rendered += literal->isPositive() ? "true" : "false";
    rendered += ",\"atom\":" + atom.str() + "}";
    return true;
  };
  auto rewriteArgumentTermsAtPrintedPosition = [&](std::vector<Kernel::TermList>& arguments, const std::vector<unsigned>& rewritePosition, Kernel::TermList replacement) {
    if (rewritePosition.empty() || rewritePosition[0] >= arguments.size()) {
      return false;
    }
    std::vector<unsigned> argumentPosition(rewritePosition.begin() + 1, rewritePosition.end());
    Kernel::TermList rewrittenArgument;
    if (!replaceTermAtPrintedPosition(replaceTermAtPrintedPosition, arguments[rewritePosition[0]], argumentPosition, 0, replacement, rewrittenArgument)) {
      return false;
    }
    arguments[rewritePosition[0]] = rewrittenArgument;
    return true;
  };
  auto matchTermForDemodulation = [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, Kernel::Substitution& substitution) -> bool {
    if (pattern.isVar()) {
      Kernel::TermList existing;
      if (!substitution.findBinding(pattern.var(), existing)) {
        substitution.bindUnbound(pattern.var(), target);
        return true;
      }
      return existing == target;
    }
    if (!pattern.isTerm() || !target.isTerm()) {
      return pattern == target;
    }
    Kernel::Term* patternTerm = pattern.term();
    Kernel::Term* targetTerm = target.term();
    if (patternTerm->functor() != targetTerm->functor()
      || patternTerm->arity() != targetTerm->arity()) {
      return false;
    }
    for (unsigned index = 0; index < patternTerm->arity(); ++index) {
      if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), substitution)) {
        return false;
      }
    }
    return true;
  };
  auto demodulatorSubstitution = [&](Kernel::Literal* equalityLiteral, Kernel::TermList leftTarget, Kernel::TermList rightTarget, Kernel::Substitution& substitution) {
    return equalityLiteral->isEquality()
      && equalityLiteral->isPositive()
      && matchTermForDemodulation(matchTermForDemodulation, *equalityLiteral->nthArgument(0), leftTarget, substitution)
      && matchTermForDemodulation(matchTermForDemodulation, *equalityLiteral->nthArgument(1), rightTarget, substitution);
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
  auto swappedReplacedSubstitutedEqualityLiteralJson = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, Kernel::TermList what, Kernel::TermList by, std::string& rendered) {
    if (!literal->isEquality()) {
      return false;
    }
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
      atom = "{\"eq\":[" + rhs + "," + lhs + "]}";
    } else {
      atom = "{\"eq\":[" + rhs + "," + lhs + "],\"sort\":" + quote(equalitySort) + "}";
    }
    rendered = "{\"polarity\":";
    rendered += literal->isPositive() ? "true" : "false";
    rendered += ",\"atom\":" + atom + "}";
    return true;
  };

	  Kernel::Substitution emptySubstitution;
	  std::vector<std::vector<Kernel::Substitution>> substitutionAlternatives;
	  if (replaySubstitutionCount == 2) {
	    substitutionAlternatives.push_back({
	      replayInfo->substitutionForBanksSub[0],
	      replayInfo->substitutionForBanksSub[1],
	    });
	  } else if (replaySubstitutionCount == 1) {
	    substitutionAlternatives.push_back({
	      replayInfo->substitutionForBanksSub[0],
	      emptySubstitution,
    });
    substitutionAlternatives.push_back({
      emptySubstitution,
      replayInfo->substitutionForBanksSub[0],
    });
  } else {
    substitutionAlternatives.push_back({
      emptySubstitution,
      emptySubstitution,
    });
  }

  std::vector<std::string> actual;
  if (!normalizedClause(unit->asClause(), actual)) {
    return false;
  }

  Kernel::TermList redex = hasReplayRewrite
    ? replayInfo->demodulationRedex
    : rewriteExtra->rewritten;
  Kernel::TermList replacement = hasReplayRewrite
    ? replayInfo->demodulationReplacement
    : rewriteExtra->replacement;
	  for (const auto& substitutions : substitutionAlternatives) {
	  for (std::size_t equalityParentIndex = 0; equalityParentIndex < 2; ++equalityParentIndex) {
	    std::size_t targetParentIndex = equalityParentIndex == 0 ? 1 : 0;
	    Kernel::Clause* equalityParent = premises[equalityParentIndex];
	    Kernel::Clause* targetParent = premises[targetParentIndex];
	    for (Kernel::Literal* equalityLiteral : equalityParent->iterLits()) {
	      if (!equalityLiteral->isEquality() || !equalityLiteral->isPositive()) {
	        continue;
	      }
	      std::vector<std::vector<Kernel::Substitution>> candidateSubstitutions;
	      candidateSubstitutions.push_back(substitutions);
	      if (hasProofExtraRewrite) {
	        Kernel::Substitution forwardSubstitution;
	        if (demodulatorSubstitution(equalityLiteral, redex, replacement, forwardSubstitution)) {
	          std::vector<Kernel::Substitution> candidate;
	          if (equalityParentIndex == 0) {
	            candidate.push_back(forwardSubstitution);
	            candidate.push_back(substitutions[targetParentIndex]);
	          } else {
	            candidate.push_back(substitutions[targetParentIndex]);
	            candidate.push_back(forwardSubstitution);
	          }
	          candidateSubstitutions.push_back(candidate);
	        }
	        Kernel::Substitution reverseSubstitution;
	        if (demodulatorSubstitution(equalityLiteral, replacement, redex, reverseSubstitution)) {
	          std::vector<Kernel::Substitution> candidate;
	          if (equalityParentIndex == 0) {
	            candidate.push_back(reverseSubstitution);
	            candidate.push_back(substitutions[targetParentIndex]);
	          } else {
	            candidate.push_back(substitutions[targetParentIndex]);
	            candidate.push_back(reverseSubstitution);
	          }
	          candidateSubstitutions.push_back(candidate);
	        }
	      }
	      for (const auto& activeSubstitutions : candidateSubstitutions) {
	      Kernel::TermList equalityLeft = Kernel::SubstHelper::apply(*equalityLiteral->nthArgument(0), activeSubstitutions[equalityParentIndex]);
	      Kernel::TermList equalityRight = Kernel::SubstHelper::apply(*equalityLiteral->nthArgument(1), activeSubstitutions[equalityParentIndex]);
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
	        collectSubstitutedLiteralAtomPositions(targetLiteral, activeSubstitutions[targetParentIndex], redex, positions);
	        if (positions.empty()) {
	          continue;
	        }

	        std::vector<std::string> paramClause;
	        if (!appendSubstitutedClauseExcept(paramClause, targetParent, activeSubstitutions[targetParentIndex], targetLiteral)
	          || !appendSubstitutedClauseExcept(paramClause, equalityParent, activeSubstitutions[equalityParentIndex], equalityLiteral)) {
	          continue;
	        }
	        std::string rewrittenTargetJson;
	        if (!replacedSubstitutedLiteralJson(targetLiteral, activeSubstitutions[targetParentIndex], redex, replacement, rewrittenTargetJson)) {
	          continue;
	        }
	        paramClause.push_back(rewrittenTargetJson);
	        normalize(paramClause);
	        bool needsConclusionSymmetry = false;
	        if (paramClause != actual) {
	          std::string swappedRewrittenTargetJson;
	          if (!swappedReplacedSubstitutedEqualityLiteralJson(targetLiteral, activeSubstitutions[targetParentIndex], redex, replacement, swappedRewrittenTargetJson)) {
	            continue;
	          }
          std::vector<std::string> symmetryClause = paramClause;
          auto rewritten = std::find(symmetryClause.begin(), symmetryClause.end(), rewrittenTargetJson);
          if (rewritten == symmetryClause.end()) {
            continue;
          }
          *rewritten = swappedRewrittenTargetJson;
          normalize(symmetryClause);
          if (symmetryClause != actual) {
            continue;
          }
          needsConclusionSymmetry = true;
        }

        std::string stepBase = "u" + std::to_string(unit->number());
        std::vector<std::string> steps;
	        std::vector<std::string> parentIds(2);
	        for (std::size_t parentIndex = 0; parentIndex < 2; ++parentIndex) {
	          std::string substitutionJson;
	          std::string clauseJson;
	          if (!certificateSubstitutionJson(activeSubstitutions[parentIndex], substitutionJson)
	            || !certificateSubstitutedClausePreservingEqualityJson(premises[parentIndex], activeSubstitutions[parentIndex], clauseJson)) {
	            return false;
	          }
          parentIds[parentIndex] = "u" + std::to_string(premises[parentIndex]->number());
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
	        std::string paramodulationConclusionJson = jsonArray(paramClause);
	        if (!certificateSubstitutedLiteralPreservingEqualityJson(equalityLiteral, activeSubstitutions[equalityParentIndex], equalityParentLiteralJson)
	          || !positiveEqualityLiteralJson(equalityLiteral, redex, replacement, equalityJson)
	          || !certificateTermJson(redex, fromJson)
	          || !certificateTermJson(replacement, toJson)
	          || !certificateSubstitutedLiteralPreservingEqualityJson(targetLiteral, activeSubstitutions[targetParentIndex], targetJson)
	          || !certificateClauseJson(unit->asClause(), conclusionJson)) {
	          return false;
	        }

	        std::string equalityParentId = parentIds[equalityParentIndex];
	        if (needsSymmetry || equalityParentLiteralJson != equalityJson) {
	          std::string symmetryClauseJson;
	          if (!substitutedClauseReplacingOneLiteralJson(equalityParent, activeSubstitutions[equalityParentIndex], equalityLiteral, equalityJson, symmetryClauseJson)) {
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

        std::string paramodulationStepId = needsConclusionSymmetry ? stepBase + "_paramodulate" : stepBase;
	        if (positions.size() == 1) {
	          std::string positionField = "\"position\":" + positionJson(positions.front()) + ",";
	          std::string rewriteScopeField;
	          rewriteScopeJson(targetLiteral, activeSubstitutions[targetParentIndex], positions.front(), rewriteScopeField);
	          steps.push_back(
            "{\"id\":" + quote(paramodulationStepId) + ","
            "\"rule\":\"paramodulate\","
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
            "\"clause\":" + paramodulationConclusionJson + "}");
	        } else {
	          std::vector<std::string> currentClause;
	          std::vector<std::string> equalityRemainder;
	          if (!substitutedClauseLiterals(targetParent, activeSubstitutions[targetParentIndex], currentClause)
	            || !appendSubstitutedClauseExcept(equalityRemainder, equalityParent, activeSubstitutions[equalityParentIndex], equalityLiteral)) {
	            return false;
	          }
          normalize(currentClause);
          normalize(equalityRemainder);
          std::string currentParentId = parentIds[targetParentIndex];
          std::string currentTargetJson = targetJson;
	          std::vector<Kernel::TermList> currentArguments;
	          if (!substitutedLiteralArgumentTerms(targetLiteral, activeSubstitutions[targetParentIndex], currentArguments)) {
	            return false;
	          }
          for (std::size_t index = 0; index < positions.size(); ++index) {
            const std::vector<unsigned>& rewritePosition = positions[index];
            if (!rewriteArgumentTermsAtPrintedPosition(currentArguments, rewritePosition, replacement)) {
              return false;
            }
            std::string nextTargetJson;
            if (!literalFromArgumentTermsJson(targetLiteral, currentArguments, nextTargetJson)) {
              return false;
            }
            auto literalIt = std::find(currentClause.begin(), currentClause.end(), currentTargetJson);
            if (literalIt == currentClause.end()) {
              return false;
            }
            currentClause.erase(literalIt);
            currentClause.push_back(nextTargetJson);
            currentClause.insert(currentClause.end(), equalityRemainder.begin(), equalityRemainder.end());
            normalize(currentClause);

            bool lastRewrite = index + 1 == positions.size();
            std::string rewriteStepId = lastRewrite ? paramodulationStepId : stepBase + "_paramodulate" + std::to_string(index);
            std::string rewriteClauseJson = lastRewrite ? paramodulationConclusionJson : jsonArray(currentClause);
	            std::string rewriteScopeField;
	            rewriteScopeJson(targetLiteral, activeSubstitutions[targetParentIndex], rewritePosition, rewriteScopeField);
	            steps.push_back(
              "{\"id\":" + quote(rewriteStepId) + ","
              "\"rule\":\"paramodulate\","
              "\"parents\":["
              + quote(equalityParentId) + ","
              + quote(currentParentId) + "],"
              "\"equality\":" + equalityJson + ","
              "\"from\":" + fromJson + ","
              "\"to\":" + toJson + ","
              "\"target\":" + currentTargetJson + ","
              "\"rewritten_target\":" + nextTargetJson + ","
              "\"position\":" + positionJson(rewritePosition) + ","
              + rewriteScopeField
              + "\"substitution\":{},"
              "\"clause\":" + rewriteClauseJson + "}");
            currentParentId = rewriteStepId;
            currentTargetJson = nextTargetJson;
          }
          if (currentClause != paramClause) {
            return false;
          }
        }
        if (needsConclusionSymmetry) {
          steps.push_back(
            "{\"id\":" + quote(stepBase) + ","
            "\"rule\":\"equality_symmetry\","
            "\"parents\":[" + quote(paramodulationStepId) + "],"
            "\"literal\":" + rewrittenTargetJson + ","
            "\"clause\":" + conclusionJson + "}");
        }
	        result = jsonArray(steps);
	        return true;
	      }
	      }
	    }
	    }
	  }
  return false;
}

bool MegalodonChecker::certificateUnitResultingResolutionStepsJson(Kernel::Unit* unit, std::string& result)
{
  auto fail = [&](const char* reason) {
    if (std::getenv("MEGALODON_CERT_DEBUG")) {
      std::cerr << "megalodon URR certificate failed for u" << unit->number() << ": " << reason << std::endl;
    }
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
  auto cloneSubstitution = [](const Kernel::Substitution& source) {
    Kernel::Substitution copy;
    Kernel::Substitution sourceCopy = source;
    for (auto [var, term] : iterTraits(sourceCopy.items())) {
      copy.bindUnbound(var, term);
    }
    return copy;
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

  auto normalizeJsonClause = [](std::vector<std::string>& clause) {
    std::sort(clause.begin(), clause.end());
    clause.erase(std::unique(clause.begin(), clause.end()), clause.end());
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

  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };

  auto applyJsonSubstitution = [&](const std::string& source,
                                   const Kernel::Substitution& substitution,
                                   std::string& rendered) {
    std::vector<std::tuple<unsigned, std::string, std::string>> replacements;
    Kernel::Substitution substitutionCopy = substitution;
    for (auto [var, term] : iterTraits(substitutionCopy.items())) {
      if (term.isVar() && term.var() == var) {
        continue;
      }
      std::string termJson;
      if (!certificateTermJson(term, termJson)) {
        return false;
      }
      replacements.push_back({var, "{\"var\":" + quote(variableName(var)) + "}", termJson});
    }
    std::sort(replacements.begin(), replacements.end(), [](const auto& left, const auto& right) {
      return std::get<0>(left) < std::get<0>(right);
    });
    rendered = source;
    for (std::size_t i = 0; i < replacements.size(); ++i) {
      replaceAll(rendered, std::get<1>(replacements[i]), quote("__mg_subst_" + std::to_string(i) + "__"));
    }
    for (std::size_t i = 0; i < replacements.size(); ++i) {
      replaceAll(rendered, quote("__mg_subst_" + std::to_string(i) + "__"), std::get<2>(replacements[i]));
    }
    return true;
  };

  auto renderClause = [&](const std::vector<Kernel::Literal*>& literals,
                          const std::vector<Kernel::Clause*>& splitSources,
                          std::string& rendered) {
    std::vector<std::string> items;
    for (Kernel::Literal* literal : literals) {
      std::string literalJson;
      if (!certificateLiteralJson(literal, literalJson)) {
        return false;
      }
      items.push_back(literalJson);
    }
    for (Kernel::Clause* splitSource : splitSources) {
      if (!appendCertificateSplitLiteralsJson(splitSource, items)) {
        return false;
      }
    }
    normalizeJsonClause(items);
    rendered = jsonArray(items);
    return true;
  };

  auto renderSubstitutedClause = [&](Kernel::Clause* clause,
                                     const Kernel::Substitution& substitution,
                                     std::string& rendered) {
    std::vector<std::string> items;
    if (!appendCertificateSubstitutedClauseLiteralsPreservingEqualityJson(clause, substitution, items)) {
      return false;
    }
    normalizeJsonClause(items);
    rendered = jsonArray(items);
    return true;
  };

  std::string actualClauseJson;
  std::vector<std::string> actualClause;
  if (!certificateClauseJson(unit->asClause(), actualClauseJson)
    || !appendCertificateClauseLiteralsJson(unit->asClause(), actualClause)) {
    return fail("actual clause json failed");
  }
  normalizeJsonClause(actualClause);

  std::vector<std::string> steps;
  std::string stepBase = "u" + std::to_string(unit->number());
  std::string currentStepId = "u" + std::to_string(mainParent->number());
  std::vector<Kernel::Literal*> currentLiterals;
  for (Kernel::Literal* literal : mainParent->iterLits()) {
    currentLiterals.push_back(literal);
  }
  std::vector<Kernel::Clause*> splitSources;
  splitSources.push_back(mainParent);
  std::vector<std::string> currentClause;
  {
    std::string currentClauseJson;
    if (!renderClause(currentLiterals, splitSources, currentClauseJson)) {
      return fail("initial clause render failed");
    }
    if (!appendCertificateClauseLiteralsJson(mainParent, currentClause)) {
      return fail("initial clause literals failed");
    }
    normalizeJsonClause(currentClause);
  }

  for (std::size_t traceIndex = 0; traceIndex < urr->steps.size(); ++traceIndex) {
    const auto& trace = urr->steps[traceIndex];
    Kernel::Clause* unitParent = trace.unitParent;
    Kernel::Literal* unitLiteral = (*unitParent)[0];

    Kernel::Literal* selectedCurrentLiteral = nullptr;
    Kernel::Substitution currentSubstitution;
    std::string traceSelectedLiteralJson;
    if (!certificateLiteralJson(trace.selected, traceSelectedLiteralJson)) {
      return fail("trace selected literal render failed");
    }
    unsigned selectionPasses = traceIndex == 0 ? 2 : 1;
    for (unsigned pass = 0; pass < selectionPasses && selectedCurrentLiteral == nullptr; ++pass) {
      for (Kernel::Literal* literal : currentLiterals) {
        if (selectionPasses == 2 && pass == 0) {
          std::string currentLiteralJson;
          if (!certificateLiteralJson(literal, currentLiteralJson)
            || currentLiteralJson != traceSelectedLiteralJson) {
            continue;
          }
        }
        Kernel::Substitution attempt;
        if (!matchLiteralWithoutReset(literal, trace.selectedSubstituted, attempt)) {
          continue;
        }
        selectedCurrentLiteral = literal;
        for (auto [var, term] : iterTraits(attempt.items())) {
          currentSubstitution.bindUnbound(var, term);
        }
        break;
      }
    }
    if (selectedCurrentLiteral == nullptr
      && matchLiteralWithoutReset(trace.selected, trace.selectedSubstituted, currentSubstitution)) {
      selectedCurrentLiteral = trace.selected;
    }
    if (selectedCurrentLiteral == nullptr) {
      return fail("current substitution match failed");
    }
    std::string currentSubstitutionJson;
    if (!certificateSubstitutionJson(currentSubstitution, currentSubstitutionJson)) {
      return fail("current substitution json failed");
    }
    std::vector<std::string> substitutedCurrentClause;
    for (const std::string& literalJson : currentClause) {
      std::string rendered;
      if (!applyJsonSubstitution(literalJson, currentSubstitution, rendered)) {
        return fail("current substituted literal render failed");
      }
      substitutedCurrentClause.push_back(rendered);
    }
    normalizeJsonClause(substitutedCurrentClause);
    std::vector<Kernel::Literal*> substitutedCurrentLiterals;
    for (Kernel::Literal* literal : currentLiterals) {
      substitutedCurrentLiterals.push_back(Kernel::SubstHelper::apply(literal, currentSubstitution));
    }
    std::string currentSubstitutedClauseJson = jsonArray(substitutedCurrentClause);
    if (currentSubstitutionJson != "{}") {
      std::string substituteId = stepBase + "_current_subst" + std::to_string(traceIndex);
      steps.push_back(
        "{\"id\":" + quote(substituteId) + ","
        "\"rule\":\"substitute\","
        "\"parents\":[" + quote(currentStepId) + "],"
        "\"substitution\":" + currentSubstitutionJson + ","
        "\"clause\":" + currentSubstitutedClauseJson + "}");
      currentStepId = substituteId;
    }
    currentLiterals = substitutedCurrentLiterals;
    currentClause = substitutedCurrentClause;

    Kernel::Substitution unitSubstitution;
    if (!matchLiteralWithoutReset(unitLiteral, trace.unitSubstituted, unitSubstitution)) {
      return fail("unit substitution match failed");
    }
    std::string unitSubstitutionJson;
    std::string unitClauseJson;
    if (!certificateSubstitutionJson(unitSubstitution, unitSubstitutionJson)
      || !renderSubstitutedClause(unitParent, unitSubstitution, unitClauseJson)) {
      return fail("unit substitution json failed");
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

    Kernel::Literal* selectedSubstituted = trace.selectedSubstituted;
    Kernel::Literal* unitSubstituted = Kernel::SubstHelper::apply(unitLiteral, unitSubstitution);
    std::string selectedJson;
    std::string selectedCurrentJson;
    std::string unitJson;
    std::string selectedBaseJson;
    if (!certificateLiteralJson(selectedSubstituted, selectedJson)
      || !certificateLiteralJson(selectedCurrentLiteral, selectedBaseJson)
      || !applyJsonSubstitution(selectedBaseJson, currentSubstitution, selectedCurrentJson)
      || !certificateSubstitutedLiteralPreservingEqualityJson(unitLiteral, unitSubstitution, unitJson)) {
      return fail("selected/unit literal json failed");
    }
    std::string selectedSourceJson = selectedCurrentJson;
    if (std::find(currentClause.begin(), currentClause.end(), selectedJson) == currentClause.end()) {
      if (!selectedSubstituted->isEquality()) {
        return fail("selected pivot orientation is not equality");
      }
      std::string swappedSelectedJson;
      if (!certificateSubstitutedEqualityLiteralJson(selectedCurrentLiteral, currentSubstitution, true, swappedSelectedJson)) {
        return fail("selected pivot symmetry render failed");
      }
      auto selectedIt = std::find(currentClause.begin(), currentClause.end(), selectedCurrentJson);
      if (selectedIt == currentClause.end()) {
        selectedIt = std::find(currentClause.begin(), currentClause.end(), swappedSelectedJson);
        selectedSourceJson = swappedSelectedJson;
      }
      if (selectedIt == currentClause.end()) {
        return fail("selected symmetry literal missing");
      }
      *selectedIt = selectedJson;
      normalizeJsonClause(currentClause);
      std::string symmetryStepId = stepBase + "_current_symmetry" + std::to_string(traceIndex);
      steps.push_back(
        "{\"id\":" + quote(symmetryStepId) + ","
        "\"rule\":\"equality_symmetry\","
        "\"parents\":[" + quote(currentStepId) + "],"
        "\"literal\":" + selectedSourceJson + ","
        "\"clause\":" + jsonArray(currentClause) + "}");
      currentStepId = symmetryStepId;
      selectedCurrentJson = selectedJson;
    }

    std::string selectedComplementJson;
    if (!certificateLiteralJson(Kernel::Literal::complementaryLiteral(selectedSubstituted), selectedComplementJson)) {
      return fail("selected complement json failed");
    }
    if (unitJson != selectedComplementJson) {
      if (!unitSubstituted->isEquality()) {
        return fail("unit pivot orientation is not equality");
      }
      std::string swappedUnitJson;
      if (!certificateSubstitutedEqualityLiteralJson(unitLiteral, unitSubstitution, true, swappedUnitJson)
        || swappedUnitJson != selectedComplementJson) {
        return fail("unit pivot symmetry mismatch");
      }
      std::vector<std::string> symmetryClause;
      bool replacedUnitLiteral = false;
      for (Kernel::Literal* literal : unitParent->iterLits()) {
        if (!replacedUnitLiteral && literal == unitLiteral) {
          symmetryClause.push_back(swappedUnitJson);
          replacedUnitLiteral = true;
          continue;
        }
        std::string rendered;
        if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, unitSubstitution, rendered)) {
          return fail("unit pivot symmetry mismatch");
        }
        symmetryClause.push_back(rendered);
      }
      if (!replacedUnitLiteral || !appendCertificateSplitLiteralsJson(unitParent, symmetryClause)) {
        return fail("unit symmetry clause failed");
      }
      std::string symmetryStepId = stepBase + "_unit_symmetry" + std::to_string(traceIndex);
      steps.push_back(
        "{\"id\":" + quote(symmetryStepId) + ","
        "\"rule\":\"equality_symmetry\","
        "\"parents\":[" + quote(unitParentId) + "],"
        "\"literal\":" + unitJson + ","
        "\"clause\":" + jsonArray(symmetryClause) + "}");
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

    std::vector<Kernel::Clause*> nextSplitSources = splitSources;
    nextSplitSources.push_back(unitParent);
    auto selectedIt = std::find(currentClause.begin(), currentClause.end(), selectedJson);
    if (selectedIt == currentClause.end()) {
      return fail("selected literal missing from current clause");
    }
    std::vector<std::string> nextCurrentClause = currentClause;
    nextCurrentClause.erase(nextCurrentClause.begin() + std::distance(currentClause.begin(), selectedIt));
    if (!appendCertificateSplitLiteralsJson(unitParent, nextCurrentClause)) {
      return fail("post-resolve split append failed");
    }
    normalizeJsonClause(nextCurrentClause);

    std::vector<Kernel::Literal*> nextCurrentLiterals;
    bool removedSelectedLiteral = false;
    for (Kernel::Literal* literal : currentLiterals) {
      if (!removedSelectedLiteral) {
        std::string rendered;
        if (!certificateLiteralJson(literal, rendered)) {
          return fail("post-resolve current literal render failed");
        }
        bool matchesSelected = rendered == selectedJson;
        if (!matchesSelected && literal->isEquality()) {
          std::string swapped;
          if (!certificateSubstitutedEqualityLiteralJson(literal, Kernel::Substitution(), true, swapped)) {
            return fail("post-resolve current literal symmetry render failed");
          }
          matchesSelected = swapped == selectedJson;
        }
        if (matchesSelected) {
          removedSelectedLiteral = true;
          continue;
        }
      }
      nextCurrentLiterals.push_back(literal);
    }
    if (!removedSelectedLiteral) {
      return fail("selected literal missing from current literal state");
    }
    std::string resolveStepId = stepBase + "_resolve" + std::to_string(traceIndex);
    steps.push_back(
      "{\"id\":" + quote(resolveStepId) + ","
      "\"rule\":\"resolve\","
      "\"parents\":[" + quote(leftParentId) + "," + quote(rightParentId) + "],"
      "\"pivot\":" + pivotJson + ","
      "\"clause\":" + jsonArray(nextCurrentClause) + "}");
    currentStepId = resolveStepId;

    currentLiterals = nextCurrentLiterals;
    currentClause = nextCurrentClause;
    splitSources = nextSplitSources;
  }

  if (currentClause != actualClause) {
    Kernel::Substitution finalRenameSubstitution;
    std::vector<bool> usedActual(unit->asClause()->length(), false);
    bool finalRenameMatched = currentLiterals.size() == unit->asClause()->length();
    if (finalRenameMatched) {
      for (Kernel::Literal* currentLiteral : currentLiterals) {
        bool matched = false;
        for (unsigned actualIndex = 0; actualIndex < unit->asClause()->length(); ++actualIndex) {
          if (usedActual[actualIndex]) {
            continue;
          }
          Kernel::Substitution attempt = cloneSubstitution(finalRenameSubstitution);
          if (!matchLiteralWithoutReset(currentLiteral, (*unit->asClause())[actualIndex], attempt)) {
            continue;
          }
          finalRenameSubstitution = cloneSubstitution(attempt);
          usedActual[actualIndex] = true;
          matched = true;
          break;
        }
        if (!matched) {
          finalRenameMatched = false;
          break;
        }
      }
    }
    std::string finalRenameSubstitutionJson;
    if (finalRenameMatched && !certificateSubstitutionJson(finalRenameSubstitution, finalRenameSubstitutionJson)) {
      return fail("final rename substitution json failed");
    }
    if (finalRenameMatched && finalRenameSubstitutionJson != "{}") {
      std::vector<Kernel::Literal*> renamedLiterals;
      for (Kernel::Literal* literal : currentLiterals) {
        renamedLiterals.push_back(Kernel::SubstHelper::apply(literal, finalRenameSubstitution));
      }
      currentLiterals = renamedLiterals;
      std::vector<std::string> renamedClause;
      for (const std::string& literalJson : currentClause) {
        std::string rendered;
        if (!applyJsonSubstitution(literalJson, finalRenameSubstitution, rendered)) {
          return fail("final rename literal render failed");
        }
        renamedClause.push_back(rendered);
      }
      normalizeJsonClause(renamedClause);
      std::string finalRenameClauseJson = jsonArray(renamedClause);
      std::string renameStepId = stepBase + "_final_rename";
      steps.push_back(
        "{\"id\":" + quote(renameStepId) + ","
        "\"rule\":\"substitute\","
        "\"parents\":[" + quote(currentStepId) + "],"
        "\"substitution\":" + finalRenameSubstitutionJson + ","
        "\"clause\":" + finalRenameClauseJson + "}");
      currentStepId = renameStepId;
      currentClause = renamedClause;
    }
  }

  for (std::size_t guard = 0; currentClause != actualClause && guard < currentLiterals.size(); ++guard) {
    bool changed = false;
    for (Kernel::Literal* literal : currentLiterals) {
      if (!literal->isEquality()) {
        continue;
      }
      std::string literalJson;
      std::string swappedJson;
      if (!certificateLiteralJson(literal, literalJson)
        || !certificateSubstitutedEqualityLiteralJson(literal, Kernel::Substitution(), true, swappedJson)) {
        return fail("final symmetry render failed");
      }
      if (std::find(actualClause.begin(), actualClause.end(), literalJson) != actualClause.end()) {
        auto swappedCurrentIt = std::find(currentClause.begin(), currentClause.end(), swappedJson);
        if (swappedCurrentIt != currentClause.end()) {
          *swappedCurrentIt = literalJson;
          normalizeJsonClause(currentClause);
          std::string symmetryStepId = stepBase + "_final_symmetry" + std::to_string(guard);
          steps.push_back(
            "{\"id\":" + quote(symmetryStepId) + ","
            "\"rule\":\"equality_symmetry\","
            "\"parents\":[" + quote(currentStepId) + "],"
            "\"literal\":" + swappedJson + ","
            "\"clause\":" + jsonArray(currentClause) + "}");
          currentStepId = symmetryStepId;
          changed = true;
          break;
        }
      }
      if (std::find(actualClause.begin(), actualClause.end(), swappedJson) == actualClause.end()) {
        continue;
      }
      auto currentIt = std::find(currentClause.begin(), currentClause.end(), literalJson);
      if (currentIt == currentClause.end()) {
        continue;
      }
      *currentIt = swappedJson;
      normalizeJsonClause(currentClause);
      std::string symmetryStepId = stepBase + "_final_symmetry" + std::to_string(guard);
      steps.push_back(
        "{\"id\":" + quote(symmetryStepId) + ","
        "\"rule\":\"equality_symmetry\","
        "\"parents\":[" + quote(currentStepId) + "],"
        "\"literal\":" + literalJson + ","
        "\"clause\":" + jsonArray(currentClause) + "}");
      currentStepId = symmetryStepId;
      changed = true;
      break;
    }
    if (!changed) {
      break;
    }
  }
  if (currentClause != actualClause) {
    return fail("sequential urr replay did not reach conclusion");
  }
  if (currentStepId != stepBase) {
    steps.push_back(
      "{\"id\":" + quote(stepBase) + ","
      "\"rule\":\"substitute\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"substitution\":{},"
      "\"clause\":" + actualClauseJson + "}");
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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
      if (!appendCertificateSplitLiteralsJson(parents[parentIndex], expected)) {
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
    if (!appendCertificateClauseLiteralsJson(unit->asClause(), actual)) {
      return false;
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

  auto matchTerm = [&](auto&& self, Kernel::TermList pattern, Kernel::TermList target, std::map<unsigned, Kernel::TermList>& bindings) -> bool {
    if (pattern.isVar()) {
      auto existing = bindings.find(pattern.var());
      if (existing == bindings.end()) {
        bindings.emplace(pattern.var(), target);
        return true;
      }
      return existing->second == target;
    }
    if (!pattern.isTerm() || !target.isTerm()) {
      return pattern == target;
    }
    Kernel::Term* patternTerm = pattern.term();
    Kernel::Term* targetTerm = target.term();
    if (patternTerm->functor() != targetTerm->functor()
      || patternTerm->arity() != targetTerm->arity()) {
      return false;
    }
    for (unsigned index = 0; index < patternTerm->arity(); ++index) {
      if (!self(self, *patternTerm->nthArgument(index), *targetTerm->nthArgument(index), bindings)) {
        return false;
      }
    }
    return true;
  };
  auto matchLiteralOriented = [&](Kernel::Literal* pattern, Kernel::Literal* target, bool samePolarity, bool reverseEquality, std::map<unsigned, Kernel::TermList>& bindings) {
    if ((pattern->polarity() == target->polarity()) != samePolarity) {
      return false;
    }
    if (pattern->isEquality() != target->isEquality()) {
      return false;
    }
    if (pattern->isEquality()) {
      if (!matchTerm(matchTerm,
          Kernel::SortHelper::getEqualityArgumentSort(pattern),
          Kernel::SortHelper::getEqualityArgumentSort(target),
          bindings)) {
        return false;
      }
      Kernel::TermList targetLeft = *target->nthArgument(reverseEquality ? 1 : 0);
      Kernel::TermList targetRight = *target->nthArgument(reverseEquality ? 0 : 1);
      return matchTerm(matchTerm, *pattern->nthArgument(0), targetLeft, bindings)
        && matchTerm(matchTerm, *pattern->nthArgument(1), targetRight, bindings);
    }
    if (pattern->functor() != target->functor()
      || pattern->arity() != target->arity()) {
      return false;
    }
    for (unsigned index = 0; index < pattern->arity(); ++index) {
      if (!matchTerm(matchTerm, *pattern->nthArgument(index), *target->nthArgument(index), bindings)) {
        return false;
      }
    }
    return true;
  };
  auto matchLiteral = [&](Kernel::Literal* pattern, Kernel::Literal* target, bool samePolarity, std::map<unsigned, Kernel::TermList>& bindings) {
    std::map<unsigned, Kernel::TermList> trial = bindings;
    if (matchLiteralOriented(pattern, target, samePolarity, false, trial)) {
      bindings = std::move(trial);
      return true;
    }
    if (pattern->isEquality()) {
      trial = bindings;
      if (matchLiteralOriented(pattern, target, samePolarity, true, trial)) {
        bindings = std::move(trial);
        return true;
      }
    }
    return false;
  };
  auto fallbackSideSubstitution = [&](Kernel::Clause* sideParent, Kernel::Literal* selectedLiteral, Kernel::Substitution& sideSubstitution) {
    for (unsigned pivotIndex = 0; pivotIndex < sideParent->length(); ++pivotIndex) {
      Kernel::Literal* sidePivot = (*sideParent)[pivotIndex];
      std::map<unsigned, Kernel::TermList> pivotBindings;
      if (!matchLiteral(sidePivot, selectedLiteral, false, pivotBindings)) {
        continue;
      }

      std::function<bool(unsigned, std::map<unsigned, Kernel::TermList>&)> matchRemainder =
        [&](unsigned sideIndex, std::map<unsigned, Kernel::TermList>& bindings) {
          if (sideIndex == sideParent->length()) {
            return true;
          }
          if (sideIndex == pivotIndex) {
            return matchRemainder(sideIndex + 1, bindings);
          }
          Kernel::Literal* sideLiteral = (*sideParent)[sideIndex];
          for (Kernel::Literal* conclusionLiteral : unit->asClause()->iterLits()) {
            std::map<unsigned, Kernel::TermList> trial = bindings;
            if (!matchLiteral(sideLiteral, conclusionLiteral, true, trial)) {
              continue;
            }
            if (matchRemainder(sideIndex + 1, trial)) {
              bindings = std::move(trial);
              return true;
            }
          }
          return false;
        };

      std::map<unsigned, Kernel::TermList> bindings = std::move(pivotBindings);
      if (!matchRemainder(0, bindings)) {
        continue;
      }
      for (const auto& binding : bindings) {
        sideSubstitution.rebind(binding.first, binding.second);
      }
      return true;
    }
    return false;
  };

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
      Kernel::Substitution sideSubstitution;
      bool foundSideSubstitution = fallbackSideSubstitution(sideParent, selectedLiteral, sideSubstitution);
      if (!foundSideSubstitution && satSR.checkSubsumptionResolutionWithLiteral(sideParent, mainParent, selectedLiteralIndex)) {
        sideSubstitution = satSR.getBindingsForSubsumptionResolutionWithLiteral();
        foundSideSubstitution = true;
      }
      if (!foundSideSubstitution) {
        continue;
      }
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
        if (!appendCertificateSplitLiteralsJson(mainParent, expected)
          || !appendCertificateSplitLiteralsJson(sideParent, expected)) {
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
        std::string highLevelStep =
          "{\"rule\":\"subsumption_resolution\","
          "\"parents\":["
          + quote("u" + std::to_string(mainParent->number())) + ","
          + quote("u" + std::to_string(sideParent->number())) + "],"
          "\"selected\":" + selectedLiteralJson + ","
          "\"side_pivot\":" + sideLiteralJson + ","
          "\"side_substitution\":" + sideSubstitutionJson + ","
          "\"clause\":" + jsonArray(actual) + "}";
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
        if (!appendCertificateSplitLiteralsJson(mainParent, resolvedExpected)) {
          continue;
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
          if (!appendCertificateSplitLiteralsJson(sideParent, sideCurrent)
            || !appendCertificateSplitLiteralsJson(sideParent, resolvedExpected)) {
            canExpandAsPrimitiveSteps = false;
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
        result = highLevelStep;
        return true;
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
    if (!appendCertificateClauseLiteralsJson(clause, literals)) {
      return false;
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
    return skipped && appendCertificateSplitLiteralsJson(clause, literals);
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
  auto substitutedLiteralArgumentTerms = [&](Kernel::Literal* literal, const Kernel::Substitution& substitution, std::vector<Kernel::TermList>& arguments) {
    Kernel::Literal* indexed = literal->isEquality()
      ? literal
      : (literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal));
    unsigned arity = indexed->isEquality() ? 2 : indexed->arity();
    arguments.clear();
    arguments.reserve(arity);
    for (unsigned i = 0; i < arity; ++i) {
      arguments.push_back(Kernel::SubstHelper::apply(*indexed->nthArgument(i), substitution));
    }
    return true;
  };
  auto literalFromArgumentTermsJson = [&](Kernel::Literal* literal, const std::vector<Kernel::TermList>& arguments, std::string& rendered) {
    if (literal->isEquality()) {
      if (arguments.size() != 2) {
        return false;
      }
      return equalityLiteralFromTermsJson(literal, arguments[0], arguments[1], rendered);
    }

    Kernel::Literal* positive = literal->isPositive() ? literal : Kernel::Literal::complementaryLiteral(literal);
    if (arguments.size() != positive->arity()) {
      return false;
    }
    std::ostringstream atom;
    atom << "{\"pred\":" << quote(predicateName(positive->functor())) << ",\"args\":[";
    for (std::size_t i = 0; i < arguments.size(); ++i) {
      if (i != 0) {
        atom << ',';
      }
      std::string arg;
      if (!certificateTermJson(arguments[i], arg)) {
        return false;
      }
      atom << arg;
    }
    atom << "]}";
    rendered = "{\"polarity\":";
    rendered += literal->isPositive() ? "true" : "false";
    rendered += ",\"atom\":" + atom.str() + "}";
    return true;
  };
  auto rewriteArgumentTermsAtPrintedPosition = [&](std::vector<Kernel::TermList>& arguments, const std::vector<unsigned>& rewritePosition, Kernel::TermList replacement) {
    if (rewritePosition.empty() || rewritePosition[0] >= arguments.size()) {
      return false;
    }
    std::vector<unsigned> argumentPosition(rewritePosition.begin() + 1, rewritePosition.end());
    Kernel::TermList rewrittenArgument;
    if (!replaceTermAtPrintedPosition(replaceTermAtPrintedPosition, arguments[rewritePosition[0]], argumentPosition, 0, replacement, rewrittenArgument)) {
      return false;
    }
    arguments[rewritePosition[0]] = rewrittenArgument;
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
    if (!appendCertificateSplitLiteralsJson(clause, literals)) {
      return false;
    }
    std::ostringstream out;
    out << '[';
    for (std::size_t i = 0; i < literals.size(); ++i) {
      if (i != 0) {
        out << ',';
      }
      out << literals[i];
    }
    out << ']';
    rendered = out.str();
    return true;
  };
  struct TargetRewrite {
    std::string literalJson;
    std::string rewrittenJson;
    std::vector<unsigned> position;
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
      std::vector<Kernel::TermList> currentArguments;
      if (!certificateSubstitutedLiteralPreservingEqualityJson(literal, substitution, literalJson)
        || !substitutedLiteralArgumentTerms(literal, substitution, currentArguments)) {
        return false;
      }
      std::string currentJson = literalJson;
      for (const std::vector<unsigned>& rewritePosition : positions) {
        if (!rewriteArgumentTermsAtPrintedPosition(currentArguments, rewritePosition, by)) {
          return false;
        }
        std::string nextJson;
        if (!literalFromArgumentTermsJson(literal, currentArguments, nextJson)) {
          return false;
        }
        targetRewrites.push_back({currentJson, nextJson, rewritePosition});
        currentJson = nextJson;
      }
      literals.push_back(currentJson);

      if (literal->isEquality()) {
        std::string swappedRewrittenJson;
        if (currentArguments.size() != 2
          || !equalityLiteralFromTermsJson(literal, currentArguments[1], currentArguments[0], swappedRewrittenJson)) {
          return false;
        }
        if (currentJson != swappedRewrittenJson) {
          symmetryCandidates.push_back({currentJson, swappedRewrittenJson});
        }
      }
    }
    if (!appendCertificateSplitLiteralsJson(clause, literals)) {
      return false;
    }
    return true;
  };
  auto substitutedClauseLiterals = [&](Kernel::Clause* clause, const Kernel::Substitution& substitution, std::vector<std::string>& literals) {
    if (!appendCertificateSubstitutedClauseLiteralsPreservingEqualityJson(clause, substitution, literals)) {
      return false;
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
    if (!appendCertificateSplitLiteralsJson(clause, literals)) {
      return false;
    }
    std::sort(literals.begin(), literals.end());
    literals.erase(std::unique(literals.begin(), literals.end()), literals.end());
    return true;
  };

  Kernel::TermList preferredRedex = Kernel::SubstHelper::apply(
    rewrite->rewrite.rewritten,
    replayInfo->substitutionForBanksSub[targetParentIndex]);
  Kernel::TermList preferredEqualitySide = Kernel::SubstHelper::apply(
    rewrite->rewrite.lhs,
    replayInfo->substitutionForBanksSub[equalityParentIndex]);
  Kernel::TermList from;
  Kernel::TermList to;
  std::vector<std::vector<unsigned>> redexPositions;
  auto chooseEqualitySource = [&](Kernel::Literal* candidate, bool allowUnpreferredMatch) {
    if (candidate == nullptr || !candidate->isEquality() || !candidate->isPositive()) {
      return false;
    }
    Kernel::Literal* substituted = Kernel::SubstHelper::apply(candidate, replayInfo->substitutionForBanksSub[equalityParentIndex]);
    Kernel::TermList left = *substituted->nthArgument(0);
    Kernel::TermList right = *substituted->nthArgument(1);
    std::vector<std::vector<unsigned>> leftPositions;
    std::vector<std::vector<unsigned>> rightPositions;
    collectPrintedSubstitutedLiteralAtomPositions(
      targetLiteral,
      replayInfo->substitutionForBanksSub[targetParentIndex],
      left,
      leftPositions);
    collectPrintedSubstitutedLiteralAtomPositions(
      targetLiteral,
      replayInfo->substitutionForBanksSub[targetParentIndex],
      right,
      rightPositions);

    if (preferredRedex == left && !leftPositions.empty()) {
      from = left;
      to = right;
      redexPositions = leftPositions;
    } else if (preferredRedex == right && !rightPositions.empty()) {
      from = right;
      to = left;
      redexPositions = rightPositions;
    } else if (preferredEqualitySide == left && !leftPositions.empty()) {
      from = left;
      to = right;
      redexPositions = leftPositions;
    } else if (preferredEqualitySide == right && !rightPositions.empty()) {
      from = right;
      to = left;
      redexPositions = rightPositions;
    } else if (allowUnpreferredMatch && !leftPositions.empty()) {
      from = left;
      to = right;
      redexPositions = leftPositions;
    } else if (allowUnpreferredMatch && !rightPositions.empty()) {
      from = right;
      to = left;
      redexPositions = rightPositions;
    } else {
      return false;
    }
    equalityLiteral = candidate;
    return true;
  };
  Kernel::Literal* recordedEqualityLiteral = equalityLiteral;
  bool foundSource = chooseEqualitySource(recordedEqualityLiteral, true);
  if (!foundSource || to.isVar()) {
    bool foundConcreteAlternative = false;
    bool foundFallbackAlternative = false;
    Kernel::Literal* fallbackLiteral = nullptr;
    Kernel::TermList fallbackFrom;
    Kernel::TermList fallbackTo;
    std::vector<std::vector<unsigned>> fallbackPositions;
    for (unsigned i = 0; i < equalityParent->length(); ++i) {
      Kernel::Literal* candidate = (*equalityParent)[i];
      if (candidate == equalityLiteral || !chooseEqualitySource(candidate, false)) {
        continue;
      }
      if (!to.isVar()) {
        foundConcreteAlternative = true;
        break;
      }
      if (!foundFallbackAlternative) {
        foundFallbackAlternative = true;
        fallbackLiteral = equalityLiteral;
        fallbackFrom = from;
        fallbackTo = to;
        fallbackPositions = redexPositions;
      }
    }
    if (!foundConcreteAlternative) {
      if (foundSource) {
        chooseEqualitySource(recordedEqualityLiteral, true);
      } else if (foundFallbackAlternative) {
        equalityLiteral = fallbackLiteral;
        from = fallbackFrom;
        to = fallbackTo;
        redexPositions = fallbackPositions;
      } else {
        return false;
      }
    }
  }
  if (!containsLiteral(equalityParent, equalityLiteral)) {
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

  auto replaceAll = [](std::string& text, const std::string& from, const std::string& to) {
    if (from.empty()) {
      return;
    }
    std::size_t pos = 0;
    while ((pos = text.find(from, pos)) != std::string::npos) {
      text.replace(pos, from.size(), to);
      pos += to.size();
    }
  };
  auto collectJsonVariables = [&](const std::vector<std::string>& clause) {
    std::vector<std::string> variables;
    const std::string marker = "{\"var\":\"";
    for (const std::string& literal : clause) {
      std::size_t pos = 0;
      while ((pos = literal.find(marker, pos)) != std::string::npos) {
        pos += marker.size();
        std::size_t end = literal.find("\"}", pos);
        if (end == std::string::npos) {
          break;
        }
        variables.push_back(literal.substr(pos, end - pos));
        pos = end + 2;
      }
    }
    std::sort(variables.begin(), variables.end());
    variables.erase(std::unique(variables.begin(), variables.end()), variables.end());
    return variables;
  };
  auto applyJsonVariableRenaming =
    [&](const std::vector<std::string>& source,
        const std::vector<std::pair<std::string, std::string>>& renaming) {
      std::vector<std::string> renamed = source;
      for (std::string& literal : renamed) {
        for (std::size_t i = 0; i < renaming.size(); ++i) {
          replaceAll(literal, "{\"var\":" + quote(renaming[i].first) + "}", quote("__mg_var_rename_" + std::to_string(i) + "__"));
        }
        for (std::size_t i = 0; i < renaming.size(); ++i) {
          replaceAll(literal, quote("__mg_var_rename_" + std::to_string(i) + "__"), "{\"var\":" + quote(renaming[i].second) + "}");
        }
      }
      std::sort(renamed.begin(), renamed.end());
      renamed.erase(std::unique(renamed.begin(), renamed.end()), renamed.end());
      return renamed;
    };
  auto findJsonVariableRenaming =
    [&](const std::vector<std::string>& source,
        const std::vector<std::string>& target,
        std::vector<std::pair<std::string, std::string>>& renaming) {
      std::vector<std::string> sourceVars = collectJsonVariables(source);
      std::vector<std::string> targetVars = collectJsonVariables(target);
      renaming.clear();
      if (sourceVars.size() != targetVars.size() || sourceVars.empty() || sourceVars.size() > 7) {
        return false;
      }

      std::vector<std::string> candidateTargets = targetVars;
      do {
        std::vector<std::pair<std::string, std::string>> candidate;
        candidate.reserve(sourceVars.size());
        bool nontrivial = false;
        for (std::size_t i = 0; i < sourceVars.size(); ++i) {
          candidate.push_back({sourceVars[i], candidateTargets[i]});
          nontrivial = nontrivial || sourceVars[i] != candidateTargets[i];
        }
        if (nontrivial && applyJsonVariableRenaming(source, candidate) == target) {
          renaming = candidate;
          return true;
        }
      } while (std::next_permutation(candidateTargets.begin(), candidateTargets.end()));
      return false;
    };
  auto renamingSubstitutionJson = [&](const std::vector<std::pair<std::string, std::string>>& renaming) {
    std::ostringstream out;
    out << '{';
    bool first = true;
    for (const auto& item : renaming) {
      if (item.first == item.second) {
        continue;
      }
      if (!first) {
        out << ',';
      }
      first = false;
      out << quote(item.first) << ":{\"var\":" << quote(item.second) << '}';
    }
    out << '}';
    return out.str();
  };

  auto canNormalizeBySymmetryToTarget = [&](const std::vector<std::string>& source,
                                            const std::vector<std::string>& target,
                                            const std::vector<std::pair<std::string, std::string>>& candidates,
                                            std::vector<std::pair<std::string, std::string>>& flips) {
    std::vector<std::string> current = source;
    flips.clear();
    for (std::size_t guard = 0; current != target && guard < candidates.size(); ++guard) {
      bool changed = false;
      for (const auto& candidate : candidates) {
        if (std::find(target.begin(), target.end(), candidate.second) == target.end()) {
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
    return current == target;
  };
  auto canNormalizeBySymmetry = [&](const std::vector<std::string>& source, std::vector<std::pair<std::string, std::string>>& flips) {
    return canNormalizeBySymmetryToTarget(source, actual, symmetryCandidates, flips);
  };
  auto renamedSymmetryCandidates = [&](const std::vector<std::pair<std::string, std::string>>& renaming) {
    std::vector<std::pair<std::string, std::string>> renamed;
    renamed.reserve(symmetryCandidates.size());
    for (const auto& candidate : symmetryCandidates) {
      std::vector<std::string> first{candidate.first};
      std::vector<std::string> second{candidate.second};
      first = applyJsonVariableRenaming(first, renaming);
      second = applyJsonVariableRenaming(second, renaming);
      if (!first.empty() && !second.empty() && first[0] != second[0]) {
        renamed.push_back({first[0], second[0]});
      }
    }
    return renamed;
  };
  auto findJsonVariableRenamingThenSymmetry =
    [&](const std::vector<std::string>& source,
        const std::vector<std::string>& target,
        std::vector<std::pair<std::string, std::string>>& renaming,
        std::vector<std::pair<std::string, std::string>>& flips) {
      std::vector<std::string> sourceVars = collectJsonVariables(source);
      std::vector<std::string> targetVars = collectJsonVariables(target);
      renaming.clear();
      flips.clear();
      if (sourceVars.size() != targetVars.size() || sourceVars.empty() || sourceVars.size() > 7) {
        return false;
      }

      std::vector<std::string> candidateTargets = targetVars;
      do {
        std::vector<std::pair<std::string, std::string>> candidate;
        candidate.reserve(sourceVars.size());
        bool nontrivial = false;
        for (std::size_t i = 0; i < sourceVars.size(); ++i) {
          candidate.push_back({sourceVars[i], candidateTargets[i]});
          nontrivial = nontrivial || sourceVars[i] != candidateTargets[i];
        }
        if (!nontrivial) {
          continue;
        }
        std::vector<std::string> renamedSource = applyJsonVariableRenaming(source, candidate);
        std::vector<std::pair<std::string, std::string>> renamedCandidates = renamedSymmetryCandidates(candidate);
        std::vector<std::pair<std::string, std::string>> candidateFlips;
        if (canNormalizeBySymmetryToTarget(renamedSource, target, renamedCandidates, candidateFlips)) {
          renaming = candidate;
          flips = candidateFlips;
          return true;
        }
      } while (std::next_permutation(candidateTargets.begin(), candidateTargets.end()));
      return false;
  };
  std::vector<std::pair<std::string, std::string>> finalSymmetryFlips;
  std::vector<std::pair<std::string, std::string>> finalRenaming;
  bool finalRenamingBeforeSymmetry = false;
  bool clauseWideParamodulation = false;
  std::vector<TargetRewrite> targetRewrites;
  if (!canNormalizeBySymmetry(paramClause, finalSymmetryFlips)) {
    finalSymmetryFlips.clear();
    if (!findJsonVariableRenaming(paramClause, actual, finalRenaming)) {
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
        finalSymmetryFlips.clear();
        if (!findJsonVariableRenaming(clauseWideParamClause, actual, finalRenaming)) {
          if (!findJsonVariableRenamingThenSymmetry(clauseWideParamClause, actual, finalRenaming, finalSymmetryFlips)) {
            return false;
          }
          finalRenamingBeforeSymmetry = true;
        }
      }
      clauseWideParamodulation = true;
      paramClause = clauseWideParamClause;
      targetRewrites = clauseWideTargetRewrites;
    } else {
      finalSymmetryFlips.clear();
    }
    if (!finalRenamingBeforeSymmetry && finalRenaming.empty()) {
      std::vector<std::pair<std::string, std::string>> mixedRenaming;
      std::vector<std::pair<std::string, std::string>> mixedFlips;
      if (findJsonVariableRenamingThenSymmetry(paramClause, actual, mixedRenaming, mixedFlips)) {
        finalRenaming = mixedRenaming;
        finalSymmetryFlips = mixedFlips;
        finalRenamingBeforeSymmetry = true;
      }
    }
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
  bool finalRenamingNeeded = !finalRenaming.empty();
  bool finalNormalizationNeeded = !finalSymmetryFlips.empty() || finalRenamingNeeded;
  std::string paramodulateStepId = finalNormalizationNeeded ? stepBase + "_paramodulate" : stepBase;
  std::string paramodulateClauseJson = finalNormalizationNeeded ? jsonArray(paramClause) : conclusionJson;
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
      std::string rewriteStepId = lastRewrite && !finalNormalizationNeeded
        ? stepBase
        : stepBase + "_paramodulate" + std::to_string(rewriteIndex);
      std::string rewriteScopeFields;
      rewriteScopeJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], rewrite.position, rewriteScopeFields);
      std::string rewriteClauseJson = lastRewrite && !finalNormalizationNeeded
        ? conclusionJson
        : jsonArray(currentClause);
      steps.push_back(
        "{\"id\":" + quote(rewriteStepId) + ","
        "\"rule\":\"paramodulate\","
        "\"parents\":["
        + quote(equalityParentId) + ","
        + quote(currentTargetId) + "],"
        "\"equality\":" + equalityJson + ","
        "\"from\":" + fromJson + ","
        "\"to\":" + toJson + ","
        "\"target\":" + rewrite.literalJson + ","
        "\"rewritten_target\":" + rewrite.rewrittenJson + ","
        "\"position\":" + positionJson(rewrite.position) + ","
        + rewriteScopeFields
        + "\"substitution\":{},"
        "\"clause\":" + rewriteClauseJson + "}");
      currentTargetId = rewriteStepId;
    }
    paramClause = currentClause;
    paramodulateStepId = currentTargetId;
  } else {
    if (simultaneousParamodulation) {
      std::vector<std::string> currentParamClause;
      std::vector<std::string> equalityRemainder;
      if (!substitutedClauseLiterals(targetParent, replayInfo->substitutionForBanksSub[targetParentIndex], currentParamClause)
        || !substitutedClauseExceptLiterals(equalityParent, replayInfo->substitutionForBanksSub[equalityParentIndex], equalityLiteral, equalityRemainder)) {
        return false;
      }
      std::string currentTargetId = parentIds[targetParentIndex];
      std::string currentTargetJson = targetJson;
      std::vector<Kernel::TermList> currentArguments;
      if (!substitutedLiteralArgumentTerms(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], currentArguments)) {
        return false;
      }
      for (std::size_t rewriteIndex = 0; rewriteIndex < redexPositions.size(); ++rewriteIndex) {
        const std::vector<unsigned>& rewritePosition = redexPositions[rewriteIndex];
        if (!rewriteArgumentTermsAtPrintedPosition(currentArguments, rewritePosition, to)) {
          return false;
        }
        std::string nextTargetJson;
        if (!literalFromArgumentTermsJson(targetLiteral, currentArguments, nextTargetJson)) {
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
        std::string rewriteStepId = lastRewrite && !finalNormalizationNeeded
          ? stepBase
          : stepBase + "_paramodulate" + std::to_string(rewriteIndex);
        std::string rewriteClauseJson = lastRewrite && !finalNormalizationNeeded
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
      rewriteFields += "\"position\":" + positionJson(position) + ",";
      std::string rewriteScopeFields;
      if (rewriteScopeJson(targetLiteral, replayInfo->substitutionForBanksSub[targetParentIndex], position, rewriteScopeFields)) {
        rewriteFields += rewriteScopeFields;
      }
      steps.push_back(
        "{\"id\":" + quote(paramodulateStepId) + ","
        "\"rule\":\"paramodulate\","
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
  if (finalRenamingNeeded && finalRenamingBeforeSymmetry) {
    std::vector<std::string> renamedClause = applyJsonVariableRenaming(currentClause, finalRenaming);
    if (finalSymmetryFlips.empty() && renamedClause != actual) {
      return false;
    }
    std::string renameStepId = finalSymmetryFlips.empty() ? stepBase : stepBase + "_rename";
    steps.push_back(
      "{\"id\":" + quote(renameStepId) + ","
      "\"rule\":\"substitute\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"substitution\":" + renamingSubstitutionJson(finalRenaming) + ","
      "\"clause\":" + (finalSymmetryFlips.empty() ? conclusionJson : jsonArray(renamedClause)) + "}");
    currentStepId = renameStepId;
    currentClause = renamedClause;
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
    bool lastNormalizationStep = index + 1 == finalSymmetryFlips.size();
    std::string normalizeStepId = lastNormalizationStep
      && (!finalRenamingNeeded || finalRenamingBeforeSymmetry)
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
  if (finalRenamingNeeded && !finalRenamingBeforeSymmetry) {
    std::vector<std::string> renamedClause = applyJsonVariableRenaming(currentClause, finalRenaming);
    if (renamedClause != actual) {
      return false;
    }
    steps.push_back(
      "{\"id\":" + quote(stepBase) + ","
      "\"rule\":\"substitute\","
      "\"parents\":[" + quote(currentStepId) + "],"
      "\"substitution\":" + renamingSubstitutionJson(finalRenaming) + ","
      "\"clause\":" + conclusionJson + "}");
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
        if (!recordEqualitySort(equalityArgumentSort)) {
          return false;
        }
        if (equalitySort == "set") {
          result = lhs + " = " + rhs;
        } else {
          result = equalityNameForSort(equalitySort) + " " + parenthesize(lhs) + " " + parenthesize(rhs);
        }
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
  _equalitySorts.insert("set");
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
    return safeHolApplication(
      *term.term()->nthArgument(0),
      *term.term()->nthArgument(1),
      lhs,
      rhs,
      result);
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
      if (!safeHolApplication(
            *term.term()->nthArgument(0),
            *term.term()->nthArgument(1),
            lhs,
            term.rhs(),
            result)) {
        return false;
      }
      substitution = childSubstitution;
      return true;
    }
    Kernel::TermList rhs;
    if (rewriteTermOnce(term.rhs(), pattern, replacement, variables, childSubstitution, rhs)) {
      if (!safeHolApplication(
            *term.term()->nthArgument(0),
            *term.term()->nthArgument(1),
            term.lhs(),
            rhs,
            result)) {
        return false;
      }
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
  _equalitySorts.clear();
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
    for (const std::string& equalitySort : _equalitySorts) {
      lines.push_back(equalityDefinition(equalitySort));
    }
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
  _equalitySorts.clear();
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
    std::set<std::string> equalitySortsSnapshot = _equalitySorts;
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
      _equalitySorts = equalitySortsSnapshot;
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
    std::set<std::string> equalitySortsSnapshot = _equalitySorts;
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
      _equalitySorts = equalitySortsSnapshot;
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
    for (const std::string& equalitySort : _equalitySorts) {
      lines.push_back(equalityDefinition(equalitySort));
    }
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
  _certificateSteps.clear();
  _certificateNativeMetadata.clear();
  _certificateNativeSteps.clear();
  out << "% Megalodon proof reconstruction output generated by Vampire\n";
  out << "% format: vampire-megalodon-proof-outline-v1\n";
  out << "megalodon_reconstruction_start.\n";
  out << "megalodon_reconstruction_version(1).\n";
  AbstractProofPrinter::print();
  printMegalodonSymbolDeclarations();
  printMegalodonSourceCandidate();
  printMegalodonClaimSkeleton();
  printMegalodonCertificateNativeSexpr();
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
      _certificateNativeMetadata.push_back("(symbol_declaration " + sexprQuote(decl) + ")");
    }
  }
  for (const auto& entry : _predicates) {
    std::string decl = predicateDeclaration(entry.first, entry.second);
    if (!decl.empty()) {
      out << "megalodon_symbol_declaration(" << quote(decl) << ").\n";
      _certificateNativeMetadata.push_back("(symbol_declaration " + sexprQuote(decl) + ")");
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
  std::ostringstream metadata;
  metadata << "(step_variable_sorts " << sexprQuote("u" + std::to_string(u->number())) << " (";
  for (std::size_t i = 0; i < rendered.size(); ++i) {
    if (i != 0) {
      out << ',';
      metadata << ' ';
    }
    out << quote(rendered[i].second);
    metadata << sexprQuote(rendered[i].second);
  }
  out << "]).\n";
  metadata << "))";
  _certificateNativeMetadata.push_back(metadata.str());
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
    _certificateNativeMetadata.push_back(
      "(step_proposition " + sexprQuote("u" + std::to_string(u->number())) + " " + sexprQuote(propositionText) + ")");
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
  if (!u->isClause()) {
    std::string nativeStep;
    bool emittedNativeStep = certificateNativeStepSexpr(u, replayInfo, nativeStep);
    if (!emittedNativeStep
      && (
        rule == Kernel::InferenceRule::AVATAR_SPLIT_CLAUSE
        || rule == Kernel::InferenceRule::AVATAR_CONTRADICTION_CLAUSE
      )) {
      std::string formula;
      if (certificateFormulaTermSexpr(static_cast<Kernel::FormulaUnit*>(u)->formula(), formula)) {
        std::ostringstream out;
        out << (rule == Kernel::InferenceRule::AVATAR_SPLIT_CLAUSE ? "(avatar_split " : "(avatar_contradiction ")
            << sexprQuote("u" + std::to_string(u->number())) << " (parents";
        for (Kernel::Unit* parent : iterTraits(u->getParents())) {
          out << ' ' << sexprQuote("u" + std::to_string(parent->number()));
        }
        out << ") (result (clause (pos " << formula << "))))";
        nativeStep = out.str();
        emittedNativeStep = true;
      }
    }
    if (emittedNativeStep) {
      if (_certificateNativeStepIds.insert(u->number()).second) {
        _certificateNativeSteps.push_back(nativeStep);
      }
    }
  }
  if (u->isClause()) {
    if (emitLegacyMegalodonJsonDiagnostics()) {
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
      bool emittedCertificate = false;
      auto emitCertificateStep = [&](const std::string& stepJson) {
        emittedCertificate = true;
        std::string identifiedStepJson = certificateJsonWithStepIds(u, stepJson);
        _certificateSteps.push_back(identifiedStepJson);
        out << "megalodon_certificate_step("
            << u->number() << ','
            << stepJson
            << ").\n";
      };
      auto emitCertificateSteps = [&](const std::string& stepsJson) {
        emittedCertificate = true;
        std::string identifiedStepsJson = certificateJsonWithStepIds(u, stepsJson);
        _certificateSteps.push_back(identifiedStepsJson);
        out << "megalodon_certificate_steps("
            << u->number() << ','
            << stepsJson
            << ").\n";
      };
      if (certificateDefinitionInputStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (hasNontrivialReplaySubstitution
        && certificateSubstitutedResolutionStepsJson(u, replayInfo, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if ((rule == Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
          || rule == Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION)
        && certificateSubstitutedResolutionStepsJson(u, replayInfo, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if ((rule == Kernel::InferenceRule::FORWARD_SUBSUMPTION_RESOLUTION
          || rule == Kernel::InferenceRule::BACKWARD_SUBSUMPTION_RESOLUTION)
        && certificateSatSubsumptionResolutionStepsJson(u, certificateStep)) {
        if (!certificateStep.empty() && certificateStep.front() == '[') {
          emitCertificateSteps(certificateStep);
        } else {
          emitCertificateStep(certificateStep);
        }
      } else if (certificateResolveStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateUnitResultingResolutionStepsJson(u, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateSubstitutedResolutionStepsJson(u, replayInfo, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateExtensionalityResolutionStepsJson(u, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateSatSubsumptionResolutionStepsJson(u, certificateStep)) {
        if (!certificateStep.empty() && certificateStep.front() == '[') {
          emitCertificateSteps(certificateStep);
        } else {
          emitCertificateStep(certificateStep);
        }
      } else if (certificateTruthConflictResolutionStepJson(u, replayInfo, certificateStep)) {
        if (!certificateStep.empty() && certificateStep.front() == '[') {
          emitCertificateSteps(certificateStep);
        } else {
          emitCertificateStep(certificateStep);
        }
      } else if (certificateTrivialInequalityRemovalStepsJson(u, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateEqualityResolutionStepJson(u, replayInfo, certificateStep)) {
        if (!certificateStep.empty() && certificateStep.front() == '[') {
          emitCertificateSteps(certificateStep);
        } else {
          emitCertificateStep(certificateStep);
        }
      } else if (certificateFactorStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateCondensationStepsJson(u, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateAvatarRefutationStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateDefinitionRewriteChainStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateBoolSimplificationStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateInequalitySplittingStepJson(u, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateEqualityFactoringStepJson(u, replayInfo, certificateStep)) {
        if (!certificateStep.empty() && certificateStep.front() == '[') {
          emitCertificateSteps(certificateStep);
        } else {
          emitCertificateStep(certificateStep);
        }
      } else if (certificateDemodulationStepsJson(u, replayInfo, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateParamodulateStepJson(u, replayInfo, certificateStep)) {
        emitCertificateStep(certificateStep);
      } else if (certificateParamodulateThenSymmetryStepsJson(u, certificateStep)) {
        emitCertificateSteps(certificateStep);
      } else if (certificateSuperpositionStepsJson(u, replayInfo, certificateStep)) {
        emitCertificateSteps(certificateStep);
      }
      if (!emittedCertificate) {
        std::ostringstream fallback;
        fallback << "{\"rule\":\"input\","
                 << "\"source\":" << certificateFallbackSourceJson(u) << "}";
        std::string fallbackStep = certificateJsonWithStepIds(u, fallback.str());
        if (fallbackStep.find("\"clause\"") != std::string::npos) {
          _certificateSteps.push_back(fallbackStep);
        }
      }
    }
    std::string nativeStep;
    if (certificateNativeStepSexpr(u, replayInfo, nativeStep)) {
      if (_certificateNativeStepIds.insert(u->number()).second) {
        _certificateNativeSteps.push_back(nativeStep);
      }
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
