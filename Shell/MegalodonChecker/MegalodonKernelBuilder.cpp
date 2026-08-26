#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Lib/Environment.hpp"

#include <map>
#include <set>
#include <utility>

namespace Shell {
namespace MegalodonKernelBuilder {

namespace {

std::string quote(const std::string& value)
{
  std::string result = "\"";
  for (char ch : value) {
    switch (ch) {
      case '\\': result += "\\\\"; break;
      case '"': result += "\\\""; break;
      case '\n': result += "\\n"; break;
      case '\r': result += "\\r"; break;
      case '\t': result += "\\t"; break;
      default: result += ch; break;
    }
  }
  result += '"';
  return result;
}

MegalodonKernelSyntax::PrimitiveStep primitiveClauseStep(
  const std::string& rule,
  const std::string& id,
  const std::vector<std::string>& parentIds,
  const std::string& resultClause,
  const std::vector<std::pair<std::string, std::string>>& fields,
  const std::string& rendered)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = rule;
  step.id = id;
  step.rendered = rendered;
  step.parentIds = parentIds;
  step.hasResultClause = true;
  step.resultClause = resultClause;
  step.fields = fields;
  return step;
}

}

MegalodonKernelSyntax::PrimitiveStep resolveStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& leftParent,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& rightParent,
  std::size_t leftPivot,
  std::size_t rightPivot,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string leftPivotText = std::to_string(leftPivot);
  const std::string rightPivotText = std::to_string(rightPivot);
  return primitiveClauseStep(
    "resolve",
    id,
    {leftParent.value, rightParent.value},
    result.sexpr,
    {{"pivot_left", leftPivotText}, {"pivot_right", rightPivotText}},
    "(resolve " + quote(id)
      + " (parents " + quote(leftParent.value) + " " + quote(rightParent.value) + ")"
      + " (pivot " + leftPivotText + " " + rightPivotText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep factorStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t leftLiteral,
  std::size_t rightLiteral,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string leftLiteralText = std::to_string(leftLiteral);
  const std::string rightLiteralText = std::to_string(rightLiteral);
  return primitiveClauseStep(
    "factor",
    id,
    {parent.value},
    result.sexpr,
    {{"literal_left", leftLiteralText}, {"literal_right", rightLiteralText}},
    "(factor " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literals " + leftLiteralText + " " + rightLiteralText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep equalitySymmetryStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string literalText = std::to_string(literal);
  return primitiveClauseStep(
    "equality_symmetry",
    id,
    {parent.value},
    result.sexpr,
    {{"literal", literalText}},
    "(equality_symmetry " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep substituteStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelSubstitution& substitution,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  return primitiveClauseStep(
    "substitute",
    id,
    {parent.value},
    result.sexpr,
    {{"substitution", substitution.sexpr}},
    "(substitute " + quote(id)
      + " (parent " + quote(parent.value) + ") " + substitution.sexpr
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep equalityResolutionStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields)
{
  const std::string literalText = std::to_string(literal);
  return primitiveClauseStep(
    "equality_resolution",
    id,
    {parent.value},
    result.sexpr,
    metadataFields,
    "(equality_resolution " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep equalityResolutionConstraintsStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelLiteral& selected,
  const MegalodonKernelSyntax::RenderedKernelClause& constraints,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields)
{
  const std::string literalText = std::to_string(literal);
  return primitiveClauseStep(
    "equality_resolution_constraints",
    id,
    {parent.value},
    result.sexpr,
    metadataFields,
    "(equality_resolution_constraints " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (selected " + selected.sexpr + ")"
      + " (constraints " + constraints.sexpr + ")"
      + " (result " + result.sexpr + "))");
}

namespace {

using KernelSymbol = std::pair<bool, unsigned>;

void collectFormulaSymbols(Kernel::Formula* formula, std::set<KernelSymbol>& symbols);

void collectTermSymbols(Kernel::TermList term, std::set<KernelSymbol>& symbols)
{
  if (term.isVar()) {
    return;
  }
  if (term.isApplication()) {
    collectTermSymbols(term.lhs(), symbols);
    collectTermSymbols(term.rhs(), symbols);
    return;
  }
  if (!term.isTerm()) {
    return;
  }
  Kernel::Term* value = term.term();
  if (value->isSpecial()) {
    const Kernel::Term::SpecialTermData* data = value->getSpecialData();
    switch (value->specialFunctor()) {
      case Kernel::SpecialFunctor::FORMULA:
        collectFormulaSymbols(data->getFormula(), symbols);
        return;
      case Kernel::SpecialFunctor::ITE:
        collectFormulaSymbols(data->getITECondition(), symbols);
        for (unsigned index = 0; index < value->arity(); ++index) {
          collectTermSymbols(*value->nthArgument(index), symbols);
        }
        return;
      case Kernel::SpecialFunctor::LET:
        collectFormulaSymbols(data->getLetBinding(), symbols);
        for (unsigned index = 0; index < value->arity(); ++index) {
          collectTermSymbols(*value->nthArgument(index), symbols);
        }
        return;
      case Kernel::SpecialFunctor::LAMBDA:
        collectTermSymbols(data->getLambdaExp(), symbols);
        return;
      case Kernel::SpecialFunctor::MATCH:
        for (unsigned index = 0; index < value->arity(); ++index) {
          collectTermSymbols(*value->nthArgument(index), symbols);
        }
        return;
    }
  }
  if (!env.signature->getFunction(value->functor())->interpreted()) {
    symbols.insert({true, value->functor()});
  }
  for (unsigned index = 0; index < value->numTermArguments(); ++index) {
    collectTermSymbols(value->termArg(index), symbols);
  }
}

void collectLiteralSymbols(Kernel::Literal* literal, std::set<KernelSymbol>& symbols)
{
  if (!env.signature->getPredicate(literal->functor())->interpreted()) {
    symbols.insert({false, literal->functor()});
  }
  for (unsigned index = 0; index < literal->arity(); ++index) {
    collectTermSymbols(*literal->nthArgument(index), symbols);
  }
}

void collectFormulaSymbols(Kernel::Formula* formula, std::set<KernelSymbol>& symbols)
{
  switch (formula->connective()) {
    case Kernel::LITERAL:
      collectLiteralSymbols(formula->literal(), symbols);
      return;
    case Kernel::AND:
    case Kernel::OR: {
      Kernel::FormulaList::Iterator iterator(formula->args());
      while (iterator.hasNext()) {
        collectFormulaSymbols(iterator.next(), symbols);
      }
      return;
    }
    case Kernel::IMP:
    case Kernel::IFF:
    case Kernel::XOR:
      collectFormulaSymbols(formula->left(), symbols);
      collectFormulaSymbols(formula->right(), symbols);
      return;
    case Kernel::NOT:
      collectFormulaSymbols(formula->uarg(), symbols);
      return;
    case Kernel::FORALL:
    case Kernel::EXISTS:
      collectFormulaSymbols(formula->qarg(), symbols);
      return;
    case Kernel::BOOL_TERM:
      collectTermSymbols(formula->getBooleanTerm(), symbols);
      return;
    case Kernel::TRUE:
    case Kernel::FALSE:
    case Kernel::NAME:
      return;
    default:
      return;
  }
}

}

std::vector<MegalodonKernelSyntax::RenderedKernelSkolemBranchScopeSymbol>
sourceSignatureScope(
  Kernel::Formula* formula,
  const std::function<std::string(unsigned)>& functionName,
  const std::function<std::string(unsigned)>& predicateName)
{
  std::set<KernelSymbol> symbols;
  collectFormulaSymbols(formula, symbols);
  std::map<std::string, std::string> scopedNames;
  for (const KernelSymbol& symbol : symbols) {
    const std::string name = symbol.first
      ? functionName(symbol.second)
      : predicateName(symbol.second);
    if (!name.empty()) {
      const Kernel::Signature::Symbol* signatureSymbol = symbol.first
        ? env.signature->getFunction(symbol.second)
        : env.signature->getPredicate(symbol.second);
      const std::string role = signatureSymbol->introduced()
        ? "source_vampire_introduced"
        : "source_input_signature";
      auto existing = scopedNames.find(name);
      if (existing == scopedNames.end() || role == "source_input_signature") {
        scopedNames[name] = role;
      }
    }
  }
  std::vector<MegalodonKernelSyntax::RenderedKernelSkolemBranchScopeSymbol> result;
  for (const auto& entry : scopedNames) {
    result.push_back({result.size(), entry.first, entry.second});
  }
  return result;
}

}
}
