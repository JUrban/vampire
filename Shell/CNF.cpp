/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */
/**
 * @file CNF.cpp
 * Implements class CNF implementing CNF transformation.
 * @since 19/01/2004 Manchester
 * @since 27/12/2007 Manchester, changed completely to a new implementation
 */


#include "Inferences/ProofExtra.hpp"
#include "Kernel/Clause.hpp"
#include "Kernel/Formula.hpp"
#include "Kernel/Inference.hpp"
#include "Kernel/FormulaUnit.hpp"
#include "Lib/Environment.hpp"
#include "Lib/ProofExtra.hpp"
#include "Shell/Options.hpp"
#include "CNF.hpp"

#include <set>
#include <vector>

using namespace Kernel;
using namespace Shell;

namespace {

using Inferences::CNFProjection;
using Inferences::CNFProjectionKind;

std::vector<Formula*> cnfProjectionArguments(Formula* formula)
{
  std::vector<Formula*> result;
  FormulaList::Iterator iterator(formula->args());
  while (iterator.hasNext()) {
    result.push_back(iterator.next());
  }
  return result;
}

std::size_t cnfProjectionClauseCount(Formula* formula)
{
  switch (formula->connective()) {
  case LITERAL:
  case FALSE:
    return 1;
  case FORALL:
    return cnfProjectionClauseCount(formula->qarg());
  case AND: {
    std::size_t count = 0;
    for (Formula* argument : cnfProjectionArguments(formula)) {
      count += cnfProjectionClauseCount(argument);
    }
    return count;
  }
  case OR: {
    std::size_t count = 1;
    for (Formula* argument : cnfProjectionArguments(formula)) {
      count *= cnfProjectionClauseCount(argument);
    }
    return count;
  }
  default:
    ASSERTION_VIOLATION_REP(formula->toString());
  }
}

CNFProjection cnfProjectionForFormula(
  Formula* formula,
  std::size_t clauseIndex,
  const std::set<unsigned>& resultVariables);

CNFProjection cnfProjectionForAndArguments(
  const std::vector<Formula*>& arguments,
  std::size_t first,
  std::size_t selected,
  std::size_t clauseIndex,
  const std::set<unsigned>& resultVariables)
{
  ASS_L(first, arguments.size());
  if (first + 1 == arguments.size()) {
    ASS_EQ(first, selected);
    return cnfProjectionForFormula(
      arguments[first],
      clauseIndex,
      resultVariables);
  }
  if (first == selected) {
    CNFProjection projection(CNFProjectionKind::AND_LEFT);
    projection.children.push_back(cnfProjectionForFormula(
      arguments[first],
      clauseIndex,
      resultVariables));
    return projection;
  }
  CNFProjection projection(CNFProjectionKind::AND_RIGHT);
  projection.children.push_back(cnfProjectionForAndArguments(
    arguments,
    first + 1,
    selected,
    clauseIndex,
    resultVariables));
  return projection;
}

CNFProjection cnfProjectionForOrArguments(
  const std::vector<Formula*>& arguments,
  std::size_t first,
  std::size_t clauseIndex,
  const std::set<unsigned>& resultVariables)
{
  ASS_L(first, arguments.size());
  if (first + 1 == arguments.size()) {
    return cnfProjectionForFormula(
      arguments[first],
      clauseIndex,
      resultVariables);
  }
  const std::size_t leftCount =
    cnfProjectionClauseCount(arguments[first]);
  ASS_G(leftCount, 0);
  CNFProjection projection(CNFProjectionKind::OR);
  projection.children.push_back(cnfProjectionForFormula(
    arguments[first],
    clauseIndex % leftCount,
    resultVariables));
  projection.children.push_back(cnfProjectionForOrArguments(
    arguments,
    first + 1,
    clauseIndex / leftCount,
    resultVariables));
  return projection;
}

CNFProjection cnfProjectionForFormula(
  Formula* formula,
  std::size_t clauseIndex,
  const std::set<unsigned>& resultVariables)
{
  ASS_L(clauseIndex, cnfProjectionClauseCount(formula));
  switch (formula->connective()) {
  case FALSE:
    ASS_EQ(clauseIndex, 0);
    return CNFProjection(CNFProjectionKind::FALSE_FORMULA);
  case LITERAL: {
    ASS_EQ(clauseIndex, 0);
    CNFProjection projection(CNFProjectionKind::LITERAL);
    projection.sourceLiteral = formula->literal();
    return projection;
  }
  case FORALL: {
    CNFProjection projection = cnfProjectionForFormula(
      formula->qarg(),
      clauseIndex,
      resultVariables);
    std::vector<std::pair<unsigned, TermList>> variables;
    VSList::Iterator iterator(formula->vars());
    while (iterator.hasNext()) {
      variables.push_back(iterator.next());
    }
    for (auto iterator = variables.rbegin(); iterator != variables.rend(); ++iterator) {
      CNFProjection quantified(CNFProjectionKind::FORALL);
      quantified.hasVariable = true;
      quantified.variable = iterator->first;
      quantified.variableSort = iterator->second;
      if (resultVariables.find(iterator->first) != resultVariables.end()) {
        quantified.hasWitnessTerm = true;
        quantified.witnessTerm = TermList::var(iterator->first);
      }
      quantified.children.push_back(std::move(projection));
      projection = std::move(quantified);
    }
    return projection;
  }
  case AND: {
    const auto arguments = cnfProjectionArguments(formula);
    std::size_t selected = 0;
    std::size_t selectedIndex = clauseIndex;
    while (selected < arguments.size()) {
      const std::size_t count = cnfProjectionClauseCount(arguments[selected]);
      if (selectedIndex < count) {
        break;
      }
      selectedIndex -= count;
      ++selected;
    }
    ASS_L(selected, arguments.size());
    return cnfProjectionForAndArguments(
      arguments,
      0,
      selected,
      selectedIndex,
      resultVariables);
  }
  case OR: {
    const auto arguments = cnfProjectionArguments(formula);
    return cnfProjectionForOrArguments(
      arguments,
      0,
      clauseIndex,
      resultVariables);
  }
  default:
    ASSERTION_VIOLATION_REP(formula->toString());
  }
}

CNFProjection cnfProjection(
  Formula* formula,
  std::size_t clauseIndex,
  Clause* resultClause)
{
  std::set<unsigned> resultVariables;
  auto variableIterator = resultClause->getVariableIterator();
  while (variableIterator.hasNext()) {
    resultVariables.insert(variableIterator.next());
  }
  return cnfProjectionForFormula(
    formula,
    clauseIndex,
    resultVariables);
}

}

/**
 * Initialise the CNF object.
 * @since 27/12/2007 Manchester
 */
CNF::CNF()
  : _literals(16),
    _formulas(16)
{
} // CNF::CNF

/**
 * Convert @b unit to CNF and push the resulting clauses on @b stack
 * @pre @b unit must be a formula unit
 * @since 27/12/2007 Manchester
 */
void CNF::clausify (Unit* unit,Stack<Clause*>& stack)
{
  ASS(! unit->isClause());

  size_t firstResult = stack.size();
  _unit = static_cast<FormulaUnit*>(unit);
  _result = &stack;
  _literals.reset();
  _formulas.reset();

  Formula* f = _unit->formula();
  switch (f->connective()) {
  case TRUE:
    return;
  case FALSE:
    {
      stack.push(Clause::empty(FormulaClauseTransformation(InferenceRule::CLAUSIFY,unit)));
      if(env.options->proofExtra() == Options::ProofExtra::LEAN){
        env.proofExtra.insert(unit, new Inferences::CNFTransformationInferenceExtra(1));
        env.proofExtra.insert(
          stack[firstResult],
          new Inferences::CNFClauseInferenceExtra(
            unit->number(),
            0,
            1,
            cnfProjection(f, 0, stack[firstResult])));
      }
    }
    return;
  default:
    clausify(f);
  }
  if(env.options->proofExtra() == Options::ProofExtra::LEAN){
    size_t count = _result->size() - firstResult;
    env.proofExtra.insert(unit, new Inferences::CNFTransformationInferenceExtra(count));
    for (size_t i = 0; i < count; ++i) {
      Clause* clause = (*_result)[firstResult + i];
      env.proofExtra.insert(
        clause,
        new Inferences::CNFClauseInferenceExtra(
          unit->number(),
          i,
          count,
          cnfProjection(f, i, clause)));
    }
  }
} // CNF::clausify()


/**
 * Clausify the formula f \/ F1 \/ ... \/ Fn \/ L1 \/ ... \/ Lm,
 * where [F1,...,Fn] is the content of _formulas and [L1,...,Lm]
 * is the content of _literals. After the clausification restore
 * the stacks _formulas and _literals to their state before the call.
 *
 * @since 27/12/2007 Manchester
 */
/*
void CNF::clausify_rec (Formula* f)
{
  switch (f->connective()) {
  case LITERAL:
    _literals.push(f->literal());
    if (_formulas.isEmpty()) {
      // collect the clause
      int length = _literals.length();
      Clause* clause = new(length) Clause(length,
          FormulaClauseTransformation(InferenceRule::CLAUSIFY,_unit));
      for (int i = length-1;i >= 0;i--) {
	      (*clause)[i] = _literals[i];
      }
      _result->push(clause);
    }
    else {
      f = _formulas.pop();
      clausify_rec(f);
      _formulas.push(f);
    }
    _literals.pop();
    return;

  case AND:
    {
      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	      clausify_rec(fs.next());
      }
    }
    return;

  case OR:
    {
      int ln = _formulas.length();

      FormulaList::Iterator fs(f->args());
      while (fs.hasNext()) {
	      _formulas.push(fs.next());
      }
      clausify_rec(_formulas.pop());
      _formulas.truncate(ln);
    }
    return;

  case FORALL:
    clausify_rec(f->qarg());
    return;

  default:
    ASSERTION_VIOLATION;
  }
}*/ // CNF::clausify

/**
 * A recursion-free implementation of the above.
 */
void CNF::clausify(Formula* f)
{
  enum TodoTag {
    MAIN,     // needs a Formula*
    LIT_REST, // needs a Formula*
    AND_REST, // needs a FormulaList*
    OR_REST,  // needs an int
  };
  union TodoVal {
    Formula* aFla;
    FormulaList* aFlist;
    int anInt;
  };

  Stack<std::pair<TodoTag,TodoVal>> todo;
  todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,{.aFla = f}));
  do {
    ASS(todo.isNonEmpty());
    auto task = todo.pop();

    switch(task.first) {
      case MAIN: {
        Formula* f = task.second.aFla;

        formula_reset:

        switch (f->connective()) {
        case LITERAL:
          _literals.push(f->literal());
          if (_formulas.isEmpty()) {
            // collect the clause
            _result->push(Clause::fromStack(_literals,
                FormulaClauseTransformation(InferenceRule::CLAUSIFY,_unit)));
            _literals.pop();
          }
          else {
            f = _formulas.pop();
            todo.push(std::make_pair<TodoTag,TodoVal>(LIT_REST,
              {.aFla = f}));
            todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
              {.aFla = f}));
          }
          break;

        case AND:
          {
            FormulaList* fl = f->args();
            if (FormulaList::isNonEmpty(fl)) {
              todo.push(std::make_pair<TodoTag,TodoVal>(AND_REST,
                {.aFlist = fl->tail()}));
              todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
                {.aFla = fl->head()}));
            }
          }
          break;

        case OR:
          {
            int ln = _formulas.length();
            FormulaList::Iterator fs(f->args());
            while (fs.hasNext()) {
              _formulas.push(fs.next());
            }
            todo.push(std::make_pair<TodoTag,TodoVal>(OR_REST,
              {.anInt = ln}));
            todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
              {.aFla = _formulas.pop()}));
          }
          break;

        case FORALL:
          f = f->qarg();
          goto formula_reset;

        default:
          ASSERTION_VIOLATION;
        }

        break;
      }
      case LIT_REST: {
        Formula* f = task.second.aFla;
        _formulas.push(f);
        _literals.pop();
        break;
      }
      case AND_REST: {
        FormulaList* fl = task.second.aFlist;
        if (FormulaList::isNonEmpty(fl)) {
          todo.push(std::make_pair<TodoTag,TodoVal>(AND_REST,
            {.aFlist = fl->tail()}));
          todo.push(std::make_pair<TodoTag,TodoVal>(MAIN,
            {.aFla = fl->head()}));
        }
        break;
      }
      case OR_REST: {
        int ln = task.second.anInt;
        _formulas.truncate(ln);
        break;
      }
    }
  } while(todo.isNonEmpty());
}
