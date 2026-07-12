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
 * @file ProofExtra.hpp
 * Various objects that include "extra information" about an inference,
 * e.g. selected literals, unifier, etc.
 *
 * @since 09/09/2024 Oxford
 */

#ifndef __Inferences_ProofExtra__
#define __Inferences_ProofExtra__


#include "Kernel/Term.hpp"
#include "Lib/ProofExtra.hpp"

#include <vector>
#include <utility>

namespace Inferences {

// inferences that use one literal from their main premise
struct LiteralInferenceExtra : public InferenceExtra {
  LiteralInferenceExtra(Kernel::Literal *selected) : selectedLiteral(selected) {}

  void output(std::ostream &out) const override;

  // the literal from the main premise
  Kernel::Literal *selectedLiteral;
};

// inferences that use one literal from their side premise
struct TwoLiteralInferenceExtra : public InferenceExtra {

  struct SynthesisExtra {
    SynthesisExtra(Kernel::Literal *conditionLiteral, Kernel::Literal *thenLiteral, Kernel::Literal* elseLiteral) : condition(conditionLiteral), thenLit(thenLiteral), elseLit(elseLiteral) {}
    Kernel::Literal *condition;
    Kernel::Literal *thenLit;
    Kernel::Literal *elseLit;
  };

  TwoLiteralInferenceExtra(Kernel::Literal *selected, Kernel::Literal *other, Kernel::Literal *condition = nullptr, Kernel::Literal* thenLit = nullptr, Kernel::Literal* elseLit = nullptr)
    : selectedLiteral(selected), otherLiteral(other), synthesisExtra(condition, thenLit, elseLit) {}

  void output(std::ostream &out) const override;

  // selected literal
  LiteralInferenceExtra selectedLiteral;
  // the literal from the side premise
  Kernel::Literal *otherLiteral;
  // synthesis information: condition and branch literals for if-then-else
  SynthesisExtra synthesisExtra;
};

struct RewriteInferenceExtra : public InferenceExtra {
  RewriteInferenceExtra(Kernel::TermList lhs, Kernel::TermList target)
    : lhs(lhs), rewritten(target) {}

  RewriteInferenceExtra(
    Kernel::TermList lhs,
    Kernel::TermList target,
    Kernel::TermList rhs,
    Kernel::TermList replacement)
    : lhs(lhs),
      rewritten(target),
      rhs(rhs),
      replacement(replacement),
      hasRhs(true),
      hasReplacement(true) {}

  void output(std::ostream &out) const override;

  // the LHS used to rewrite with
  Kernel::TermList lhs;
  // the rewritten term
  Kernel::TermList rewritten;
  // the RHS of the rewrite rule before instantiation, if available
  Kernel::TermList rhs;
  // the replacement term after instantiation, if available
  Kernel::TermList replacement;
  bool hasRhs = false;
  bool hasReplacement = false;
};

struct CNFTransformationInferenceExtra : public InferenceExtra {
  CNFTransformationInferenceExtra(unsigned int number)
    : number(number) {}

  void output(std::ostream &out) const override;

  // the rewrite information for the transformation
  unsigned number;
};

struct CNFClauseInferenceExtra : public InferenceExtra {
  CNFClauseInferenceExtra(unsigned int parentNumber, unsigned int index, unsigned int count)
    : parentNumber(parentNumber), index(index), count(count) {}

  void output(std::ostream &out) const override;

  unsigned parentNumber;
  unsigned index;
  unsigned count;
};

struct TwoLiteralRewriteInferenceExtra : public InferenceExtra {
  TwoLiteralRewriteInferenceExtra(
    Kernel::Literal *selected,
    Kernel::Literal *other,
    Kernel::TermList lhs,
    Kernel::TermList rewritten,
    Kernel::Literal *condition = nullptr,
    Kernel::Literal *thenLit = nullptr,
    Kernel::Literal *elseLit = nullptr)
    : selected(selected, other, condition, thenLit, elseLit), rewrite(lhs, rewritten) {}
  void output(std::ostream &out) const override;

  // selected literals
  TwoLiteralInferenceExtra selected;
  // rewrite information
  RewriteInferenceExtra rewrite;
};

struct UnitResultingResolutionExtra : public InferenceExtra {
  struct Step {
    Step(
      Kernel::Literal* selected,
      Kernel::Literal* selectedSubstituted,
      Kernel::Clause* unitParent,
      Kernel::Literal* unitSubstituted)
      : selected(selected),
        selectedSubstituted(selectedSubstituted),
        unitParent(unitParent),
        unitSubstituted(unitSubstituted) {}

    Kernel::Literal* selected;
    Kernel::Literal* selectedSubstituted;
    Kernel::Clause* unitParent;
    Kernel::Literal* unitSubstituted;
  };

  UnitResultingResolutionExtra(
    Kernel::Clause* mainParent,
    std::vector<Step> steps,
    std::vector<Kernel::Literal*> remaining)
    : mainParent(mainParent), steps(std::move(steps)), remaining(std::move(remaining)) {}

  void output(std::ostream &out) const override;

  Kernel::Clause* mainParent;
  std::vector<Step> steps;
  std::vector<Kernel::Literal*> remaining;
};
} // namespace Inferences

#endif
