/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable
 * copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#ifndef __TweeGoalTransformation__
#define __TweeGoalTransformation__

#include "Forwards.hpp"
#include "Kernel/Term.hpp"
#include "Lib/ProofExtra.hpp"

#include <utility>
#include <vector>

namespace Shell {

struct TweeDefinitionFoldingExtra : public InferenceExtra {
  std::vector<std::pair<Kernel::TermList, Kernel::TermList>> steps;

  explicit TweeDefinitionFoldingExtra(std::vector<std::pair<Kernel::TermList, Kernel::TermList>> steps)
    : steps(std::move(steps)) {}

  void output(std::ostream& out) const override;
};

class TweeGoalTransformation {
public:
  void apply(Kernel::Problem &, bool grounOnly);
};

};

#endif /* __TweeGoalTransformation__ */
