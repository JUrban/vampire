#include "Shell/MegalodonChecker/MegalodonProofExpander.hpp"

#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"

#include <algorithm>
#include <functional>
#include <map>

namespace Shell {
namespace MegalodonProofExpander {

namespace {

void setBinding(Environment& environment, unsigned variable, Kernel::TermList term)
{
  auto existing = std::find_if(
    environment.begin(),
    environment.end(),
    [variable](const auto& binding) { return binding.first == variable; });
  if (existing == environment.end()) {
    environment.push_back({variable, term});
  } else {
    existing->second = term;
  }
  std::sort(
    environment.begin(),
    environment.end(),
    [](const auto& left, const auto& right) {
      return left.first < right.first;
    });
}

Kernel::TermList applyEnvironment(
  Kernel::TermList term,
  const Environment& environment)
{
  Kernel::Substitution substitution;
  for (const auto& binding : environment) {
    substitution.rebind(binding.first, binding.second);
  }
  return Kernel::SubstHelper::apply(term, substitution);
}

Environment composeParentEnvironment(
  const Environment& childEnvironment,
  const Environment& parentSubstitution)
{
  Environment result = childEnvironment;
  for (const auto& binding : parentSubstitution) {
    setBinding(
      result,
      binding.first,
      applyEnvironment(binding.second, childEnvironment));
  }
  for (auto& binding : result) {
    binding.second = applyEnvironment(binding.second, result);
  }
  return result;
}

bool sameEnvironment(const Environment& left, const Environment& right)
{
  return left == right;
}

}

bool expandGroundProof(
  const std::vector<Step>& steps,
  const std::string& finalStep,
  Expansion& result,
  std::string& error)
{
  std::map<std::string, const Step*> stepById;
  for (const auto& step : steps) {
    if (step.id.empty() || !stepById.emplace(step.id, &step).second) {
      error = "primitive proof contains a missing or duplicate step ID";
      return false;
    }
  }
  if (stepById.find(finalStep) == stepById.end()) {
    error = "primitive proof does not contain its final step";
    return false;
  }

  result = Expansion{"ivy_ground_v1", finalStep, {}};
  std::vector<bool> active;
  std::function<bool(const std::string&, const Environment&, std::size_t&)>
    visit = [&](const std::string& stepId,
                const Environment& environment,
                std::size_t& resultIndex) {
      for (const auto& instance : result.instances) {
        if (instance.stepId == stepId
            && sameEnvironment(instance.environment, environment)) {
          resultIndex = instance.index;
          return true;
        }
      }
      auto found = stepById.find(stepId);
      if (found == stepById.end()) {
        error = "primitive proof instance references unknown parent " + stepId;
        return false;
      }
      resultIndex = result.instances.size();
      result.instances.push_back(
        Instance{resultIndex, stepId, environment, {}, {}});
      active.push_back(true);

      const Step& step = *found->second;
      for (const auto& application : step.applications) {
        Kernel::TermList grounded =
          applyEnvironment(application.term, environment);
        if (!grounded.ground()) {
          error = "proof instance " + stepId
            + " retains a variable in a Skolem application";
          return false;
        }
        const auto duplicate = std::find_if(
          result.instances[resultIndex].applications.begin(),
          result.instances[resultIndex].applications.end(),
          [&](const Application& existing) {
            return existing.functionSymbol == application.functionSymbol
              && existing.term == grounded;
          });
        if (duplicate == result.instances[resultIndex].applications.end()) {
          result.instances[resultIndex].applications.push_back(
            Application{application.functionSymbol, grounded});
        }
      }

      const Environment parentEnvironment =
        composeParentEnvironment(environment, step.parentSubstitution);
      for (const std::string& parentId : step.parentIds) {
        std::size_t parentIndex = 0;
        if (!visit(parentId, parentEnvironment, parentIndex)) {
          return false;
        }
        if (parentIndex < active.size() && active[parentIndex]) {
          error = "primitive proof instance graph contains a cycle";
          return false;
        }
        result.instances[resultIndex].parentInstances.push_back(parentIndex);
      }
      active[resultIndex] = false;
      return true;
    };

  std::size_t rootIndex = 0;
  if (!visit(finalStep, {}, rootIndex)) {
    return false;
  }
  if (rootIndex != 0) {
    error = "primitive proof expansion did not allocate the root first";
    return false;
  }
  return true;
}

bool expandClauseProof(
  const std::vector<ClauseStepRequest>& requests,
  const std::string& finalStep,
  ClauseExpansion& result,
  std::string& error)
{
  result = ClauseExpansion{};
  if (requests.empty()) {
    error = "clausal primitive expansion is empty";
    return false;
  }

  for (const ClauseStepRequest& request : requests) {
    MegalodonKernelSyntax::PrimitiveStep primitive;
    if (const auto* step =
          std::get_if<SubstituteClauseStep>(&request.step)) {
      primitive = MegalodonKernelBuilder::substituteStep(
        step->id,
        step->parent,
        step->substitution,
        step->result);
    } else if (const auto* step =
                 std::get_if<EqualitySymmetryClauseStep>(&request.step)) {
      primitive = MegalodonKernelBuilder::equalitySymmetryStep(
        step->id,
        step->parent,
        step->literal,
        step->result);
    } else if (const auto* step =
                 std::get_if<ParamodulateClauseStep>(&request.step)) {
      primitive = MegalodonKernelBuilder::paramodulateStep(
        step->id,
        step->equalityParent,
        step->equalityLiteral,
        step->targetParent,
        step->targetLiteral,
        step->position,
        step->from,
        step->to,
        step->result);
    } else if (const auto* step =
                 std::get_if<FactorClauseStep>(&request.step)) {
      primitive = MegalodonKernelBuilder::factorStep(
        step->id,
        step->parent,
        step->leftLiteral,
        step->rightLiteral,
        step->result);
    }

    std::string rendered = primitive.rendered;
    for (const std::string& record : request.trailingRecords) {
      rendered += "\n  " + record;
    }
    result.renderedSteps.push_back(std::move(rendered));
    result.primitives.push_back(std::move(primitive));
  }

  std::vector<std::string> validationFields;
  if (!MegalodonKernelSyntax::appendPrimitiveExpansionChainFields(
        validationFields,
        result.primitives,
        finalStep)) {
    result = ClauseExpansion{};
    error = "clausal primitive expansion is not a connected final-step chain";
    return false;
  }
  return true;
}

}
}
