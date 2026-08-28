#include "Shell/MegalodonChecker/MegalodonProofExpander.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"
#include "Lib/DHMap.hpp"

#include <algorithm>
#include <functional>
#include <map>
#include <set>
#include <sstream>

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
  return result;
}

void closeEnvironment(Environment& environment)
{
  for (std::size_t pass = 0; pass <= environment.size(); ++pass) {
    bool changed = false;
    for (auto& binding : environment) {
      Kernel::TermList normalized = applyEnvironment(binding.second, environment);
      if (normalized != binding.second) {
        binding.second = normalized;
        changed = true;
      }
    }
    if (!changed) {
      return;
    }
  }
}

const Kernel::TermList* findGroundTerm(
  Kernel::TermList sort,
  const std::vector<GroundTerm>& groundTerms,
  const Step& step,
  const Environment& environment)
{
  auto found = std::find_if(
    groundTerms.begin(),
    groundTerms.end(),
    [&](const GroundTerm& candidate) {
      return candidate.sort == sort
        && candidate.term.ground()
        && (!candidate.requiresExistingApplication
            || std::any_of(
              environment.begin(),
              environment.end(),
              [&](const auto& binding) {
                return binding.second == candidate.term;
              })
            || std::any_of(
              step.applications.begin(),
              step.applications.end(),
              [&](const Application& application) {
                return application.functionSymbol == candidate.functionSymbol
                  && application.term == candidate.term;
              }));
    });
  return found == groundTerms.end() ? nullptr : &found->term;
}

void rememberVariableSort(
  VariableSorts& sorts,
  unsigned variable,
  Kernel::TermList sort)
{
  auto found = std::find_if(
    sorts.begin(),
    sorts.end(),
    [&](const auto& binding) { return binding.first == variable; });
  if (found == sorts.end()) {
    sorts.push_back({variable, sort});
  }
}

void rememberTermVariableSorts(
  Kernel::TermList term,
  VariableSorts& sorts)
{
  if (!term.isTerm()) {
    return;
  }
  Lib::DHMap<unsigned, Kernel::TermList> collected;
  Kernel::SortHelper::collectVariableSorts(term.term(), collected);
  Lib::DHMap<unsigned, Kernel::TermList>::Iterator iterator(collected);
  while (iterator.hasNext()) {
    unsigned variable;
    Kernel::TermList sort;
    iterator.next(variable, sort);
    rememberVariableSort(sorts, variable, sort);
  }
}

bool groundEnvironment(
  const Step& step,
  const Environment& incoming,
  bool parametric,
  const std::vector<GroundTerm>& groundTerms,
  Environment& result,
  std::string& error)
{
  VariableSorts relevant = step.freeVariableSorts;
  for (const auto& application : step.applications) {
    if (application.requiresGrounding) {
      rememberTermVariableSorts(application.term, relevant);
    }
  }
  for (const auto& binding : step.parentSubstitution) {
    rememberTermVariableSorts(binding.second, relevant);
  }

  result = incoming;
  result.erase(
    std::remove_if(
      result.begin(),
      result.end(),
      [&](const auto& binding) {
        return std::none_of(
          relevant.begin(),
          relevant.end(),
          [&](const auto& variable) {
            return variable.first == binding.first;
          });
      }),
    result.end());

  if (parametric) {
    result.erase(
      std::remove_if(
        result.begin(),
        result.end(),
        [](const auto& binding) { return !binding.second.ground(); }),
      result.end());
  }
  closeEnvironment(result);

  for (const auto& binding : result) {
    auto expected = std::find_if(
      step.freeVariableSorts.begin(),
      step.freeVariableSorts.end(),
      [&](const auto& variable) { return variable.first == binding.first; });
    Kernel::TermList actualSort;
    if (expected != step.freeVariableSorts.end()
        && binding.second.ground()
        && Kernel::SortHelper::tryGetResultSort(binding.second, actualSort)
        && actualSort != expected->second) {
      std::ostringstream expectedText;
      std::ostringstream actualText;
      expectedText << expected->second;
      actualText << actualSort;
      error = "proof instance " + step.id + " binds X"
        + std::to_string(binding.first) + " at sort " + expectedText.str()
        + " to a term of sort " + actualText.str();
      return false;
    }
  }

  if (parametric) {
    return true;
  }

  VariableSorts needed = step.freeVariableSorts;
  for (const auto& binding : result) {
    auto bindingSort = std::find_if(
      step.freeVariableSorts.begin(),
      step.freeVariableSorts.end(),
      [&](const auto& item) { return item.first == binding.first; });
    if (binding.second.isVar() && bindingSort != step.freeVariableSorts.end()) {
      rememberVariableSort(needed, binding.second.var(), bindingSort->second);
    } else {
      rememberTermVariableSorts(binding.second, needed);
    }
  }
  for (const auto& application : step.applications) {
    if (application.requiresGrounding) {
      rememberTermVariableSorts(application.term, needed);
    }
  }

  Environment completion;
  for (const auto& variable : needed) {
    const Kernel::TermList* groundTerm =
      findGroundTerm(variable.second, groundTerms, step, result);
    if (groundTerm == nullptr) {
      std::ostringstream renderedSort;
      renderedSort << variable.second;
      error = "proof instance " + step.id
        + " has no producer ground inhabitant for variable X"
        + std::to_string(variable.first)
        + " of sort " + renderedSort.str();
      return false;
    }
    setBinding(completion, variable.first, *groundTerm);
    auto existing = std::find_if(
      result.begin(),
      result.end(),
      [&](const auto& binding) { return binding.first == variable.first; });
    const bool isStepVariable = std::any_of(
      step.freeVariableSorts.begin(),
      step.freeVariableSorts.end(),
      [&](const auto& item) { return item.first == variable.first; });
    if (existing == result.end() && isStepVariable) {
      setBinding(result, variable.first, *groundTerm);
    }
  }
  for (auto& binding : result) {
    binding.second = applyEnvironment(binding.second, completion);
  }
  closeEnvironment(result);
  for (const auto& binding : result) {
    if (!binding.second.ground()) {
      error = "proof instance " + step.id
        + " retains a variable after typed grounding";
      return false;
    }
  }
  return true;
}

bool sameEnvironment(const Environment& left, const Environment& right)
{
  return left == right;
}

using ApplicationArities = std::map<unsigned, std::size_t>;
using FunctionDefinitions = std::map<unsigned, const FunctionDefinition*>;

std::size_t applicationArity(Kernel::TermList term)
{
  std::size_t arity = 0;
  while (term.isApplication()) {
    ++arity;
    term = term.lhs();
  }
  return arity;
}

bool rememberGroundApplications(
  Kernel::TermList term,
  const ApplicationArities& arities,
  const FunctionDefinitions& definitions,
  std::set<unsigned>& expandingDefinitions,
  std::vector<Application>& applications,
  std::string& error)
{
  Kernel::TermList head = term;
  while (head.isApplication()) {
    head = head.lhs();
  }
  if (head.isTerm() && head.term()->arity() == 0) {
    const unsigned functionSymbol = head.term()->functor();
    auto expected = arities.find(functionSymbol);
    if (expected != arities.end()
        && applicationArity(term) == expected->second
        && term.ground()
        && std::none_of(
          applications.begin(),
          applications.end(),
          [&](const Application& existing) {
            return existing.functionSymbol == functionSymbol
              && existing.term == term;
          })) {
      applications.push_back(Application{functionSymbol, term});
    }
  }

  if (head.isTerm() && !head.term()->isSpecial()) {
    auto definition = definitions.find(head.term()->functor());
    if (definition != definitions.end()) {
      std::vector<Kernel::TermList> arguments;
      for (unsigned index = 0;
           index < head.term()->numTermArguments();
           ++index) {
        arguments.push_back(*head.term()->nthArgument(index));
      }
      Kernel::TermList outer = term;
      std::vector<Kernel::TermList> outerArguments;
      while (outer.isApplication()) {
        outerArguments.push_back(outer.rhs());
        outer = outer.lhs();
      }
      std::reverse(outerArguments.begin(), outerArguments.end());
      arguments.insert(
        arguments.end(), outerArguments.begin(), outerArguments.end());
      if (arguments.size() != definition->second->parameters.size()) {
        error = "producer function definition is not fully applied while expanding a ground Ivy instance";
        return false;
      }
      expandingDefinitions.insert(definition->first);
      Kernel::Substitution substitution;
      for (std::size_t index = 0; index < arguments.size(); ++index) {
        substitution.rebind(
          definition->second->parameters[index], arguments[index]);
      }
      Kernel::TermList expanded = Kernel::SubstHelper::apply(
        definition->second->body, substitution);
      expandingDefinitions.erase(definition->first);
      if (!rememberGroundApplications(
            expanded,
            arities,
            definitions,
            expandingDefinitions,
            applications,
            error)) {
        return false;
      }
      return true;
    }
  }

  if (term.isVar()) {
    return true;
  }
  if (term.isApplication()) {
    return rememberGroundApplications(
             term.lhs(), arities, definitions, expandingDefinitions,
             applications, error)
      && rememberGroundApplications(
           term.rhs(), arities, definitions, expandingDefinitions,
           applications, error);
  }
  Kernel::Term* body = term.term();
  for (unsigned index = 0; index < body->arity(); ++index) {
    if (!rememberGroundApplications(
          *body->nthArgument(index), arities, definitions,
          expandingDefinitions, applications, error)) {
      return false;
    }
  }
  return true;
}

}

bool expandGroundProof(
  const std::vector<Step>& steps,
  const std::string& finalStep,
  const std::vector<GroundTerm>& groundTerms,
  const std::vector<FunctionDefinition>& functionDefinitions,
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

  ApplicationArities applicationArities;
  struct SkolemOwnerPattern {
    std::string stepId;
    std::vector<unsigned> dependencyVariables;
  };
  std::map<unsigned, SkolemOwnerPattern> skolemOwnerPatterns;
  for (const auto& step : steps) {
    for (const auto& application : step.applications) {
      const std::size_t arity = applicationArity(application.term);
      auto inserted = applicationArities.emplace(
        application.functionSymbol, arity);
      if (!inserted.second && inserted.first->second != arity) {
        error = "primitive proof uses one Skolem symbol at inconsistent arities";
        return false;
      }
      if (application.skolemOwner) {
        Kernel::TermList head = application.term;
        std::vector<Kernel::TermList> arguments;
        while (head.isApplication()) {
          arguments.push_back(head.rhs());
          head = head.lhs();
        }
        std::reverse(arguments.begin(), arguments.end());
        std::vector<unsigned> dependencyVariables;
        std::set<unsigned> seenVariables;
        for (Kernel::TermList argument : arguments) {
          if (!argument.isVar()
              || !seenVariables.insert(argument.var()).second) {
            error = "Skolem owner application does not have distinct variable dependencies";
            return false;
          }
          dependencyVariables.push_back(argument.var());
        }
        auto owner = skolemOwnerPatterns.emplace(
          application.functionSymbol,
          SkolemOwnerPattern{step.id, dependencyVariables});
        if (!owner.second
            && (owner.first->second.stepId != step.id
                || owner.first->second.dependencyVariables
                   != dependencyVariables)) {
          error = "primitive proof has inconsistent Skolem owner patterns";
          return false;
        }
      }
    }
  }
  FunctionDefinitions definitionBySymbol;
  for (const auto& definition : functionDefinitions) {
    if (!definitionBySymbol.emplace(
          definition.functionSymbol, &definition).second) {
      error = "primitive proof has duplicate producer function definitions";
      return false;
    }
  }
  std::map<unsigned, unsigned> definitionVisitState;
  std::function<bool(unsigned)> validateDefinition;
  validateDefinition = [&](unsigned symbol) {
    const unsigned state = definitionVisitState[symbol];
    if (state == 1) {
      error = "cyclic producer function definitions in the ground Ivy expander";
      return false;
    }
    if (state == 2) {
      return true;
    }
    definitionVisitState[symbol] = 1;
    std::function<bool(Kernel::TermList)> visitDependencies;
    visitDependencies = [&](Kernel::TermList term) {
      Kernel::TermList head = term;
      while (head.isApplication()) {
        head = head.lhs();
      }
      if (head.isTerm() && !head.term()->isSpecial()) {
        auto dependency = definitionBySymbol.find(head.term()->functor());
        if (dependency != definitionBySymbol.end()
            && !validateDefinition(dependency->first)) {
          return false;
        }
      }
      if (term.isVar()) {
        return true;
      }
      if (term.isApplication()) {
        return visitDependencies(term.lhs())
          && visitDependencies(term.rhs());
      }
      Kernel::Term* body = term.term();
      for (unsigned index = 0; index < body->arity(); ++index) {
        if (!visitDependencies(*body->nthArgument(index))) {
          return false;
        }
      }
      return true;
    };
    if (!visitDependencies(definitionBySymbol.at(symbol)->body)) {
      return false;
    }
    definitionVisitState[symbol] = 2;
    return true;
  };
  for (const auto& definition : definitionBySymbol) {
    if (!validateDefinition(definition.first)) {
      return false;
    }
  }

  result = Expansion{"ivy_instance_v3", finalStep, {}};
  std::vector<bool> active;
  std::function<bool(
    const std::string&, const Environment&, bool, std::size_t&)>
    visit = [&](const std::string& stepId,
                const Environment& environment,
                bool parametric,
                std::size_t& resultIndex) {
      auto found = stepById.find(stepId);
      if (found == stepById.end()) {
        error = "primitive proof instance references unknown parent " + stepId;
        return false;
      }
      const Step& step = *found->second;
      bool instanceParametric = parametric;
      if (instanceParametric
          && std::any_of(
            step.applications.begin(),
            step.applications.end(),
            [](const Application& application) {
              return application.requiresGrounding;
            })) {
        Environment probeEnvironment;
        if (!groundEnvironment(
              step,
              environment,
              true,
              groundTerms,
              probeEnvironment,
              error)) {
          return false;
        }
        const bool requiredApplicationsAreGround = std::all_of(
          step.applications.begin(),
          step.applications.end(),
          [&](const Application& application) {
            return !application.requiresGrounding
              || applyEnvironment(application.term, probeEnvironment).ground();
          });
        if (requiredApplicationsAreGround) {
          instanceParametric = false;
        }
      }
      Environment groundedEnvironment;
      if (!groundEnvironment(
            step,
            environment,
            instanceParametric,
            groundTerms,
            groundedEnvironment,
            error)) {
        return false;
      }
      for (const auto& instance : result.instances) {
        if (instance.stepId == stepId
            && instance.parametric == instanceParametric
            && sameEnvironment(instance.environment, groundedEnvironment)) {
          resultIndex = instance.index;
          return true;
        }
      }
      resultIndex = result.instances.size();
      result.instances.push_back(
        Instance{
          resultIndex,
          stepId,
          instanceParametric,
          groundedEnvironment,
          {},
          {},
          {},
          {}});
      active.push_back(true);

      for (const auto& application : step.applications) {
        Kernel::TermList grounded =
          applyEnvironment(application.term, groundedEnvironment);
        if (!grounded.ground()) {
          if (instanceParametric) {
            result.instances[resultIndex].sourceApplications.push_back(
              application);
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
            continue;
          }
          if (!application.requiresGrounding) {
            continue;
          }
          error = "proof instance " + stepId
            + " retains a variable in a Skolem application";
          return false;
        }
        result.instances[resultIndex].sourceApplications.push_back(
          application);
        std::set<unsigned> expandingDefinitions;
        if (!rememberGroundApplications(
              grounded,
              applicationArities,
              definitionBySymbol,
              expandingDefinitions,
              result.instances[resultIndex].applications,
              error)) {
          return false;
        }
      }
      for (const auto& binding : groundedEnvironment) {
        std::set<unsigned> expandingDefinitions;
        if (!rememberGroundApplications(
              binding.second,
              applicationArities,
              definitionBySymbol,
              expandingDefinitions,
              result.instances[resultIndex].applications,
              error)) {
          return false;
        }
      }

      const Environment parentEnvironment =
        composeParentEnvironment(groundedEnvironment, step.parentSubstitution);
      for (const std::string& parentId : step.parentIds) {
        if (stepById.find(parentId) == stepById.end()) {
          error = "primitive proof step " + stepId
            + " references unknown parent " + parentId;
          return false;
        }
        const bool parentParametric =
          instanceParametric
          || std::find(
               step.parametricParentIds.begin(),
               step.parametricParentIds.end(),
               parentId) != step.parametricParentIds.end();
        std::size_t parentIndex = 0;
        if (!visit(
              parentId,
              parentEnvironment,
              parentParametric,
              parentIndex)) {
          return false;
        }
        if (parentIndex < active.size() && active[parentIndex]) {
          error = "primitive proof instance graph contains a cycle";
          return false;
        }
        result.instances[resultIndex].parentInstances.push_back(parentIndex);
        Environment edgeEnvironment;
        const Step& parentStep = *stepById.at(parentId);
        for (const auto& variable : parentStep.freeVariableSorts) {
          const bool explicitlySubstituted = std::any_of(
            step.parentSubstitution.begin(),
            step.parentSubstitution.end(),
            [&](const auto& binding) {
              return binding.first == variable.first;
            });
          if (explicitlySubstituted) {
            continue;
          }
          const bool retainedByChild = std::any_of(
            step.freeVariableSorts.begin(),
            step.freeVariableSorts.end(),
            [&](const auto& childVariable) {
              return childVariable.first == variable.first
                && childVariable.second == variable.second;
            });
          if (retainedByChild) {
            continue;
          }
          const auto binding = std::find_if(
            result.instances[parentIndex].environment.begin(),
            result.instances[parentIndex].environment.end(),
            [&](const auto& candidate) {
              return candidate.first == variable.first;
            });
          if (binding != result.instances[parentIndex].environment.end()) {
            edgeEnvironment.push_back(*binding);
          }
        }
        result.instances[resultIndex].parentEnvironments.push_back(
          std::move(edgeEnvironment));
        for (const Application& application :
             result.instances[parentIndex].applications) {
          Application inherited = application;
          inherited.term =
            applyEnvironment(application.term, parentEnvironment);
          if (!instanceParametric && !inherited.term.ground()) {
            if (result.instances[parentIndex].parametric) {
              // A parametric formula parent may contain Skolem applications in
              // branches omitted by this child's projection.  The parent
              // instance keeps those occurrences; only a child occurrence or
              // an explicit edge substitution may specialize them here.
              continue;
            }
            error = "non-parametric proof instance " + stepId
              + " inherited an unground Skolem application from non-parametric "
              + parentId;
            return false;
          }
          const auto duplicate = std::find_if(
            result.instances[resultIndex].applications.begin(),
            result.instances[resultIndex].applications.end(),
            [&](const Application& existing) {
              return existing.functionSymbol == inherited.functionSymbol
                && existing.term == inherited.term;
            });
          if (duplicate == result.instances[resultIndex].applications.end()) {
            result.instances[resultIndex].applications.push_back(
              std::move(inherited));
          }
        }
      }
      active[resultIndex] = false;
      return true;
    };

  std::size_t rootIndex = 0;
  if (!visit(finalStep, {}, false, rootIndex)) {
    return false;
  }
  if (rootIndex != 0) {
    error = "primitive proof expansion did not allocate the root first";
    return false;
  }
  for (std::size_t instanceIndex = 0;
       instanceIndex < result.instances.size();
       ++instanceIndex) {
    const std::vector<Application> applications =
      result.instances[instanceIndex].applications;
    for (const Application& application : applications) {
      auto owner = skolemOwnerPatterns.find(application.functionSymbol);
      if (owner == skolemOwnerPatterns.end() || !application.term.ground()) {
        continue;
      }
      const bool existingExactOwner = std::any_of(
        result.instances.begin(),
        result.instances.end(),
        [&](const Instance& candidate) {
          if (candidate.stepId != owner->second.stepId) {
            return false;
          }
          const Step& ownerStep = *stepById.at(candidate.stepId);
          return std::any_of(
            ownerStep.applications.begin(),
            ownerStep.applications.end(),
            [&](const Application& source) {
              return source.skolemOwner
                && source.functionSymbol == application.functionSymbol
                && applyEnvironment(source.term, candidate.environment)
                   == application.term;
            });
        });
      if (existingExactOwner) {
        continue;
      }
      Kernel::TermList head = application.term;
      std::vector<Kernel::TermList> arguments;
      while (head.isApplication()) {
        arguments.push_back(head.rhs());
        head = head.lhs();
      }
      std::reverse(arguments.begin(), arguments.end());
      if (arguments.size() != owner->second.dependencyVariables.size()) {
        error = "ground Skolem application does not match its owner pattern";
        return false;
      }
      Environment ownerEnvironment;
      for (std::size_t index = 0; index < arguments.size(); ++index) {
        setBinding(
          ownerEnvironment,
          owner->second.dependencyVariables[index],
          arguments[index]);
      }
      std::size_t ownerIndex = 0;
      if (!visit(
            owner->second.stepId,
            ownerEnvironment,
            false,
            ownerIndex)) {
        std::ostringstream applicationText;
        applicationText << application.term;
        error += " while adding the Skolem owner for "
          + applicationText.str();
        return false;
      }
    }
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
                 std::get_if<ResolveClauseStep>(&request.step)) {
      primitive = step->hasIvyProgram
        ? MegalodonKernelBuilder::resolveIvyStep(
            step->id,
            step->leftParent,
            step->rightParent,
            step->leftPivot,
            step->rightPivot,
            step->result,
            step->leftLiterals,
            step->rightLiterals,
            step->resultLiterals)
        : MegalodonKernelBuilder::resolveStep(
            step->id,
            step->leftParent,
            step->rightParent,
            step->leftPivot,
            step->rightPivot,
            step->result);
    } else if (const auto* step =
                 std::get_if<ParamodulateClauseStep>(&request.step)) {
      primitive = step->hasIvyProgram
        ? MegalodonKernelBuilder::paramodulateIvyStep(
            step->id,
            step->equalityParent,
            step->equalityLiteral,
            step->targetParent,
            step->targetLiteral,
            step->position,
            step->from,
            step->to,
            step->result,
            step->equalityLiterals,
            step->targetLiterals,
            step->rewrittenLiteral,
            step->resultLiterals,
            step->rewriteSymmetry)
        : MegalodonKernelBuilder::paramodulateStep(
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
      primitive = step->hasIvyProgram
        ? MegalodonKernelBuilder::factorIvyStep(
            step->id,
            step->parent,
            step->leftLiteral,
            step->rightLiteral,
            step->result,
            step->sourceLiterals,
            step->resultLiterals)
        : MegalodonKernelBuilder::factorStep(
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
  for (std::size_t index = 0; index < result.renderedSteps.size(); ++index) {
    if (index != 0) {
      result.rendered += "\n  ";
    }
    result.rendered += result.renderedSteps[index];
  }
  return true;
}

namespace {

Kernel::Formula* normalizeTransportShape(Kernel::Formula* formula)
{
  switch (formula->connective()) {
    case Kernel::FORALL:
    case Kernel::EXISTS: {
      std::vector<std::pair<unsigned, Kernel::TermList>> variables;
      Kernel::VSList::Iterator iterator(formula->vars());
      while (iterator.hasNext()) {
        variables.push_back(iterator.next());
      }
      Kernel::Formula* body = normalizeTransportShape(formula->qarg());
      for (std::size_t index = variables.size(); index-- > 0;) {
        body = new Kernel::QuantifiedFormula(
          formula->connective(),
          Kernel::VSList::singleton(variables[index]),
          body);
      }
      return body;
    }
    case Kernel::AND:
    case Kernel::OR: {
      std::vector<Kernel::Formula*> arguments;
      auto iterator = formula->args()->iter();
      while (iterator.hasNext()) {
        arguments.push_back(normalizeTransportShape(iterator.next()));
      }
      if (arguments.size() < 2) {
        return formula;
      }
      Kernel::Formula* result = arguments.back();
      for (std::size_t index = arguments.size() - 1; index-- > 0;) {
        result = new Kernel::JunctionFormula(
          formula->connective(),
          new Kernel::FormulaList(
            arguments[index],
            new Kernel::FormulaList(result)));
      }
      return result;
    }
    case Kernel::IMP:
    case Kernel::IFF:
    case Kernel::XOR:
      return new Kernel::BinaryFormula(
        formula->connective(),
        normalizeTransportShape(formula->left()),
        normalizeTransportShape(formula->right()));
    case Kernel::NOT:
      return new Kernel::BinaryFormula(
        Kernel::IMP,
        normalizeTransportShape(formula->uarg()),
        Kernel::Formula::falseFormula());
    default:
      return formula;
  }
}

Kernel::TermList substitutedVariable(
  Kernel::TermList term,
  const Environment& substitutions)
{
  for (std::size_t remaining = substitutions.size();
       term.isVar() && remaining-- > 0;) {
    auto found = std::find_if(
      substitutions.begin(),
      substitutions.end(),
      [&](const auto& binding) { return binding.first == term.var(); });
    if (found == substitutions.end()
        || (found->second.isVar() && found->second.var() == term.var())) {
      break;
    }
    term = found->second;
  }
  return term;
}

bool sameFormulaModuloAliases(
  Kernel::Formula* left,
  const Environment& leftAliases,
  Kernel::Formula* right,
  const Environment& rightAliases);

bool sameTermModuloAliases(
  Kernel::TermList left,
  const Environment& leftAliases,
  Kernel::TermList right,
  const Environment& rightAliases)
{
  left = substitutedVariable(left, leftAliases);
  right = substitutedVariable(right, rightAliases);
  if (left.isVar() || right.isVar()) {
    return left.isVar()
      && right.isVar()
      && left.var() == right.var();
  }
  if (left.isApplication() || right.isApplication()) {
    return left.isApplication()
      && right.isApplication()
      && sameTermModuloAliases(
           left.lhs(), leftAliases, right.lhs(), rightAliases)
      && sameTermModuloAliases(
           left.rhs(), leftAliases, right.rhs(), rightAliases);
  }
  if (!left.isTerm() || !right.isTerm()) {
    return left == right;
  }
  Kernel::Term* leftTerm = left.term();
  Kernel::Term* rightTerm = right.term();
  if (leftTerm->isSpecial() || rightTerm->isSpecial()) {
    if (!leftTerm->isSpecial() || !rightTerm->isSpecial()
        || leftTerm->specialFunctor() != rightTerm->specialFunctor()) {
      return false;
    }
    if (leftTerm->isFormula() && rightTerm->isFormula()) {
      return sameFormulaModuloAliases(
        leftTerm->getSpecialData()->getFormula(), leftAliases,
        rightTerm->getSpecialData()->getFormula(), rightAliases);
    }
    if (leftTerm->isLambda() && rightTerm->isLambda()) {
      const auto* leftData = leftTerm->getSpecialData();
      const auto* rightData = rightTerm->getSpecialData();
      std::vector<std::pair<unsigned, Kernel::TermList>> leftVariables;
      std::vector<std::pair<unsigned, Kernel::TermList>> rightVariables;
      Kernel::VSList::Iterator leftIterator(leftData->getLambdaVars());
      Kernel::VSList::Iterator rightIterator(rightData->getLambdaVars());
      while (leftIterator.hasNext()) {
        leftVariables.push_back(leftIterator.next());
      }
      while (rightIterator.hasNext()) {
        rightVariables.push_back(rightIterator.next());
      }
      if (leftVariables.size() != rightVariables.size()) {
        return false;
      }
      Environment bodyLeftAliases = leftAliases;
      Environment bodyRightAliases = rightAliases;
      for (std::size_t index = 0; index < leftVariables.size(); ++index) {
        const auto& leftVariable = leftVariables[index];
        const auto& rightVariable = rightVariables[index];
        if (!sameTermModuloAliases(
              leftVariable.second, bodyLeftAliases,
              rightVariable.second, bodyRightAliases)) {
          return false;
        }
        setBinding(
          bodyLeftAliases,
          leftVariable.first,
          Kernel::TermList::var(rightVariable.first));
        setBinding(
          bodyRightAliases,
          rightVariable.first,
          Kernel::TermList::var(rightVariable.first));
      }
      return sameTermModuloAliases(
               leftData->getLambdaExpSort(), bodyLeftAliases,
               rightData->getLambdaExpSort(), bodyRightAliases)
        && sameTermModuloAliases(
             leftData->getLambdaExp(), bodyLeftAliases,
             rightData->getLambdaExp(), bodyRightAliases);
    }
    return left == right;
  }
  if (leftTerm->functor() != rightTerm->functor()
      || leftTerm->arity() != rightTerm->arity()) {
    return false;
  }
  for (unsigned index = 0; index < leftTerm->arity(); ++index) {
    if (!sameTermModuloAliases(
          *leftTerm->nthArgument(index), leftAliases,
          *rightTerm->nthArgument(index), rightAliases)) {
      return false;
    }
  }
  return true;
}

bool sameLiteralModuloAliases(
  const Kernel::Literal* left,
  const Environment& leftAliases,
  const Kernel::Literal* right,
  const Environment& rightAliases)
{
  if (left->functor() != right->functor()
      || left->arity() != right->arity()
      || left->polarity() != right->polarity()) {
    return false;
  }
  if (left->isEquality()
      && Kernel::SortHelper::getEqualityArgumentSort(left)
         != Kernel::SortHelper::getEqualityArgumentSort(right)) {
    return false;
  }
  for (unsigned index = 0; index < left->arity(); ++index) {
    if (!sameTermModuloAliases(
          *left->nthArgument(index), leftAliases,
          *right->nthArgument(index), rightAliases)) {
      return false;
    }
  }
  return true;
}

bool sameFormulaModuloAliases(
  Kernel::Formula* left,
  const Environment& leftAliases,
  Kernel::Formula* right,
  const Environment& rightAliases)
{
  if (left->connective() != right->connective()) {
    return false;
  }
  switch (left->connective()) {
    case Kernel::LITERAL:
      return sameLiteralModuloAliases(
        left->literal(), leftAliases, right->literal(), rightAliases);
    case Kernel::BOOL_TERM:
      return sameTermModuloAliases(
        left->getBooleanTerm(), leftAliases,
        right->getBooleanTerm(), rightAliases);
    case Kernel::TRUE:
    case Kernel::FALSE:
      return true;
    case Kernel::NAME:
      return static_cast<Kernel::NamedFormula*>(left)->name()
        == static_cast<Kernel::NamedFormula*>(right)->name();
    case Kernel::NOT:
      return sameFormulaModuloAliases(
        left->uarg(), leftAliases, right->uarg(), rightAliases);
    case Kernel::IMP:
    case Kernel::IFF:
    case Kernel::XOR:
      return sameFormulaModuloAliases(
               left->left(), leftAliases, right->left(), rightAliases)
        && sameFormulaModuloAliases(
             left->right(), leftAliases, right->right(), rightAliases);
    case Kernel::FORALL:
    case Kernel::EXISTS: {
      Kernel::VSList::Iterator leftVariables(left->vars());
      Kernel::VSList::Iterator rightVariables(right->vars());
      while (leftVariables.hasNext() && rightVariables.hasNext()) {
        if (leftVariables.next() != rightVariables.next()) {
          return false;
        }
      }
      return !leftVariables.hasNext()
        && !rightVariables.hasNext()
        && sameFormulaModuloAliases(
             left->qarg(), leftAliases, right->qarg(), rightAliases);
    }
    case Kernel::AND:
    case Kernel::OR: {
      auto leftArguments = left->args()->iter();
      auto rightArguments = right->args()->iter();
      while (leftArguments.hasNext() && rightArguments.hasNext()) {
        if (!sameFormulaModuloAliases(
              leftArguments.next(), leftAliases,
              rightArguments.next(), rightAliases)) {
          return false;
        }
      }
      return !leftArguments.hasNext() && !rightArguments.hasNext();
    }
    default:
      return false;
  }
}

bool swappedEqualityLiteral(
  const Kernel::Literal* source,
  const Environment& sourceAliases,
  const Kernel::Literal* target,
  const Environment& targetAliases)
{
  return source->isEquality()
    && target->isEquality()
    && source->polarity() == target->polarity()
    && Kernel::SortHelper::getEqualityArgumentSort(source)
       == Kernel::SortHelper::getEqualityArgumentSort(target)
    && sameTermModuloAliases(
         *source->nthArgument(0), sourceAliases,
         *target->nthArgument(1), targetAliases)
    && sameTermModuloAliases(
         *source->nthArgument(1), sourceAliases,
         *target->nthArgument(0), targetAliases);
}

bool binaryJunctionChildren(
  Kernel::Formula* formula,
  Kernel::Formula*& left,
  Kernel::Formula*& right)
{
  if (formula->connective() != Kernel::AND
      && formula->connective() != Kernel::OR) {
    return false;
  }
  auto iterator = formula->args()->iter();
  if (!iterator.hasNext()) {
    return false;
  }
  left = iterator.next();
  if (!iterator.hasNext()) {
    return false;
  }
  right = iterator.next();
  return !iterator.hasNext();
}

}

bool expandFormulaTransport(
  const FormulaTransportRequest& request,
  FormulaTransportNode& result,
  std::string& error)
{
  if (request.source == nullptr || request.target == nullptr) {
    error = "formula transport request has a missing endpoint";
    return false;
  }
  unsigned nextFreshVariable = 0;
  auto reserveFormulaVariables = [&](Kernel::Formula* formula) {
    Lib::DHMap<unsigned, Kernel::TermList> variables;
    Kernel::SortHelper::collectVariableSorts(formula, variables, false);
    Lib::DHMap<unsigned, Kernel::TermList>::Iterator iterator(variables);
    while (iterator.hasNext()) {
      unsigned variable;
      Kernel::TermList sort;
      iterator.next(variable, sort);
      nextFreshVariable = std::max(nextFreshVariable, variable + 1);
    }
  };
  reserveFormulaVariables(request.source);
  reserveFormulaVariables(request.target);
  for (const auto& [sourceVariable, targetTerm] : request.freeVariableMap) {
    nextFreshVariable = std::max(nextFreshVariable, sourceVariable + 1);
    if (targetTerm.isVar()) {
      nextFreshVariable = std::max(nextFreshVariable, targetTerm.var() + 1);
    }
  }
  std::size_t nextIndex = 0;
  std::function<bool(
    Kernel::Formula*,
    Kernel::Formula*,
    const Environment&,
    const Environment&,
    bool,
    bool,
    const VariableSorts&,
    FormulaTransportNode&)> build;
  build = [&](Kernel::Formula* rawSource,
              Kernel::Formula* rawTarget,
              const Environment& sourceAliases,
              const Environment& targetAliases,
              bool preserveSourceNegativeEqualityOrientation,
              bool preserveTargetNegativeEqualityOrientation,
              const VariableSorts& context,
              FormulaTransportNode& node) {
    Kernel::Formula* source = normalizeTransportShape(rawSource);
    Kernel::Formula* target = normalizeTransportShape(rawTarget);
    node = FormulaTransportNode{};
    node.index = nextIndex++;
    node.source = source;
    node.target = target;
    node.sourceVariableMap = sourceAliases;
    node.targetVariableMap = targetAliases;
    node.preserveSourceNegativeEqualityOrientation =
      preserveSourceNegativeEqualityOrientation;
    node.preserveTargetNegativeEqualityOrientation =
      preserveTargetNegativeEqualityOrientation;
    node.context = context;

    if (sameFormulaModuloAliases(
          source, sourceAliases, target, targetAliases)) {
      node.primitive = "transport_identity";
      return true;
    }
    if (source->connective() == Kernel::LITERAL
        && target->connective() == Kernel::LITERAL
        && swappedEqualityLiteral(
             source->literal(), sourceAliases,
             target->literal(), targetAliases)) {
      node.primitive = source->literal()->isPositive()
        ? "transport_equality_symmetry_positive"
        : "transport_equality_symmetry_negative";
      return true;
    }
    if ((source->connective() == Kernel::FORALL
         || source->connective() == Kernel::EXISTS)
        && source->connective() == target->connective()) {
      Kernel::VSList::Iterator sourceVariables(source->vars());
      Kernel::VSList::Iterator targetVariables(target->vars());
      if (!sourceVariables.hasNext() || !targetVariables.hasNext()) {
        error = "formula transport quantifier has no variable";
        return false;
      }
      const auto sourceVariable = sourceVariables.next();
      const auto targetVariable = targetVariables.next();
      if (sourceVariables.hasNext()
          || targetVariables.hasNext()
          || sourceVariable.second != targetVariable.second) {
        error = "formula transport quantifier binders do not match";
        return false;
      }
      Environment childSourceAliases = sourceAliases;
      const unsigned contextVariable = nextFreshVariable++;
      setBinding(
        childSourceAliases,
        sourceVariable.first,
        Kernel::TermList::var(contextVariable));
      Environment childTargetAliases = targetAliases;
      setBinding(
        childTargetAliases,
        targetVariable.first,
        Kernel::TermList::var(contextVariable));
      VariableSorts childContext = context;
      childContext.push_back({contextVariable, targetVariable.second});
      FormulaTransportNode child;
      if (!build(
            source->qarg(),
            target->qarg(),
            childSourceAliases,
            childTargetAliases,
            preserveSourceNegativeEqualityOrientation,
            preserveTargetNegativeEqualityOrientation,
            childContext,
            child)) {
        return false;
      }
      node.primitive = source->connective() == Kernel::FORALL
        ? "transport_forall_map"
        : "transport_exists_map";
      node.children.push_back(std::move(child));
      return true;
    }
    if (source->connective() == Kernel::IMP
        && target->connective() == Kernel::IMP) {
      FormulaTransportNode left;
      FormulaTransportNode right;
      if (!build(
            target->left(), source->left(),
            targetAliases, sourceAliases,
            preserveTargetNegativeEqualityOrientation,
            preserveSourceNegativeEqualityOrientation,
            context, left)
          || !build(
            source->right(), target->right(),
            sourceAliases, targetAliases,
            preserveSourceNegativeEqualityOrientation,
            preserveTargetNegativeEqualityOrientation,
            context, right)) {
        return false;
      }
      node.primitive = "transport_imp_map";
      node.children.push_back(std::move(left));
      node.children.push_back(std::move(right));
      return true;
    }
    if ((source->connective() == Kernel::AND
         || source->connective() == Kernel::OR)
        && source->connective() == target->connective()) {
      Kernel::Formula* sourceLeft = nullptr;
      Kernel::Formula* sourceRight = nullptr;
      Kernel::Formula* targetLeft = nullptr;
      Kernel::Formula* targetRight = nullptr;
      if (!binaryJunctionChildren(source, sourceLeft, sourceRight)
          || !binaryJunctionChildren(target, targetLeft, targetRight)) {
        error = "formula transport junction is not binary after normalization";
        return false;
      }
      FormulaTransportNode left;
      FormulaTransportNode right;
      if (!build(
            sourceLeft, targetLeft,
            sourceAliases, targetAliases,
            preserveSourceNegativeEqualityOrientation,
            preserveTargetNegativeEqualityOrientation,
            context, left)
          || !build(
            sourceRight, targetRight,
            sourceAliases, targetAliases,
            preserveSourceNegativeEqualityOrientation,
            preserveTargetNegativeEqualityOrientation,
            context, right)) {
        return false;
      }
      node.primitive = source->connective() == Kernel::AND
        ? "transport_and_map"
        : "transport_or_map";
      node.children.push_back(std::move(left));
      node.children.push_back(std::move(right));
      return true;
    }
    error = "formula transport endpoints do not match a producer primitive: "
      + source->toString() + " ==> " + target->toString();
    return false;
  };

  return build(
    request.source,
    request.target,
    request.freeVariableMap,
    {},
    request.preserveSourceNegativeEqualityOrientation,
    false,
    {},
    result);
}

}
}
