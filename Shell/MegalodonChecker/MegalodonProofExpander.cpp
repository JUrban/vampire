#include "Shell/MegalodonChecker/MegalodonProofExpander.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"
#include "Lib/DHMap.hpp"

#include <algorithm>
#include <cctype>
#include <chrono>
#include <cstdlib>
#include <functional>
#include <iostream>
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

  VariableSorts needed;
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
      if (std::any_of(
            step.freeVariableSorts.begin(),
            step.freeVariableSorts.end(),
            [&](const auto& variable) {
              return std::none_of(
                groundedEnvironment.begin(),
                groundedEnvironment.end(),
                [&](const auto& binding) {
                  return binding.first == variable.first;
                });
            })) {
        instanceParametric = true;
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
        Environment parentVisitEnvironment = parentEnvironment;
        for (const auto& fresh : step.freshParentVariables) {
          if (fresh.first != parentId) continue;
          if (!parentParametric) {
            error = "primitive proof step " + stepId
              + " freshens a non-parametric parent " + parentId;
            return false;
          }
          if (std::getenv("MEGALODON_CERT_DEBUG")) {
            std::cerr << "megalodon grounding fresh edge " << stepId
                      << " -> " << parentId << " X" << fresh.second
                      << " environment " << parentVisitEnvironment.size();
          }
          parentVisitEnvironment.erase(
            std::remove_if(
              parentVisitEnvironment.begin(),
              parentVisitEnvironment.end(),
              [&](const auto& binding) {
                return binding.first == fresh.second;
              }),
            parentVisitEnvironment.end());
          if (std::getenv("MEGALODON_CERT_DEBUG")) {
            std::cerr << " -> " << parentVisitEnvironment.size()
                      << std::endl;
          }
        }
        std::size_t parentIndex = 0;
        if (!visit(
              parentId,
              parentVisitEnvironment,
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
            applyEnvironment(application.term, parentVisitEnvironment);
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
        step->result,
        step->producerProof);
    } else if (const auto* step =
                 std::get_if<EqualitySymmetryClauseStep>(&request.step)) {
      if (step->producerProof.empty()) {
        error = step->id
          + ": missing direct producer proof for equality symmetry";
        return false;
      }
      primitive = MegalodonKernelBuilder::equalitySymmetryStep(
        step->id,
        step->parent,
        step->literal,
        step->result,
        step->producerProof);
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
            step->resultLiterals,
            step->producerProof)
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
            step->rewriteSymmetry,
            step->producerProof)
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
      if ((step->producerUsesEqualityParentUnderBinder
           || step->producerScopedLambdaChoice != nullptr)
          && !step->hasProducerEqualityParentBinderVariable) {
        error = step->id
          + ": scoped paramodulation lacks its producer equality-parent binder variable";
        return false;
      }
      if (step->producerUsesEqualityParentUnderBinder
          || step->producerScopedLambdaChoice != nullptr) {
        primitive.producerParametricParentIds = {
          step->equalityParent.value,
        };
        primitive.producerFreshParentVariables = {{
          step->equalityParent.value,
          step->producerEqualityParentBinderVariable,
        }};
      }
      if (step->producerScopedLambdaChoice != nullptr) {
        primitive.forceChoiceNormalization = true;
        primitive.producerScopedLambdaChoice =
          step->producerScopedLambdaChoice;
      }
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
            step->resultLiterals,
            step->producerProof)
        : MegalodonKernelBuilder::factorStep(
            step->id,
            step->parent,
            step->leftLiteral,
            step->rightLiteral,
            step->result);
      primitive.producerSourceLiterals = step->sourceLiterals;
      primitive.producerResultLiterals = step->resultLiterals;
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

bool inputEqualityOrientationDiffers(
  Kernel::Formula* source,
  bool preserveSourceInputEqualityOrientation,
  Kernel::Formula* target,
  bool preserveTargetInputEqualityOrientation)
{
  if (source->connective() != target->connective()) {
    return false;
  }
  switch (source->connective()) {
    case Kernel::LITERAL: {
      if (!source->literal()->isEquality()
          || !target->literal()->isEquality()) {
        return false;
      }
      const bool sourceFlipped =
        preserveSourceInputEqualityOrientation
        && static_cast<Kernel::AtomicFormula*>(source)->flipForPrinting;
      const bool targetFlipped =
        preserveTargetInputEqualityOrientation
        && static_cast<Kernel::AtomicFormula*>(target)->flipForPrinting;
      return sourceFlipped != targetFlipped;
    }
    case Kernel::NOT:
      return inputEqualityOrientationDiffers(
        source->uarg(), preserveSourceInputEqualityOrientation,
        target->uarg(), preserveTargetInputEqualityOrientation);
    case Kernel::IMP:
    case Kernel::IFF:
    case Kernel::XOR:
      return inputEqualityOrientationDiffers(
               source->left(), preserveSourceInputEqualityOrientation,
               target->left(), preserveTargetInputEqualityOrientation)
        || inputEqualityOrientationDiffers(
             source->right(), preserveSourceInputEqualityOrientation,
             target->right(), preserveTargetInputEqualityOrientation);
    case Kernel::FORALL:
    case Kernel::EXISTS:
      return inputEqualityOrientationDiffers(
        source->qarg(), preserveSourceInputEqualityOrientation,
        target->qarg(), preserveTargetInputEqualityOrientation);
    case Kernel::AND:
    case Kernel::OR: {
      auto sourceArguments = source->args()->iter();
      auto targetArguments = target->args()->iter();
      while (sourceArguments.hasNext() && targetArguments.hasNext()) {
        if (inputEqualityOrientationDiffers(
              sourceArguments.next(), preserveSourceInputEqualityOrientation,
              targetArguments.next(), preserveTargetInputEqualityOrientation)) {
          return true;
        }
      }
      return false;
    }
    default:
      return false;
  }
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
              bool preserveSourceInputEqualityOrientation,
              bool preserveTargetInputEqualityOrientation,
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
    node.preserveSourceInputEqualityOrientation =
      preserveSourceInputEqualityOrientation;
    node.preserveTargetInputEqualityOrientation =
      preserveTargetInputEqualityOrientation;
    node.context = context;

    if (sameFormulaModuloAliases(
          source, sourceAliases, target, targetAliases)
        && !inputEqualityOrientationDiffers(
             source, preserveSourceInputEqualityOrientation,
             target, preserveTargetInputEqualityOrientation)) {
      node.primitive = "transport_identity";
      return true;
    }
    if (source->connective() == Kernel::LITERAL
        && target->connective() == Kernel::LITERAL
        && (swappedEqualityLiteral(
              source->literal(), sourceAliases,
              target->literal(), targetAliases)
            || (sameLiteralModuloAliases(
                  source->literal(), sourceAliases,
                  target->literal(), targetAliases)
                && inputEqualityOrientationDiffers(
                     source, preserveSourceInputEqualityOrientation,
                     target, preserveTargetInputEqualityOrientation)))) {
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
            preserveSourceInputEqualityOrientation,
            preserveTargetInputEqualityOrientation,
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
            preserveTargetInputEqualityOrientation,
            preserveSourceInputEqualityOrientation,
            context, left)
          || !build(
            source->right(), target->right(),
            sourceAliases, targetAliases,
            preserveSourceNegativeEqualityOrientation,
            preserveTargetNegativeEqualityOrientation,
            preserveSourceInputEqualityOrientation,
            preserveTargetInputEqualityOrientation,
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
            preserveSourceInputEqualityOrientation,
            preserveTargetInputEqualityOrientation,
            context, left)
          || !build(
            sourceRight, targetRight,
            sourceAliases, targetAliases,
            preserveSourceNegativeEqualityOrientation,
            preserveTargetNegativeEqualityOrientation,
            preserveSourceInputEqualityOrientation,
            preserveTargetInputEqualityOrientation,
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
    request.preserveSourceInputEqualityOrientation,
    request.preserveTargetInputEqualityOrientation,
    {},
    result);
}

bool expandGoalReplay(
  const std::vector<GoalReplayStep>& steps,
  const std::string& finalStep,
  MegalodonKernelSyntax::RenderedKernelGoalReplay& result,
  std::string& error)
{
  std::map<std::string, const GoalReplayStep*> byId;
  for (const auto& step : steps) {
    if (step.id.empty() || !byId.emplace(step.id, &step).second) {
      error = "goal replay has an empty or duplicate step id";
      return false;
    }
  }
  auto final = byId.find(finalStep);
  if (final == byId.end() || !final->second->final) {
    error = "goal replay final step is not the refutation root";
    return false;
  }

  std::set<std::string> reachable;
  std::set<std::string> active;
  std::function<bool(const std::string&)> visit =
    [&](const std::string& id) {
      if (reachable.find(id) != reachable.end()) {
        return true;
      }
      auto found = byId.find(id);
      if (found == byId.end()) {
        // A choice-normalized producer block may replace an entire local-symbol
        // slice.  References into that replaced slice are opaque leaves in the
        // final native certificate, exactly as they are for the consumer.
        reachable.insert(id);
        return true;
      }
      if (!active.insert(id).second) {
        error = "goal replay proof graph is cyclic at " + id;
        return false;
      }
      for (const std::string& parent : found->second->parentIds) {
        if (!visit(parent)) {
          return false;
        }
      }
      active.erase(id);
      reachable.insert(id);
      return true;
    };
  if (!visit(finalStep)) {
    return false;
  }

  if (std::getenv("MEGALODON_CERT_DEBUG")) {
    std::function<bool(
      const std::string&, const std::string&, std::set<std::string>&,
      std::vector<std::string>&)> findPath;
    findPath = [&](const std::string& id,
                   const std::string& target,
                   std::set<std::string>& seen,
                   std::vector<std::string>& path) {
      if (!seen.insert(id).second) return false;
      path.push_back(id);
      if (id == target) return true;
      const auto found = byId.find(id);
      if (found != byId.end()) {
        for (const std::string& parent : found->second->parentIds) {
          if (findPath(parent, target, seen, path)) return true;
        }
      }
      path.pop_back();
      seen.erase(id);
      return false;
    };
    for (const auto& step : steps) {
      if (!step.source || step.sourceRole == "conjecture"
          || reachable.find(step.id) == reachable.end()) {
        continue;
      }
      std::set<std::string> seen;
      std::vector<std::string> path;
      findPath(finalStep, step.id, seen, path);
      std::cerr << "megalodon goal source path " << step.id << ':';
      for (const std::string& id : path) std::cerr << ' ' << id;
      std::cerr << std::endl;
    }
  }

  std::vector<const GoalReplayStep*> conjectures;
  std::vector<const GoalReplayStep*> negatedConjectures;
  for (const auto& step : steps) {
    // The refutation can be independent of the conjecture when the imported
    // axioms are already inconsistent.  Preserve the unique source goal pair
    // even in that case; the final contradiction remains the replay root.
    if (step.sourceRole == "conjecture") {
      conjectures.push_back(&step);
    } else if (step.sourceRole == "negated_conjecture") {
      negatedConjectures.push_back(&step);
    }
  }
  if (conjectures.size() != 1 || negatedConjectures.size() != 1) {
    error = "goal replay requires exactly one conjecture and one negated conjecture";
    return false;
  }
  const GoalReplayStep& conjecture = *conjectures.front();
  const GoalReplayStep& negated = *negatedConjectures.front();
  if (conjecture.formula.sexpr.empty()
      || negated.formula.sexpr.empty()
      || std::find(
           negated.parentIds.begin(),
           negated.parentIds.end(),
           conjecture.id) == negated.parentIds.end()) {
    error = "goal replay negated conjecture is not linked to its conjecture parent";
    return false;
  }

  result = MegalodonKernelSyntax::RenderedKernelGoalReplay();
  result.finalStep = MegalodonKernelSyntax::unitRef(finalStep);
  result.conjectureStep = MegalodonKernelSyntax::unitRef(conjecture.id);
  result.conjectureFormula = conjecture.formula;
  result.negatedConjectureStep = MegalodonKernelSyntax::unitRef(negated.id);
  result.negatedConjectureFormula = negated.formula;
  for (const auto& step : steps) {
    if (!step.source
        || step.sourceRole == "conjecture"
        || reachable.find(step.id) == reachable.end()) {
      continue;
    }
    if (step.sourceRole != "axiom"
        && step.sourceRole != "definition"
        && step.sourceRole != "set_reflexivity"
        && step.sourceRole != "negated_conjecture") {
      error = "goal replay has unsupported source role " + step.sourceRole;
      return false;
    }
    result.sources.push_back({
      MegalodonKernelSyntax::unitRef(step.id),
      step.sourceRole,
    });
  }
  if (reachable.find(negated.id) != reachable.end()
      && std::none_of(
           result.sources.begin(),
           result.sources.end(),
           [&](const auto& source) {
             return source.step.value == negated.id
               && source.role == "negated_conjecture";
           })) {
    error = "goal replay source leaves omit the negated conjecture";
    return false;
  }
  return true;
}

namespace {

struct PreservedSexpr {
  bool atom = true;
  std::string token;
  std::vector<PreservedSexpr> items;

  void appendTo(std::string& result) const
  {
    if (atom) {
      result += token;
      return;
    }
    result += '(';
    for (std::size_t index = 0; index < items.size(); ++index) {
      if (index != 0) result += ' ';
      items[index].appendTo(result);
    }
    result += ')';
  }

  std::size_t renderedSize() const
  {
    if (atom) return token.size();
    std::size_t size = 2;
    for (const auto& item : items) {
      size += item.renderedSize();
    }
    if (!items.empty()) size += items.size() - 1;
    return size;
  }

  std::string render() const
  {
    std::string result;
    result.reserve(renderedSize());
    appendTo(result);
    return result;
  }

  bool operator==(const PreservedSexpr& other) const
  {
    return atom == other.atom && token == other.token && items == other.items;
  }

  bool operator!=(const PreservedSexpr& other) const
  {
    return !(*this == other);
  }
};

PreservedSexpr preservedAtom(std::string token)
{
  PreservedSexpr result;
  result.token = std::move(token);
  return result;
}

template<class... Items>
PreservedSexpr preservedList(Items&&... items)
{
  PreservedSexpr result;
  result.atom = false;
  result.items.reserve(sizeof...(Items));
  (result.items.push_back(std::forward<Items>(items)), ...);
  return result;
}

class PreservedSexprParser {
public:
  bool parse(const std::string& source, PreservedSexpr& result)
  {
    _source = &source;
    _cursor = 0;
    skipWhitespace();
    if (!parseOne(result)) return false;
    skipWhitespace();
    return _cursor == _source->size();
  }

private:
  const std::string* _source = nullptr;
  std::size_t _cursor = 0;

  void skipWhitespace()
  {
    while (_cursor < _source->size()
      && std::isspace(static_cast<unsigned char>((*_source)[_cursor]))) {
      ++_cursor;
    }
  }

  bool parseOne(PreservedSexpr& result)
  {
    if (_cursor >= _source->size() || (*_source)[_cursor] == ')') {
      return false;
    }
    if ((*_source)[_cursor] == '(') {
      result.atom = false;
      result.token.clear();
      result.items.clear();
      ++_cursor;
      skipWhitespace();
      while (_cursor < _source->size() && (*_source)[_cursor] != ')') {
        PreservedSexpr item;
        if (!parseOne(item)) return false;
        result.items.push_back(std::move(item));
        skipWhitespace();
      }
      if (_cursor >= _source->size()) return false;
      ++_cursor;
      return true;
    }

    result.atom = true;
    result.items.clear();
    const std::size_t start = _cursor;
    if ((*_source)[_cursor] == '"') {
      ++_cursor;
      bool escaped = false;
      while (_cursor < _source->size()) {
        const char ch = (*_source)[_cursor++];
        if (escaped) {
          escaped = false;
        } else if (ch == '\\') {
          escaped = true;
        } else if (ch == '"') {
          result.token = _source->substr(start, _cursor - start);
          return true;
        }
      }
      return false;
    }
    while (_cursor < _source->size()
      && !std::isspace(static_cast<unsigned char>((*_source)[_cursor]))
      && (*_source)[_cursor] != '('
      && (*_source)[_cursor] != ')') {
      ++_cursor;
    }
    if (_cursor == start) return false;
    result.token = _source->substr(start, _cursor - start);
    return true;
  }
};

bool sexprHead(const PreservedSexpr& value, const char* head)
{
  return !value.atom && !value.items.empty() && value.items[0].atom
    && value.items[0].token == head;
}

PreservedSexpr quotedTmh(const std::string& quotedName)
{
  PreservedSexpr head;
  head.token = "TMH";
  PreservedSexpr name;
  name.token = quotedName;
  PreservedSexpr result;
  result.atom = false;
  result.items = {std::move(head), std::move(name)};
  return result;
}

PreservedSexpr* sexprTermChild(
  PreservedSexpr& term,
  unsigned position)
{
  if (sexprHead(term, "TPAP") && term.items.size() == 3 && position == 0) {
    return &term.items[1];
  }
  if (sexprHead(term, "AP") && term.items.size() == 3) {
    if (position == 0 && sexprHead(term.items[1], "TMH")
        && term.items[1].items.size() == 2
        && term.items[1].items[1].atom
        && term.items[1].items[1].token == "\"vLAM\"") {
      return &term.items[2];
    }
    if (position <= 1) return &term.items[position + 1];
  }
  if ((sexprHead(term, "LAM") || sexprHead(term, "ALL"))
      && term.items.size() == 3 && position == 0) {
    return &term.items[2];
  }
  if ((sexprHead(term, "LAMV") || sexprHead(term, "VLAMV")
       || sexprHead(term, "ALLV"))
      && term.items.size() == 4 && position == 0) {
    return &term.items[3];
  }
  if (sexprHead(term, "IMP") && term.items.size() == 3 && position <= 1) {
    return &term.items[position + 1];
  }
  return nullptr;
}

const PreservedSexpr* sexprTermChild(
  const PreservedSexpr& term,
  unsigned position)
{
  return sexprTermChild(const_cast<PreservedSexpr&>(term), position);
}

bool replaceSexprTermAtPosition(
  const PreservedSexpr& source,
  const std::vector<unsigned>& position,
  const PreservedSexpr& replacement,
  PreservedSexpr& result,
  PreservedSexpr* selected = nullptr)
{
  result = source;
  PreservedSexpr* cursor = &result;
  for (unsigned child : position) {
    cursor = sexprTermChild(*cursor, child);
    if (cursor == nullptr) return false;
  }
  if (selected != nullptr) *selected = *cursor;
  *cursor = replacement;
  return true;
}

bool typedEqualitySexpr(
  const PreservedSexpr& atom,
  PreservedSexpr& type,
  PreservedSexpr& left,
  PreservedSexpr& right)
{
  static const char* equalityHash =
    "\"5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a\"";
  if (!sexprHead(atom, "AP") || atom.items.size() != 3
      || !sexprHead(atom.items[1], "AP") || atom.items[1].items.size() != 3
      || !sexprHead(atom.items[1].items[1], "TPAP")
      || atom.items[1].items[1].items.size() != 3
      || !sexprHead(atom.items[1].items[1].items[1], "TMH")
      || atom.items[1].items[1].items[1].items.size() != 2
      || !atom.items[1].items[1].items[1].items[1].atom
      || atom.items[1].items[1].items[1].items[1].token != equalityHash) {
    return false;
  }
  type = atom.items[1].items[1].items[2];
  left = atom.items[1].items[2];
  right = atom.items[2];
  return true;
}

PreservedSexpr equalityAtomSexpr(
  const PreservedSexpr& type,
  const PreservedSexpr& left,
  const PreservedSexpr& right)
{
  PreservedSexprParser parser;
  PreservedSexpr result;
  const std::string rendered =
    "(AP (AP (TPAP (TMH \"5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a\") "
    + type.render() + ") " + left.render() + ") " + right.render() + ")";
  if (!parser.parse(rendered, result)) result = PreservedSexpr();
  return result;
}

PreservedSexpr literalSexpr(
  bool positive,
  const PreservedSexpr& atom)
{
  PreservedSexpr sign;
  sign.token = positive ? "pos" : "neg";
  PreservedSexpr result;
  result.atom = false;
  result.items = {std::move(sign), atom};
  return result;
}

std::string quotePreservedName(const std::string& value)
{
  std::string rendered = "\"";
  for (char ch : value) {
    if (ch == '\\' || ch == '"') rendered += '\\';
    rendered += ch;
  }
  return rendered + '"';
}

bool namedTermSexpr(
  const PreservedSexpr& value,
  const std::string& name)
{
  return sexprHead(value, "TMH") && value.items.size() == 2
    && value.items[1].atom
    && value.items[1].token == quotePreservedName(name);
}

bool binaryNamedApplicationSexpr(
  const PreservedSexpr& value,
  const std::string& name,
  PreservedSexpr& left,
  PreservedSexpr& right)
{
  if (!sexprHead(value, "AP") || value.items.size() != 3
      || !sexprHead(value.items[1], "AP")
      || value.items[1].items.size() != 3
      || !namedTermSexpr(value.items[1].items[1], name)) {
    return false;
  }
  left = value.items[1].items[2];
  right = value.items[2];
  return true;
}

bool binaryNamedApplicationSexprView(
  const PreservedSexpr& value,
  const std::string& name,
  const PreservedSexpr*& left,
  const PreservedSexpr*& right)
{
  if (!sexprHead(value, "AP") || value.items.size() != 3
      || !sexprHead(value.items[1], "AP")
      || value.items[1].items.size() != 3
      || !namedTermSexpr(value.items[1].items[1], name)) {
    return false;
  }
  left = &value.items[1].items[2];
  right = &value.items[2];
  return true;
}

bool preservedName(
  const PreservedSexpr& value,
  std::string& result);

bool namedExistsSexpr(
  const PreservedSexpr& value,
  std::string& variable,
  PreservedSexpr& type,
  PreservedSexpr& body)
{
  if (!sexprHead(value, "AP") || value.items.size() != 3
      || !namedTermSexpr(value.items[1], "vampire_exists_prop")
      || !sexprHead(value.items[2], "VLAMV")
      || value.items[2].items.size() != 4
      || !preservedName(value.items[2].items[1], variable)) {
    return false;
  }
  type = value.items[2].items[2];
  body = value.items[2].items[3];
  return true;
}

PreservedSexpr substituteNamedVariableSexpr(
  const PreservedSexpr& source,
  const std::string& variable,
  const PreservedSexpr& replacement)
{
  if (namedTermSexpr(source, variable)) return replacement;
  PreservedSexpr result = source;
  if (result.atom) return result;
  // A local Ivy substitution binds its keys over the body, while outer
  // specialization still applies to each replacement value.
  if (sexprHead(result, "substitute") && result.items.size() == 3
      && sexprHead(result.items[1], "subst")) {
    bool locallyBound = false;
    for (std::size_t index = 1;
         index < result.items[1].items.size();
         ++index) {
      PreservedSexpr& binding = result.items[1].items[index];
      std::string name;
      if (binding.atom || binding.items.size() != 2
          || !preservedName(binding.items[0], name)) {
        continue;
      }
      locallyBound = locallyBound || name == variable;
      binding.items[1] = substituteNamedVariableSexpr(
        binding.items[1], variable, replacement);
    }
    if (!locallyBound) {
      result.items[2] = substituteNamedVariableSexpr(
        result.items[2], variable, replacement);
    }
    return result;
  }
  if ((sexprHead(result, "ALLV")
       || sexprHead(result, "LAMV")
       || sexprHead(result, "VLAMV")
       || sexprHead(result, "term_lambda"))
      && result.items.size() == 4
      && result.items[1].atom
      && result.items[1].token == quotePreservedName(variable)) {
    return result;
  }
  for (std::size_t index = 1; index < result.items.size(); ++index) {
    result.items[index] = substituteNamedVariableSexpr(
      result.items[index], variable, replacement);
  }
  return result;
}

PreservedSexpr freshenProofProgramBindersWithEnvironment(
  PreservedSexpr source,
  std::size_t& fresh,
  std::map<std::string, std::vector<std::string>>& termRenamings,
  std::map<std::string, std::vector<std::string>>& proofRenamings)
{
  std::string termName;
  if (sexprHead(source, "TMH") && source.items.size() == 2
      && preservedName(source.items[1], termName)) {
    auto renamed = termRenamings.find(termName);
    if (renamed != termRenamings.end() && !renamed->second.empty()
        && renamed->second.back() != termName) {
      return quotedTmh(quotePreservedName(renamed->second.back()));
    }
    return source;
  }
  if (sexprHead(source, "hyp") && source.items.size() == 2) {
    std::string name;
    if (preservedName(source.items[1], name)) {
      auto renamed = proofRenamings.find(name);
      if (renamed != proofRenamings.end() && !renamed->second.empty()) {
        return preservedList(
          preservedAtom("hyp"),
          preservedAtom(quotePreservedName(renamed->second.back())));
      }
    }
    return source;
  }
  PreservedSexpr result = std::move(source);
  if (result.atom) return result;
  if ((sexprHead(result, "ALLV")
       || sexprHead(result, "LAMV")
       || sexprHead(result, "VLAMV"))
      && result.items.size() == 4) {
    std::string name;
    if (preservedName(result.items[1], name)) {
      result.items[2] = freshenProofProgramBindersWithEnvironment(
        std::move(result.items[2]), fresh, termRenamings, proofRenamings);
      termRenamings[name].push_back(name);
      result.items[3] = freshenProofProgramBindersWithEnvironment(
        std::move(result.items[3]), fresh, termRenamings, proofRenamings);
      termRenamings[name].pop_back();
      if (termRenamings[name].empty()) termRenamings.erase(name);
      return result;
    }
  }
  if (sexprHead(result, "term_lambda") && result.items.size() == 4) {
    std::string name;
    if (preservedName(result.items[1], name)) {
      const std::string replacement =
        "ivy_proof_alpha_t_" + std::to_string(fresh++);
      result.items[1] = preservedAtom(quotePreservedName(replacement));
      result.items[2] = freshenProofProgramBindersWithEnvironment(
        std::move(result.items[2]), fresh, termRenamings, proofRenamings);
      termRenamings[name].push_back(replacement);
      result.items[3] = freshenProofProgramBindersWithEnvironment(
        std::move(result.items[3]), fresh, termRenamings, proofRenamings);
      termRenamings[name].pop_back();
      if (termRenamings[name].empty()) termRenamings.erase(name);
      return result;
    }
  }
  if (sexprHead(result, "proof_lambda") && result.items.size() == 4) {
    std::string name;
    if (preservedName(result.items[1], name)) {
      const std::string replacement =
        "ivy_proof_alpha_h_" + std::to_string(fresh++);
      result.items[1] = preservedAtom(quotePreservedName(replacement));
      result.items[2] = freshenProofProgramBindersWithEnvironment(
        std::move(result.items[2]), fresh, termRenamings, proofRenamings);
      proofRenamings[name].push_back(replacement);
      result.items[3] = freshenProofProgramBindersWithEnvironment(
        std::move(result.items[3]), fresh, termRenamings, proofRenamings);
      proofRenamings[name].pop_back();
      if (proofRenamings[name].empty()) proofRenamings.erase(name);
      return result;
    }
  }
  for (std::size_t index = 1; index < result.items.size(); ++index) {
    result.items[index] = freshenProofProgramBindersWithEnvironment(
      std::move(result.items[index]), fresh, termRenamings, proofRenamings);
  }
  return result;
}

PreservedSexpr freshenProofProgramBinders(
  PreservedSexpr source,
  std::size_t& fresh)
{
  std::map<std::string, std::vector<std::string>> termRenamings;
  std::map<std::string, std::vector<std::string>> proofRenamings;
  return freshenProofProgramBindersWithEnvironment(
    std::move(source), fresh, termRenamings, proofRenamings);
}

PreservedSexpr replaceExactSexpr(
  const PreservedSexpr& source,
  const PreservedSexpr& needle,
  const PreservedSexpr& replacement,
  std::size_t& replacements)
{
  if (source == needle) {
    ++replacements;
    return replacement;
  }
  PreservedSexpr result = source;
  if (result.atom) return result;
  for (std::size_t index = 1; index < result.items.size(); ++index) {
    result.items[index] = replaceExactSexpr(
      result.items[index], needle, replacement, replacements);
  }
  return result;
}

bool containsExactSexpr(
  const PreservedSexpr& source,
  const PreservedSexpr& needle)
{
  if (source == needle) return true;
  if (source.atom) return false;
  for (std::size_t index = 1; index < source.items.size(); ++index) {
    if (containsExactSexpr(source.items[index], needle)) return true;
  }
  return false;
}

bool containsFreeNamedTermSexpr(
  const PreservedSexpr& source,
  const std::string& name)
{
  if (namedTermSexpr(source, name)) return true;
  if (source.atom) return false;
  if ((sexprHead(source, "ALLV")
       || sexprHead(source, "LAMV")
       || sexprHead(source, "VLAMV")
       || sexprHead(source, "term_lambda"))
      && source.items.size() == 4) {
    std::string binder;
    if (preservedName(source.items[1], binder) && binder == name) {
      return containsFreeNamedTermSexpr(source.items[2], name);
    }
  }
  for (std::size_t index = 1; index < source.items.size(); ++index) {
    if (containsFreeNamedTermSexpr(source.items[index], name)) return true;
  }
  return false;
}

PreservedSexpr betaNormalizeSexpr(const PreservedSexpr& source)
{
  PreservedSexpr result = source;
  if (result.atom) return result;
  for (std::size_t index = 1; index < result.items.size(); ++index) {
    result.items[index] = betaNormalizeSexpr(result.items[index]);
  }
  if (sexprHead(result, "AP") && result.items.size() == 3
      && (sexprHead(result.items[1], "LAMV")
          || sexprHead(result.items[1], "VLAMV"))
      && result.items[1].items.size() == 4) {
    std::string variable;
    if (preservedName(result.items[1].items[1], variable)) {
      return betaNormalizeSexpr(substituteNamedVariableSexpr(
        result.items[1].items[3], variable, result.items[2]));
    }
  }
  if (sexprHead(result, "term_apply") && result.items.size() == 3
      && sexprHead(result.items[1], "term_lambda")
      && result.items[1].items.size() == 4) {
    std::string variable;
    const PreservedSexpr* argument = &result.items[2];
    if (!argument->atom && argument->items.size() == 2
        && (sexprHead(*argument, "term")
            || sexprHead(*argument, "formula")
            || sexprHead(*argument, "literal")
            || sexprHead(*argument, "clause"))) {
      argument = &argument->items[1];
    }
    if (preservedName(result.items[1].items[1], variable)) {
      return betaNormalizeSexpr(substituteNamedVariableSexpr(
        result.items[1].items[3], variable, *argument));
    }
  }
  return result;
}

bool canonicalInhabitantSexpr(
  const PreservedSexpr& type,
  const std::string& stem,
  std::size_t depth,
  PreservedSexpr& result)
{
  PreservedSexprParser parser;
  std::string rendered;
  if (sexprHead(type, "PROP") && type.items.size() == 1) {
    rendered = "(TMH \"vampire_true\")";
  } else if (sexprHead(type, "SET") && type.items.size() == 1) {
    rendered = "(AP (TMH \"Eps_i\") (LAMV "
      + quotePreservedName(stem + "_set")
      + " (SET) (TMH \"vampire_true\")))";
  } else if (sexprHead(type, "AR") && type.items.size() == 3) {
    PreservedSexpr body;
    if (!canonicalInhabitantSexpr(
          type.items[2], stem, depth + 1, body)) {
      return false;
    }
    rendered = "(LAMV "
      + quotePreservedName(stem + "_arg" + std::to_string(depth))
      + " " + type.items[1].render() + " " + body.render() + ")";
  } else {
    return false;
  }
  return parser.parse(rendered, result);
}

bool preservedName(
  const PreservedSexpr& value,
  std::string& result)
{
  if (!value.atom || value.token.size() < 2
      || value.token.front() != '"' || value.token.back() != '"') {
    return false;
  }
  result.clear();
  for (std::size_t index = 1; index + 1 < value.token.size(); ++index) {
    if (value.token[index] == '\\' && index + 2 < value.token.size()) {
      ++index;
    }
    result += value.token[index];
  }
  return true;
}

bool alphaEquivalentSexpr(
  const PreservedSexpr& left,
  const PreservedSexpr& right,
  std::vector<std::string>& leftBinders,
  std::vector<std::string>& rightBinders)
{
  if (left.atom || right.atom) {
    return left.atom && right.atom && left.token == right.token;
  }
  const bool leftBinder = sexprHead(left, "ALLV")
    || sexprHead(left, "LAMV") || sexprHead(left, "VLAMV");
  const bool rightBinder = sexprHead(right, "ALLV")
    || sexprHead(right, "LAMV") || sexprHead(right, "VLAMV");
  if (leftBinder || rightBinder) {
    if (!leftBinder || !rightBinder || left.items.size() != 4
        || right.items.size() != 4
        || left.items[0].token != right.items[0].token
        || !alphaEquivalentSexpr(
             left.items[2], right.items[2], leftBinders, rightBinders)) {
      return false;
    }
    std::string leftName;
    std::string rightName;
    if (!preservedName(left.items[1], leftName)
        || !preservedName(right.items[1], rightName)) {
      return false;
    }
    leftBinders.push_back(leftName);
    rightBinders.push_back(rightName);
    const bool result = alphaEquivalentSexpr(
      left.items[3], right.items[3], leftBinders, rightBinders);
    leftBinders.pop_back();
    rightBinders.pop_back();
    return result;
  }
  if (sexprHead(left, "TMH") && left.items.size() == 2
      && sexprHead(right, "TMH") && right.items.size() == 2) {
    std::string leftName;
    std::string rightName;
    if (!preservedName(left.items[1], leftName)
        || !preservedName(right.items[1], rightName)) {
      return false;
    }
    auto boundIndex = [](const std::vector<std::string>& binders,
                         const std::string& name) {
      for (std::size_t offset = 0; offset < binders.size(); ++offset) {
        const std::size_t index = binders.size() - offset - 1;
        if (binders[index] == name) return static_cast<long>(offset);
      }
      return -1L;
    };
    const long leftIndex = boundIndex(leftBinders, leftName);
    const long rightIndex = boundIndex(rightBinders, rightName);
    return leftIndex >= 0 || rightIndex >= 0
      ? leftIndex == rightIndex
      : leftName == rightName;
  }
  if (left.items.size() != right.items.size()) return false;
  for (std::size_t index = 0; index < left.items.size(); ++index) {
    if (!alphaEquivalentSexpr(
          left.items[index], right.items[index],
          leftBinders, rightBinders)) {
      return false;
    }
  }
  return true;
}

bool alphaEquivalentSexpr(
  const PreservedSexpr& left,
  const PreservedSexpr& right)
{
  std::vector<std::string> leftBinders;
  std::vector<std::string> rightBinders;
  return alphaEquivalentSexpr(
    left, right, leftBinders, rightBinders);
}

bool containsNamedTermSexpr(
  const PreservedSexpr& value,
  const std::string& name)
{
  if (namedTermSexpr(value, name)) return true;
  if (value.atom) return false;
  for (const auto& item : value.items) {
    if (containsNamedTermSexpr(item, name)) return true;
  }
  return false;
}

PreservedSexpr normalizeFoolLogicalDefinitions(const PreservedSexpr& value)
{
  if (sexprHead(value, "TMH") && value.items.size() == 2) {
    if (namedTermSexpr(value, "f__true")) {
      return quotedTmh(quotePreservedName("vampire_true"));
    }
    if (namedTermSexpr(value, "f__false")) {
      return quotedTmh(quotePreservedName("vampire_false"));
    }
  }
  if (sexprHead(value, "AP") && value.items.size() == 3
      && namedTermSexpr(value.items[1], "vNOT")) {
    return preservedList(
      preservedAtom("IMP"),
      normalizeFoolLogicalDefinitions(value.items[2]),
      quotedTmh(quotePreservedName("vampire_false")));
  }
  if (sexprHead(value, "AP") && value.items.size() == 3
      && sexprHead(value.items[1], "AP")
      && value.items[1].items.size() == 3) {
    const PreservedSexpr& head = value.items[1].items[1];
    const PreservedSexpr left =
      normalizeFoolLogicalDefinitions(value.items[1].items[2]);
    const PreservedSexpr right =
      normalizeFoolLogicalDefinitions(value.items[2]);
    if (namedTermSexpr(head, "vIMP")) {
      return preservedList(preservedAtom("IMP"), left, right);
    }
    const char* replacement = namedTermSexpr(head, "vAND")
      ? "vampire_and"
      : namedTermSexpr(head, "vOR") ? "vampire_or" : nullptr;
    if (replacement != nullptr) {
      return preservedList(
        preservedAtom("AP"),
        preservedList(
          preservedAtom("AP"),
          quotedTmh(quotePreservedName(replacement)),
          left),
        right);
    }
  }
  if (value.atom) return value;
  PreservedSexpr result = value;
  for (PreservedSexpr& item : result.items) {
    item = normalizeFoolLogicalDefinitions(item);
  }
  return result;
}

bool buildFoolProgramNode(
  const PreservedSexpr& source,
  const PreservedSexpr& target,
  bool forward,
  const std::vector<std::pair<
    std::string, MegalodonKernelSyntax::RenderedKernelType>>& context,
  std::size_t& nextIndex,
  MegalodonKernelSyntax::RenderedKernelFoolProgramNode& node,
  const std::map<std::string, PreservedSexpr>* instantiations = nullptr,
  bool allowJunctionReassociation = false)
{
  node.index = nextIndex++;
  node.direction = forward ? "forward" : "backward";
  node.source = MegalodonKernelSyntax::formula(source.render());
  node.target = MegalodonKernelSyntax::formula(target.render());
  node.context = context;
  if (alphaEquivalentSexpr(source, target)) {
    node.rule = "identity";
    return true;
  }
  if (sexprHead(source, "ALLV") && source.items.size() == 4
      && sexprHead(target, "ALLV") && target.items.size() == 4
      && source.items[2] == target.items[2]) {
    std::string sourceName;
    std::string targetName;
    if (!preservedName(source.items[1], sourceName)
        || !preservedName(target.items[1], targetName)) {
      return false;
    }
    std::string binderName =
      "ivy_fool_bound" + std::to_string(node.index);
    const auto unavailable = [&](const std::string& name) {
      return containsNamedTermSexpr(source, name)
        || containsNamedTermSexpr(target, name)
        || std::any_of(
             context.begin(), context.end(),
             [&](const auto& binding) { return binding.first == name; });
    };
    while (unavailable(binderName)) binderName += '_';
    const auto binder = std::make_pair(
      binderName,
      MegalodonKernelSyntax::type(target.items[2].render()));
    node.rule = "forall";
    node.binders.push_back(binder);
    node.children.resize(1);
    auto bodyContext = context;
    bodyContext.push_back(binder);
    PreservedSexpr replacement;
    PreservedSexprParser parser;
    if (!parser.parse(
          "(TMH " + quotePreservedName(binderName) + ")", replacement)) {
      return false;
    }
    const PreservedSexpr sourceBody = substituteNamedVariableSexpr(
      source.items[3], sourceName, replacement);
    const PreservedSexpr targetBody = substituteNamedVariableSexpr(
      target.items[3], targetName, replacement);
    return buildFoolProgramNode(
      sourceBody, targetBody, forward,
      bodyContext, nextIndex, node.children[0], instantiations,
      allowJunctionReassociation);
  }
  if (forward && instantiations != nullptr
      && sexprHead(source, "ALLV") && source.items.size() == 4) {
    std::string sourceName;
    if (!preservedName(source.items[1], sourceName)) return false;
    const auto witness = instantiations->find(sourceName);
    if (witness != instantiations->end()) {
      node.rule = "forall_instantiate";
      node.terms.push_back(
        MegalodonKernelSyntax::term(witness->second.render()));
      node.children.resize(1);
      const PreservedSexpr sourceBody = substituteNamedVariableSexpr(
        source.items[3], sourceName, witness->second);
      return buildFoolProgramNode(
        sourceBody, target, forward,
        context, nextIndex, node.children[0], instantiations,
        allowJunctionReassociation);
    }
  }
  if (sexprHead(source, "IMP") && source.items.size() == 3
      && sexprHead(target, "IMP") && target.items.size() == 3) {
    node.rule = "implies";
    node.children.resize(2);
    return buildFoolProgramNode(
             source.items[1], target.items[1], !forward,
             context, nextIndex, node.children[0], instantiations,
             allowJunctionReassociation)
      && buildFoolProgramNode(
             source.items[2], target.items[2], forward,
             context, nextIndex, node.children[1], instantiations,
             allowJunctionReassociation);
  }
  PreservedSexpr sourceLeft;
  PreservedSexpr sourceRight;
  PreservedSexpr targetLeft;
  PreservedSexpr targetRight;
  for (const char* connective : {"vampire_and", "vampire_or"}) {
    if (binaryNamedApplicationSexpr(
          source, connective, sourceLeft, sourceRight)
        && binaryNamedApplicationSexpr(
          target, connective, targetLeft, targetRight)) {
      if (allowJunctionReassociation
          && connective == std::string("vampire_or")) {
        std::vector<PreservedSexpr> sourceLeaves;
        std::vector<PreservedSexpr> targetLeaves;
        const auto flatten = [&](const PreservedSexpr& value,
                                 std::vector<PreservedSexpr>& leaves,
                                 const auto& self) -> void {
          PreservedSexpr left;
          PreservedSexpr right;
          if (binaryNamedApplicationSexpr(
                value, "vampire_or", left, right)) {
            self(left, leaves, self);
            self(right, leaves, self);
          } else {
            leaves.push_back(value);
          }
        };
        flatten(source, sourceLeaves, flatten);
        flatten(target, targetLeaves, flatten);
        if (sourceLeaves.size() != targetLeaves.size()
            || sourceLeaves.size() < 2) {
          return false;
        }
        node.rule = "or_reassociate";
        node.children.resize(sourceLeaves.size());
        for (std::size_t index = 0; index < sourceLeaves.size(); ++index) {
          if (!buildFoolProgramNode(
                sourceLeaves[index], targetLeaves[index], forward,
                context, nextIndex, node.children[index], instantiations,
                allowJunctionReassociation)) {
            return false;
          }
        }
        return true;
      }
      node.rule = connective == std::string("vampire_and") ? "and" : "or";
      node.children.resize(2);
      return buildFoolProgramNode(
               sourceLeft, targetLeft, forward,
               context, nextIndex, node.children[0], instantiations,
               allowJunctionReassociation)
        && buildFoolProgramNode(
             sourceRight, targetRight, forward,
             context, nextIndex, node.children[1], instantiations,
             allowJunctionReassociation);
    }
  }
  std::string sourceExistsName;
  std::string targetExistsName;
  PreservedSexpr sourceExistsType;
  PreservedSexpr targetExistsType;
  PreservedSexpr sourceExistsBody;
  PreservedSexpr targetExistsBody;
  if (namedExistsSexpr(
        source, sourceExistsName, sourceExistsType, sourceExistsBody)
      && namedExistsSexpr(
        target, targetExistsName, targetExistsType, targetExistsBody)
      && sourceExistsType == targetExistsType) {
    std::string binderName =
      "ivy_fool_exists_bound" + std::to_string(node.index);
    const auto unavailable = [&](const std::string& name) {
      return containsNamedTermSexpr(source, name)
        || containsNamedTermSexpr(target, name)
        || std::any_of(
             context.begin(), context.end(),
             [&](const auto& binding) { return binding.first == name; });
    };
    while (unavailable(binderName)) binderName += '_';
    const auto binder = std::make_pair(
      binderName,
      MegalodonKernelSyntax::type(sourceExistsType.render()));
    node.rule = "exists";
    node.binders.push_back(binder);
    node.children.resize(1);
    auto bodyContext = context;
    bodyContext.push_back(binder);
    PreservedSexpr replacement;
    PreservedSexprParser parser;
    if (!parser.parse(
          "(TMH " + quotePreservedName(binderName) + ")", replacement)) {
      return false;
    }
    const PreservedSexpr sourceBody = substituteNamedVariableSexpr(
      sourceExistsBody, sourceExistsName, replacement);
    const PreservedSexpr targetBody = substituteNamedVariableSexpr(
      targetExistsBody, targetExistsName, replacement);
    return buildFoolProgramNode(
      sourceBody, targetBody, forward,
      bodyContext, nextIndex, node.children[0], instantiations,
      allowJunctionReassociation);
  }
  // Structural nodes above account for the overwhelmingly common case.
  // Normalizing a complete remaining subtree at every ancestor made this
  // recorder quadratic on large folded formulas.  Logical-definition
  // transport is an atomic fallback, so perform the expensive comparison
  // only after structural descent is unavailable.
  if (alphaEquivalentSexpr(
        normalizeFoolLogicalDefinitions(source),
        normalizeFoolLogicalDefinitions(target))) {
    node.rule = "logical_definition";
    return true;
  }
  PreservedSexpr sourceType;
  PreservedSexpr targetType;
  if (typedEqualitySexpr(source, sourceType, sourceLeft, sourceRight)
      && typedEqualitySexpr(target, targetType, targetLeft, targetRight)
      && sourceType == targetType
      && alphaEquivalentSexpr(sourceLeft, targetRight)
      && alphaEquivalentSexpr(sourceRight, targetLeft)) {
    node.rule = "equality_symmetry";
    return true;
  }
  PreservedSexpr type;
  PreservedSexpr left;
  PreservedSexpr right;
  if (!typedEqualitySexpr(target, type, left, right)
      || !sexprHead(type, "PROP") || type.items.size() != 1) {
    return false;
  }
  if ((namedTermSexpr(right, "vampire_true")
       || namedTermSexpr(right, "f__true"))
      && alphaEquivalentSexpr(source, left)) {
    node.rule = source == left
      ? "prop_eq_true" : "prop_eq_true_lambda_alpha";
    return true;
  }
  if ((namedTermSexpr(left, "vampire_true")
       || namedTermSexpr(left, "f__true"))
      && alphaEquivalentSexpr(source, right)) {
    node.rule = source == right
      ? "true_eq_prop" : "true_eq_prop_lambda_alpha";
    return true;
  }
  const bool rightIsTrue = namedTermSexpr(right, "vampire_true")
    || namedTermSexpr(right, "f__true");
  const bool leftIsTrue = namedTermSexpr(left, "vampire_true")
    || namedTermSexpr(left, "f__true");
  if (allowJunctionReassociation && (rightIsTrue || leftIsTrue)) {
    const PreservedSexpr& atom = rightIsTrue ? left : right;
    node.rule = rightIsTrue
      ? "prop_eq_true_transport" : "true_eq_prop_transport";
    node.children.resize(1);
    return buildFoolProgramNode(
      source, atom, forward, context, nextIndex, node.children[0],
      instantiations, allowJunctionReassociation);
  }
  if (allowJunctionReassociation && std::getenv("MEGALODON_CERT_DEBUG")) {
    std::cerr << "FOOL predicate-fold atomic mismatch"
              << "\n  source: " << source.render()
              << "\n  target: " << target.render() << std::endl;
  }
  return false;
}

class IvyClauseProofBuilder {
public:
  std::string parent(const std::string& name) const
  {
    return "(parent " + quote(name) + ")";
  }

  bool projection(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::vector<std::string>& source,
    const std::vector<std::string>& target,
    std::string& result)
  {
    return projectionFromProof(
      instantiate(parent(parentId), parentArguments), source, target, result);
  }

  bool projectionFromProof(
    const std::string& sourceProof,
    const std::vector<std::string>& source,
    const std::vector<std::string>& target,
    std::string& result)
  {
    if (source == target) {
      result = sourceProof;
      return true;
    }
    if (source.empty() || target.empty()) {
      return false;
    }
    result = eliminate(
      source,
      0,
      sourceProof,
      clauseTerm(target),
      [&](std::size_t index, const std::string& proof) {
        const auto found = std::find(
          target.begin(), target.end(), source[index]);
        return found == target.end()
          ? std::string()
          : inject(
              target,
              static_cast<std::size_t>(found - target.begin()),
              proof);
      });
    return !result.empty();
  }

  bool inequalitySplit(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::vector<std::string>& source,
    const std::vector<InequalitySplitProofItem>& splits,
    const std::vector<std::string>& target,
    std::string& result)
  {
    static const std::string propExtHash =
      "23ea4ad0d25e31cb704cd6f5752b77c544628e235c5c99d36647ab24d0d261c9";
    PreservedSexprParser parser;
    std::map<std::string, const InequalitySplitProofItem*> splitByLiteral;
    for (const auto& split : splits) {
      if (split.sourceLiteral.empty() || split.replacementLiteral.empty()
          || split.splitTerm.empty() || split.targetTerm.empty()
          || split.replacementProposition.empty()
          || !splitByLiteral.emplace(
                split.sourceLiteral, &split).second) {
        return false;
      }
    }
    if (splitByLiteral.empty()) return false;

    const auto truthProof = [&]() {
      const std::string proposition = fresh("ineq_true_prop");
      const std::string proof = fresh("ineq_true_proof");
      return termLambda(
        proposition,
        "(PROP)",
        proofLambda(
          proof,
          formula("(TMH " + quote(proposition) + ")"),
          hypothesis(proof)));
    };
    const auto propExt = [&](const PreservedSexpr& left,
                             const PreservedSexpr& right,
                             const std::string& leftToRight,
                             const std::string& rightToLeft) {
      return proofApply(
        proofApply(
          termApply(
            termApply(
              "(known " + quote(propExtHash) + ")",
              formula(left.render())),
            formula(right.render())),
          leftToRight),
        rightToLeft);
    };
    const auto replacementProof = [&](const InequalitySplitProofItem& split,
                                      const std::string& sourceProof) {
      PreservedSexpr sourceLiteral;
      PreservedSexpr replacementLiteral;
      PreservedSexpr splitTerm;
      PreservedSexpr targetTerm;
      PreservedSexpr named;
      PreservedSexpr equalityType;
      PreservedSexpr sourceLeft;
      PreservedSexpr sourceRight;
      PreservedSexpr replacementType;
      PreservedSexpr replacementLeft;
      PreservedSexpr replacementRight;
      if (!parser.parse(split.sourceLiteral, sourceLiteral)
          || !sexprHead(sourceLiteral, "neg")
          || sourceLiteral.items.size() != 2
          || !typedEqualitySexpr(
               sourceLiteral.items[1], equalityType,
               sourceLeft, sourceRight)
          || !parser.parse(split.replacementLiteral, replacementLiteral)
          || !sexprHead(replacementLiteral, "pos")
          || replacementLiteral.items.size() != 2
          || !typedEqualitySexpr(
               replacementLiteral.items[1], replacementType,
               replacementLeft, replacementRight)
          || !sexprHead(replacementType, "PROP")
          || replacementType.items.size() != 1
          || !parser.parse(split.splitTerm, splitTerm)
          || !parser.parse(split.targetTerm, targetTerm)
          || !parser.parse(split.replacementProposition, named)) {
        return std::string();
      }
      const bool trueOnLeft =
        namedTermSexpr(replacementLeft, "vampire_true")
        || namedTermSexpr(replacementLeft, "f__true");
      const bool trueOnRight =
        namedTermSexpr(replacementRight, "vampire_true")
        || namedTermSexpr(replacementRight, "f__true");
      const PreservedSexpr& declaredNamed =
        trueOnLeft ? replacementRight : replacementLeft;
      if (trueOnLeft == trueOnRight || declaredNamed != named) {
        return std::string();
      }

      std::string namedProof;
      if (sourceLeft == targetTerm && sourceRight == splitTerm) {
        namedProof = sourceProof;
      } else if (sourceLeft == splitTerm && sourceRight == targetTerm) {
        namedProof = equalitySymmetry(sourceLiteral, sourceProof);
      } else {
        return std::string();
      }
      if (namedProof.empty()) return namedProof;

      PreservedSexpr trueTerm;
      if (!parser.parse("(TMH \"vampire_true\")", trueTerm)) {
        return std::string();
      }
      const std::string namedHypothesis = fresh("ineq_named");
      const std::string trueHypothesis = fresh("ineq_true");
      const std::string namedToTrue = proofLambda(
        namedHypothesis, formula(named.render()), truthProof());
      const std::string trueToNamed = proofLambda(
        trueHypothesis, formula(trueTerm.render()), namedProof);
      return trueOnLeft
        ? propExt(trueTerm, named, trueToNamed, namedToTrue)
        : propExt(named, trueTerm, namedToTrue, trueToNamed);
    };

    std::vector<std::string> transformed;
    transformed.reserve(source.size());
    for (const std::string& literal : source) {
      auto split = splitByLiteral.find(literal);
      transformed.push_back(split == splitByLiteral.end()
        ? literal : split->second->replacementLiteral);
    }
    auto sortedTransformed = transformed;
    auto sortedTarget = target;
    std::sort(sortedTransformed.begin(), sortedTransformed.end());
    std::sort(sortedTarget.begin(), sortedTarget.end());
    if (sortedTransformed != sortedTarget) return false;

    result = eliminate(
      source,
      0,
      instantiate(parent(parentId), parentArguments),
      clauseTerm(target),
      [&](std::size_t index, const std::string& proof) {
        auto split = splitByLiteral.find(source[index]);
        if (split == splitByLiteral.end()) {
          return injectLiteral(target, source[index], proof);
        }
        const std::string direct = replacementProof(*split->second, proof);
        return direct.empty()
          ? std::string()
          : injectLiteral(
              target, split->second->replacementLiteral, direct);
      });
    return !result.empty();
  }

  bool inequalityNameIntro(
    const std::string& resultLiteralText,
    const std::string& namedPropositionText,
    const std::string& splitTermText,
    const std::string& splitTypeText,
    std::string& result)
  {
    static const std::string propExtHash =
      "23ea4ad0d25e31cb704cd6f5752b77c544628e235c5c99d36647ab24d0d261c9";
    PreservedSexprParser parser;
    PreservedSexpr literal;
    PreservedSexpr named;
    PreservedSexpr splitTerm;
    PreservedSexpr splitType;
    PreservedSexpr equalityType;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!parser.parse(resultLiteralText, literal)
        || !sexprHead(literal, "pos") || literal.items.size() != 2
        || !typedEqualitySexpr(
             literal.items[1], equalityType, left, right)
        || !sexprHead(equalityType, "PROP")
        || equalityType.items.size() != 1
        || !parser.parse(namedPropositionText, named)
        || !parser.parse(splitTermText, splitTerm)
        || !parser.parse(splitTypeText, splitType)) {
      return false;
    }
    const bool falseOnLeft = namedTermSexpr(left, "vampire_false")
      || namedTermSexpr(left, "f__false");
    const bool falseOnRight = namedTermSexpr(right, "vampire_false")
      || namedTermSexpr(right, "f__false");
    const PreservedSexpr& declaredNamed = falseOnLeft ? right : left;
    if (falseOnLeft == falseOnRight || declaredNamed != named) return false;

    const std::string relation = fresh("ineq_intro_relation");
    const std::string premise = fresh("ineq_intro_refl");
    const std::string relationTerm = "(TMH " + quote(relation) + ")";
    const std::string reflexiveAtom =
      "(AP (AP " + relationTerm + " " + splitTerm.render()
      + ") " + splitTerm.render() + ")";
    const std::string reflexivity = termLambda(
      relation,
      "(AR " + splitType.render()
        + " (AR " + splitType.render() + " (PROP)))",
      proofLambda(
        premise, formula(reflexiveAtom), hypothesis(premise)));
    const std::string namedHypothesis = fresh("ineq_intro_named");
    const std::string namedToFalse = proofLambda(
      namedHypothesis,
      formula(named.render()),
      proofApply(hypothesis(namedHypothesis), reflexivity));
    const std::string falseHypothesis = fresh("ineq_intro_false");
    const std::string falseToNamed = proofLambda(
      falseHypothesis,
      formula("(TMH \"vampire_false\")"),
      termApply(hypothesis(falseHypothesis), formula(named.render())));
    const auto propExt = [&](const PreservedSexpr& first,
                             const PreservedSexpr& second,
                             const std::string& firstToSecond,
                             const std::string& secondToFirst) {
      return proofApply(
        proofApply(
          termApply(
            termApply(
              "(known " + quote(propExtHash) + ")",
              formula(first.render())),
            formula(second.render())),
          firstToSecond),
        secondToFirst);
    };
    PreservedSexpr falseTerm;
    if (!parser.parse("(TMH \"vampire_false\")", falseTerm)) return false;
    result = falseOnLeft
      ? propExt(falseTerm, named, falseToNamed, namedToFalse)
      : propExt(named, falseTerm, namedToFalse, falseToNamed);
    return true;
  }

  bool cnfFormulaClause(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::string& sourceFormula,
    const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
    const std::vector<std::string>& target,
    std::string& result)
  {
    return !parentId.empty()
      && cnfFormulaClauseProof(
           instantiate(parent(parentId), parentArguments),
           sourceFormula,
           projection,
           target,
           result);
  }

  bool cnfFormulaClauseProof(
    const std::string& sourceProof,
    const std::string& sourceFormula,
    const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
    const std::vector<std::string>& target,
    std::string& result)
  {
    PreservedSexprParser parser;
    PreservedSexpr source;
    if (sourceProof.empty() || !parser.parse(sourceFormula, source)) {
      return false;
    }
    const std::string targetTerm = clauseTerm(target);
    std::function<std::string(
      const PreservedSexpr&,
      const MegalodonKernelSyntax::RenderedKernelCnfProjection&,
      const std::string&)> project =
      [&](const PreservedSexpr& current,
          const MegalodonKernelSyntax::RenderedKernelCnfProjection& node,
          const std::string& proof) -> std::string {
        if (node.kind == "false") {
          return node.children.empty() && target.empty()
              && (namedTermSexpr(current, "vampire_false")
                  || namedTermSexpr(current, "f__false"))
            ? proof
            : std::string();
        }
        if (node.kind == "literal") {
          if (!node.children.empty() || !node.hasSourceLiteral
              || node.resultLiteralIndex >= target.size()) {
            return std::string();
          }
          PreservedSexpr declared;
          if (!parser.parse(node.sourceLiteral.sexpr, declared)) {
            return std::string();
          }
          PreservedSexpr expected;
          if (sexprHead(current, "IMP") && current.items.size() == 3
              && (namedTermSexpr(current.items[2], "vampire_false")
                  || namedTermSexpr(current.items[2], "f__false"))) {
            expected = literalSexpr(false, current.items[1]);
          } else {
            expected = literalSexpr(true, current);
          }
          PreservedSexpr targetLiteral;
          return parser.parse(
                   target[node.resultLiteralIndex], targetLiteral)
              && alphaEquivalentSexpr(expected, declared)
              && alphaEquivalentSexpr(targetLiteral, declared)
            ? inject(target, node.resultLiteralIndex, proof)
            : std::string();
        }
        if (node.kind == "forall") {
          if (!node.hasVariable || !node.hasVariableType
              || node.children.size() != 1
              || !sexprHead(current, "ALLV")
              || current.items.size() != 4
              || !current.items[1].atom
              || current.items[1].token != quote(node.variable)) {
            return std::string();
          }
          PreservedSexpr type;
          PreservedSexpr witness;
          if (!parser.parse(node.variableType.sexpr, type)
              || !(current.items[2] == type)) {
            return std::string();
          }
          if (node.hasWitnessTerm) {
            if (!parser.parse(node.witnessTerm.sexpr, witness)) {
              return std::string();
            }
          } else if (!canonicalInhabitantSexpr(
                       type,
                       "ivy_cnf_inhabitant_" + node.variable,
                       0,
                       witness)) {
            return std::string();
          }
          const PreservedSexpr body = substituteNamedVariableSexpr(
            current.items[3], node.variable, witness);
          return project(
            body,
            node.children[0],
            termApply(proof, "(term " + witness.render() + ")"));
        }

        PreservedSexpr left;
        PreservedSexpr right;
        if (node.kind == "and_left" || node.kind == "and_right") {
          if (node.children.size() != 1
              || !binaryNamedApplicationSexpr(
                   current, "vampire_and", left, right)) {
            return std::string();
          }
          const std::string leftName = fresh("cnf_and_left");
          const std::string rightName = fresh("cnf_and_right");
          const bool selectLeft = node.kind == "and_left";
          const std::string selected = selectLeft
            ? hypothesis(leftName)
            : hypothesis(rightName);
          const std::string selectedProof = proofApply(
            termApply(proof, formula(selectLeft
              ? left.render() : right.render())),
            proofLambda(
              leftName,
              formula(left.render()),
              proofLambda(
                rightName,
                formula(right.render()),
                selected)));
          return project(
            selectLeft ? left : right,
            node.children[0],
            selectedProof);
        }
        if (node.kind == "or") {
          if (node.children.size() != 2
              || !binaryNamedApplicationSexpr(
                   current, "vampire_or", left, right)) {
            return std::string();
          }
          const std::string leftName = fresh("cnf_or_left");
          const std::string rightName = fresh("cnf_or_right");
          const std::string leftProof = project(
            left, node.children[0], hypothesis(leftName));
          const std::string rightProof = project(
            right, node.children[1], hypothesis(rightName));
          if (leftProof.empty() || rightProof.empty()) {
            return std::string();
          }
          return proofApply(
            proofApply(
              termApply(proof, targetTerm),
              proofLambda(
                leftName, formula(left.render()), leftProof)),
            proofLambda(
              rightName, formula(right.render()), rightProof));
        }
        return std::string();
      };

    result = project(
      source,
      projection,
      sourceProof);
    return !result.empty();
  }

  bool foolFormula(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
    std::string& result)
  {
    return !parentId.empty()
      && foolFormulaProof(
           program,
           instantiate(parent(parentId), parentArguments),
           result);
  }

  bool foolFormulaProof(
    const MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
    const std::string& inputProof,
    std::string& result)
  {
    static const std::string propExtHash =
      "23ea4ad0d25e31cb704cd6f5752b77c544628e235c5c99d36647ab24d0d261c9";
    PreservedSexprParser parser;
    const auto parseFormula = [&](const auto& formula, PreservedSexpr& parsed) {
      return parser.parse(formula.sexpr, parsed);
    };
    const auto directionIs = [](const auto& node, const char* direction) {
      return node.direction == direction;
    };
    const auto isTrue = [](const PreservedSexpr& formula) {
      return namedTermSexpr(formula, "vampire_true")
        || namedTermSexpr(formula, "f__true");
    };
    const auto truthProof = [&]() {
      const std::string propositionName = fresh("fool_true_prop");
      const std::string proofName = fresh("fool_true_proof");
      return termLambda(
        propositionName,
        "(PROP)",
        proofLambda(
          proofName,
          formula("(TMH " + quote(propositionName) + ")"),
          hypothesis(proofName)));
    };
    const auto propExt = [&](const PreservedSexpr& left,
                             const PreservedSexpr& right,
                             const std::string& leftToRight,
                             const std::string& rightToLeft) {
      return proofApply(
        proofApply(
          termApply(
            termApply(
              "(known " + quote(propExtHash) + ")",
              formula(left.render())),
            formula(right.render())),
          leftToRight),
        rightToLeft);
    };
    const auto andIntroduction = [&](const PreservedSexpr& left,
                                     const PreservedSexpr& right,
                                     const std::string& leftProof,
                                     const std::string& rightProof) {
      const std::string qName = fresh("fool_and_q");
      const std::string handlerName = fresh("fool_and_handler");
      const std::string q = "(TMH " + quote(qName) + ")";
      return termLambda(
        qName,
        "(PROP)",
        proofLambda(
          handlerName,
          formula(formulaImp(
            left.render(), formulaImp(right.render(), q))),
          proofApply(
            proofApply(hypothesis(handlerName), leftProof),
            rightProof)));
    };
    const auto andElimination = [&](const PreservedSexpr& left,
                                    const PreservedSexpr& right,
                                    const std::string& proof,
                                    bool selectLeft) {
      const std::string leftName = fresh("fool_and_left");
      const std::string rightName = fresh("fool_and_right");
      const PreservedSexpr& selected = selectLeft ? left : right;
      return proofApply(
        termApply(proof, formula(selected.render())),
        proofLambda(
          leftName,
          formula(left.render()),
          proofLambda(
            rightName,
            formula(right.render()),
            hypothesis(selectLeft ? leftName : rightName))));
    };
    const auto orIntroduction = [&](const PreservedSexpr& left,
                                    const PreservedSexpr& right,
                                    const std::string& proof,
                                    bool selectLeft) {
      const std::string qName = fresh("fool_or_q");
      const std::string leftName = fresh("fool_or_left");
      const std::string rightName = fresh("fool_or_right");
      const std::string q = "(TMH " + quote(qName) + ")";
      return termLambda(
        qName,
        "(PROP)",
        proofLambda(
          leftName,
          formula(formulaImp(left.render(), q)),
          proofLambda(
            rightName,
            formula(formulaImp(right.render(), q)),
            proofApply(
              hypothesis(selectLeft ? leftName : rightName),
              proof))));
    };

    std::function<std::string(
      const MegalodonKernelSyntax::RenderedKernelFoolProgramNode&,
      const std::string&)> convert =
      [&](const MegalodonKernelSyntax::RenderedKernelFoolProgramNode& node,
          const std::string& proof) -> std::string {
        PreservedSexpr source;
        PreservedSexpr target;
        if (!parseFormula(node.source, source)
            || !parseFormula(node.target, target)
            || (!directionIs(node, "forward")
                && !directionIs(node, "backward"))) {
          return std::string();
        }
        if (node.rule == "identity") {
          return alphaEquivalentSexpr(source, target) && node.binders.empty()
              && node.children.empty()
            ? proof
            : std::string();
        }
        if (node.rule == "logical_definition") {
          return alphaEquivalentSexpr(
                   normalizeFoolLogicalDefinitions(source),
                   normalizeFoolLogicalDefinitions(target))
              && node.binders.empty() && node.children.empty()
            ? proof
            : std::string();
        }
        if (node.rule == "forall") {
          if (node.binders.empty() || node.children.size() != 1) {
            return std::string();
          }
          PreservedSexpr sourceBody = source;
          PreservedSexpr targetBody = target;
          std::string instantiated = proof;
          for (const auto& [name, renderedType] : node.binders) {
            PreservedSexpr type;
            std::string sourceName;
            std::string targetName;
            if (!parser.parse(renderedType.sexpr, type)
                || !sexprHead(sourceBody, "ALLV")
                || !sexprHead(targetBody, "ALLV")
                || sourceBody.items.size() != 4
                || targetBody.items.size() != 4
                || !preservedName(sourceBody.items[1], sourceName)
                || !preservedName(targetBody.items[1], targetName)
                || !(sourceBody.items[2] == type)
                || !(targetBody.items[2] == type)) {
              return std::string();
            }
            PreservedSexpr replacement;
            if (!parser.parse(
                  "(TMH " + quotePreservedName(name) + ")", replacement)) {
              return std::string();
            }
            sourceBody = substituteNamedVariableSexpr(
              sourceBody.items[3], sourceName, replacement);
            targetBody = substituteNamedVariableSexpr(
              targetBody.items[3], targetName, replacement);
            instantiated = termApply(
              instantiated,
              "(term (TMH " + quote(name) + "))");
          }
          PreservedSexpr childSource;
          PreservedSexpr childTarget;
          const auto& child = node.children[0];
          if (!parseFormula(child.source, childSource)
              || !parseFormula(child.target, childTarget)
              || !(sourceBody == childSource)
              || !(targetBody == childTarget)
              || child.direction != node.direction) {
            return std::string();
          }
          std::string body = convert(child, instantiated);
          if (body.empty()) return body;
          for (auto iterator = node.binders.rbegin();
               iterator != node.binders.rend(); ++iterator) {
            body = termLambda(
              iterator->first, iterator->second.sexpr, body);
          }
          return body;
        }
        if (node.rule == "forall_instantiate") {
          if (!directionIs(node, "forward")
              || !node.binders.empty() || node.terms.size() != 1
              || node.children.size() != 1
              || !sexprHead(source, "ALLV") || source.items.size() != 4) {
            return std::string();
          }
          std::string sourceName;
          PreservedSexpr witness;
          if (!preservedName(source.items[1], sourceName)
              || !parser.parse(node.terms[0].sexpr, witness)) {
            return std::string();
          }
          const PreservedSexpr sourceBody = substituteNamedVariableSexpr(
            source.items[3], sourceName, witness);
          PreservedSexpr childSource;
          PreservedSexpr childTarget;
          const auto& child = node.children[0];
          if (!parseFormula(child.source, childSource)
              || !parseFormula(child.target, childTarget)
              || sourceBody != childSource || target != childTarget
              || child.direction != node.direction) {
            return std::string();
          }
          return convert(
            child,
            termApply(proof, "(term " + witness.render() + ")"));
        }
        if (node.rule == "implies") {
          if (!node.binders.empty() || node.children.size() != 2
              || !sexprHead(source, "IMP") || source.items.size() != 3
              || !sexprHead(target, "IMP") || target.items.size() != 3) {
            return std::string();
          }
          const auto& leftChild = node.children[0];
          const auto& rightChild = node.children[1];
          PreservedSexpr leftSource;
          PreservedSexpr leftTarget;
          PreservedSexpr rightSource;
          PreservedSexpr rightTarget;
          const std::string opposite = directionIs(node, "forward")
            ? "backward" : "forward";
          if (!parseFormula(leftChild.source, leftSource)
              || !parseFormula(leftChild.target, leftTarget)
              || !parseFormula(rightChild.source, rightSource)
              || !parseFormula(rightChild.target, rightTarget)
              || !(leftSource == source.items[1])
              || !(leftTarget == target.items[1])
              || !(rightSource == source.items[2])
              || !(rightTarget == target.items[2])
              || leftChild.direction != opposite
              || rightChild.direction != node.direction) {
            return std::string();
          }
          const PreservedSexpr& premise = directionIs(node, "forward")
            ? target.items[1] : source.items[1];
          const std::string premiseName = fresh("fool_implication");
          const std::string sourcePremise = convert(
            leftChild, hypothesis(premiseName));
          if (sourcePremise.empty()) return sourcePremise;
          const std::string sourceConclusion = proofApply(proof, sourcePremise);
          const std::string targetConclusion = convert(
            rightChild, sourceConclusion);
          return targetConclusion.empty()
            ? targetConclusion
            : proofLambda(
                premiseName, formula(premise.render()), targetConclusion);
        }

        if (node.rule == "and" || node.rule == "or") {
          if (!node.binders.empty() || node.children.size() != 2) {
            return std::string();
          }
          const std::string connective = node.rule == "and"
            ? "vampire_and" : "vampire_or";
          PreservedSexpr sourceLeft;
          PreservedSexpr sourceRight;
          PreservedSexpr targetLeft;
          PreservedSexpr targetRight;
          if (!binaryNamedApplicationSexpr(
                source, connective, sourceLeft, sourceRight)
              || !binaryNamedApplicationSexpr(
                target, connective, targetLeft, targetRight)) {
            return std::string();
          }
          const auto& leftChild = node.children[0];
          const auto& rightChild = node.children[1];
          PreservedSexpr leftSource;
          PreservedSexpr leftTarget;
          PreservedSexpr rightSource;
          PreservedSexpr rightTarget;
          if (!parseFormula(leftChild.source, leftSource)
              || !parseFormula(leftChild.target, leftTarget)
              || !parseFormula(rightChild.source, rightSource)
              || !parseFormula(rightChild.target, rightTarget)
              || leftSource != sourceLeft || leftTarget != targetLeft
              || rightSource != sourceRight || rightTarget != targetRight
              || leftChild.direction != node.direction
              || rightChild.direction != node.direction) {
            return std::string();
          }
          const PreservedSexpr& fromLeft = directionIs(node, "forward")
            ? sourceLeft : targetLeft;
          const PreservedSexpr& fromRight = directionIs(node, "forward")
            ? sourceRight : targetRight;
          const PreservedSexpr& toLeft = directionIs(node, "forward")
            ? targetLeft : sourceLeft;
          const PreservedSexpr& toRight = directionIs(node, "forward")
            ? targetRight : sourceRight;
          if (node.rule == "and") {
            const PreservedSexpr& fromFormula = directionIs(node, "forward")
              ? source : target;
            const std::string sourceName = fresh("fool_and_source");
            const std::string sourceProof = hypothesis(sourceName);
            const std::string leftProof = convert(
              leftChild,
              andElimination(fromLeft, fromRight, sourceProof, true));
            const std::string rightProof = convert(
              rightChild,
              andElimination(fromLeft, fromRight, sourceProof, false));
            if (leftProof.empty() || rightProof.empty()) {
              return std::string();
            }
            return proofApply(
              proofLambda(
                sourceName,
                formula(fromFormula.render()),
                andIntroduction(toLeft, toRight, leftProof, rightProof)),
              proof);
          }

          const PreservedSexpr& toFormula = directionIs(node, "forward")
            ? target : source;
          const std::string leftName = fresh("fool_or_source_left");
          const std::string rightName = fresh("fool_or_source_right");
          const std::string leftProof = convert(
            leftChild, hypothesis(leftName));
          const std::string rightProof = convert(
            rightChild, hypothesis(rightName));
          if (leftProof.empty() || rightProof.empty()) {
            return std::string();
          }
          return proofApply(
            proofApply(
              termApply(proof, formula(toFormula.render())),
              proofLambda(
                leftName,
                formula(fromLeft.render()),
                orIntroduction(toLeft, toRight, leftProof, true))),
            proofLambda(
              rightName,
              formula(fromRight.render()),
              orIntroduction(toLeft, toRight, rightProof, false)));
        }

        if (node.rule == "or_reassociate") {
          if (!node.binders.empty() || node.children.size() < 2) {
            return std::string();
          }
          const auto flatten = [&](const PreservedSexpr& value,
                                   std::vector<PreservedSexpr>& leaves,
                                   const auto& self) -> void {
            PreservedSexpr left;
            PreservedSexpr right;
            if (binaryNamedApplicationSexpr(
                  value, "vampire_or", left, right)) {
              self(left, leaves, self);
              self(right, leaves, self);
            } else {
              leaves.push_back(value);
            }
          };
          std::vector<PreservedSexpr> sourceLeaves;
          std::vector<PreservedSexpr> targetLeaves;
          flatten(source, sourceLeaves, flatten);
          flatten(target, targetLeaves, flatten);
          if (sourceLeaves.size() != node.children.size()
              || targetLeaves.size() != node.children.size()) {
            return std::string();
          }
          for (std::size_t index = 0; index < node.children.size(); ++index) {
            PreservedSexpr childSource;
            PreservedSexpr childTarget;
            if (!parseFormula(node.children[index].source, childSource)
                || !parseFormula(node.children[index].target, childTarget)
                || childSource != sourceLeaves[index]
                || childTarget != targetLeaves[index]
                || node.children[index].direction != node.direction) {
              return std::string();
            }
          }

          const PreservedSexpr& from = directionIs(node, "forward")
            ? source : target;
          const PreservedSexpr& to = directionIs(node, "forward")
            ? target : source;
          const auto leafCount = [&](const PreservedSexpr& value,
                                     const auto& self) -> std::size_t {
            PreservedSexpr left;
            PreservedSexpr right;
            return binaryNamedApplicationSexpr(
                     value, "vampire_or", left, right)
              ? self(left, self) + self(right, self)
              : 1;
          };
          const auto inject = [&](const PreservedSexpr& value,
                                  std::size_t leafIndex,
                                  const std::string& leafProof,
                                  const auto& self) -> std::string {
            PreservedSexpr left;
            PreservedSexpr right;
            if (!binaryNamedApplicationSexpr(
                  value, "vampire_or", left, right)) {
              return leafIndex == 0 ? leafProof : std::string();
            }
            const std::size_t leftCount = leafCount(left, leafCount);
            if (leafIndex < leftCount) {
              const std::string nested = self(
                left, leafIndex, leafProof, self);
              return nested.empty()
                ? nested
                : orIntroduction(left, right, nested, true);
            }
            const std::string nested = self(
              right, leafIndex - leftCount, leafProof, self);
            return nested.empty()
              ? nested
              : orIntroduction(left, right, nested, false);
          };
          const auto eliminate = [&](const PreservedSexpr& value,
                                     std::size_t offset,
                                     const std::string& valueProof,
                                     const auto& self) -> std::string {
            PreservedSexpr left;
            PreservedSexpr right;
            if (!binaryNamedApplicationSexpr(
                  value, "vampire_or", left, right)) {
              if (offset >= node.children.size()) return std::string();
              const std::string converted = convert(
                node.children[offset], valueProof);
              return converted.empty()
                ? converted
                : inject(to, offset, converted, inject);
            }
            const std::string leftName = fresh("fool_or_reassoc_left");
            const std::string rightName = fresh("fool_or_reassoc_right");
            const std::string leftProof = self(
              left, offset, hypothesis(leftName), self);
            const std::string rightProof = self(
              right,
              offset + leafCount(left, leafCount),
              hypothesis(rightName), self);
            if (leftProof.empty() || rightProof.empty()) {
              return std::string();
            }
            return proofApply(
              proofApply(
                termApply(valueProof, formula(to.render())),
                proofLambda(
                  leftName, formula(left.render()), leftProof)),
              proofLambda(
                rightName, formula(right.render()), rightProof));
          };
          return eliminate(from, 0, proof, eliminate);
        }

        if (node.rule == "exists") {
          if (node.binders.size() != 1 || node.children.size() != 1) {
            return std::string();
          }
          std::string sourceName;
          std::string targetName;
          PreservedSexpr sourceType;
          PreservedSexpr targetType;
          PreservedSexpr sourceBody;
          PreservedSexpr targetBody;
          if (!namedExistsSexpr(
                source, sourceName, sourceType, sourceBody)
              || !namedExistsSexpr(
                target, targetName, targetType, targetBody)
              || sourceType != targetType
              || node.binders[0].second.sexpr != sourceType.render()) {
            return std::string();
          }
          const std::string& binderName = node.binders[0].first;
          PreservedSexpr replacement;
          if (!parser.parse(
                "(TMH " + quote(binderName) + ")", replacement)) {
            return std::string();
          }
          sourceBody = substituteNamedVariableSexpr(
            sourceBody, sourceName, replacement);
          targetBody = substituteNamedVariableSexpr(
            targetBody, targetName, replacement);
          const auto& child = node.children[0];
          PreservedSexpr childSource;
          PreservedSexpr childTarget;
          if (!parseFormula(child.source, childSource)
              || !parseFormula(child.target, childTarget)
              || childSource != sourceBody || childTarget != targetBody
              || child.direction != node.direction) {
            return std::string();
          }
          const PreservedSexpr& fromBody = directionIs(node, "forward")
            ? sourceBody : targetBody;
          const PreservedSexpr& toBody = directionIs(node, "forward")
            ? targetBody : sourceBody;
          const std::string qName = fresh("fool_exists_q");
          const std::string handlerName = fresh("fool_exists_handler");
          const std::string bodyName = fresh("fool_exists_body");
          const std::string q = "(TMH " + quote(qName) + ")";
          const std::string converted = convert(
            child, hypothesis(bodyName));
          if (converted.empty()) return converted;
          const std::string continuation = termLambda(
            binderName,
            sourceType.render(),
            proofLambda(
              bodyName,
              formula(fromBody.render()),
              proofApply(
                termApply(
                  hypothesis(handlerName),
                  "(term (TMH " + quote(binderName) + "))"),
                converted)));
          return termLambda(
            qName,
            "(PROP)",
            proofLambda(
              handlerName,
              formula(
                "(ALLV " + quote(binderName) + " "
                + sourceType.render() + " (IMP "
                + toBody.render() + " " + q + "))"),
              proofApply(
                termApply(proof, formula(q)),
                continuation)));
        }

        if (node.rule == "equality_symmetry") {
          PreservedSexpr sourceType;
          PreservedSexpr sourceLeft;
          PreservedSexpr sourceRight;
          PreservedSexpr targetType;
          PreservedSexpr targetLeft;
          PreservedSexpr targetRight;
          if (!node.binders.empty() || !node.children.empty()
              || !typedEqualitySexpr(
                   source, sourceType, sourceLeft, sourceRight)
              || !typedEqualitySexpr(
                   target, targetType, targetLeft, targetRight)
              || !(sourceType == targetType)
              || !alphaEquivalentSexpr(sourceLeft, targetRight)
              || !alphaEquivalentSexpr(sourceRight, targetLeft)) {
            return std::string();
          }
          return directionIs(node, "forward")
            ? positiveEqualitySymmetry(
                sourceType, sourceLeft, sourceRight, proof)
            : positiveEqualitySymmetry(
                targetType, targetLeft, targetRight, proof);
        }

        const bool propEqTransport =
          node.rule == "prop_eq_true_transport";
        const bool trueEqTransport =
          node.rule == "true_eq_prop_transport";
        const bool propEqTrue = propEqTransport
          || node.rule == "prop_eq_true"
          || node.rule == "prop_eq_true_lambda_alpha";
        const bool trueEqProp = trueEqTransport
          || node.rule == "true_eq_prop"
          || node.rule == "true_eq_prop_lambda_alpha";
        const bool transported = propEqTransport || trueEqTransport;
        PreservedSexpr equalityType;
        PreservedSexpr equalityLeft;
        PreservedSexpr equalityRight;
        if ((!propEqTrue && !trueEqProp)
            || !node.binders.empty()
            || node.children.size() != (transported ? 1 : 0)
            || !typedEqualitySexpr(
                 target, equalityType, equalityLeft, equalityRight)
            || !sexprHead(equalityType, "PROP")
            || equalityType.items.size() != 1
            || (propEqTrue && !isTrue(equalityRight))
            || (trueEqProp && !isTrue(equalityLeft))) {
          return std::string();
        }
        const PreservedSexpr& atom = propEqTrue
          ? equalityLeft : equalityRight;
        const PreservedSexpr& trueTerm = propEqTrue
          ? equalityRight : equalityLeft;
        if (!transported && !alphaEquivalentSexpr(source, atom)) {
          return std::string();
        }
        if (transported) {
          PreservedSexpr childSource;
          PreservedSexpr childTarget;
          if (!parseFormula(node.children[0].source, childSource)
              || !parseFormula(node.children[0].target, childTarget)
              || childSource != source || childTarget != atom
              || node.children[0].direction != node.direction) {
            return std::string();
          }
        }
        const std::string atomProofName = fresh("fool_atom");
        const std::string trueProofName = fresh("fool_true");
        const std::string atomToTrue = proofLambda(
          atomProofName, formula(atom.render()), truthProof());
        if (directionIs(node, "forward")) {
          const std::string atomProof = transported
            ? convert(node.children[0], proof) : proof;
          if (atomProof.empty()) return atomProof;
          const std::string trueToAtom = proofLambda(
            trueProofName, formula(trueTerm.render()), atomProof);
          return propEqTrue
            ? propExt(atom, trueTerm, atomToTrue, trueToAtom)
            : propExt(trueTerm, atom, trueToAtom, atomToTrue);
        }

        const std::string leftName = fresh("fool_eq_left");
        const std::string rightName = fresh("fool_eq_right");
        const std::string motiveBody = propEqTrue
          ? formulaImp(
              "(TMH " + quote(leftName) + ")",
              "(TMH " + quote(rightName) + ")")
          : formulaImp(
              "(TMH " + quote(rightName) + ")",
              "(TMH " + quote(leftName) + ")");
        const std::string motive =
          "(term (LAMV " + quote(leftName) + " (PROP)"
          + " (LAMV " + quote(rightName) + " (PROP) "
          + motiveBody + ")))";
        const std::string atomProof = proofApply(
          proofApply(termApply(proof, motive), atomToTrue),
          truthProof());
        return transported
          ? convert(node.children[0], atomProof) : atomProof;
      };

    if (inputProof.empty() || program.version != "ivy_fool_formula_v1") {
      return false;
    }
    result = convert(program.root, inputProof);
    return !result.empty();
  }

  bool ennfFormula(
    const std::string& stepId,
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const MegalodonKernelSyntax::RenderedKernelEnnfTrace& trace,
    std::string& result,
    std::string& error)
  {
    static const std::string falseFormula = "(TMH \"vampire_false\")";
    static const std::string dnegHash =
      "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0";
    PreservedSexprParser parser;
    _freshPrefix = "ivy_ennf_" + stepId + "_";
    _reservedNames.clear();

    const auto reserveNames = [&](const PreservedSexpr& value, const auto& self) -> void {
      if (value.atom) {
        std::string name;
        if (preservedName(value, name)) _reservedNames.insert(name);
        return;
      }
      for (const auto& item : value.items) self(item, self);
    };
    std::function<bool(const MegalodonKernelSyntax::RenderedKernelEnnfTrace&)>
      reserveTrace;
    reserveTrace = [&](const auto& node) {
      PreservedSexpr source;
      PreservedSexpr target;
      if (!node.hasSourceFormula || !node.hasResultFormula
          || !parser.parse(node.sourceFormula.sexpr, source)
          || !parser.parse(node.resultFormula.sexpr, target)) {
        return false;
      }
      reserveNames(source, reserveNames);
      reserveNames(target, reserveNames);
      for (const auto& child : node.children) {
        if (!reserveTrace(child)) return false;
      }
      return true;
    };
    if (stepId.empty() || parentId.empty() || !reserveTrace(trace)) {
      error = "ENNF recorder trace has no exact producer formulas";
      return false;
    }

    const auto rawTerm = [](const std::string& value) {
      return "(term " + value + ")";
    };
    const auto known = [&](const std::string& name) {
      return "(known " + quote(name) + ")";
    };
    const auto namedTerm = [&](const std::string& name) {
      return "(TMH " + quote(name) + ")";
    };
    const auto isFalse = [](const PreservedSexpr& value) {
      return namedTermSexpr(value, "vampire_false")
        || namedTermSexpr(value, "f__false");
    };
    const auto parseRendered = [&](const std::string& value,
                                   PreservedSexpr& parsed) {
      return parser.parse(value, parsed);
    };
    const auto parseNode = [&](const auto& node,
                               PreservedSexpr& source,
                               PreservedSexpr& target) {
      return node.hasSourceFormula && node.hasResultFormula
        && parseRendered(node.sourceFormula.sexpr, source)
        && parseRendered(node.resultFormula.sexpr, target);
    };
    const auto notFormula = [&](const PreservedSexpr& value,
                                PreservedSexpr& resultFormula) {
      return parseRendered(
        formulaImp(value.render(), falseFormula), resultFormula);
    };
    const auto primitiveIs = [](const auto& node,
                                const std::string& connective,
                                bool polarity) {
      return node.sourceConnective == connective
        && node.polarity == polarity
        && node.primitive == "ennf_" + connective
          + (polarity ? "_positive" : "_negative");
    };
    const auto orIntroduction = [&](const PreservedSexpr& left,
                                    const PreservedSexpr& right,
                                    const std::string& proof,
                                    bool injectLeft) {
      const std::string qName = fresh("or_q");
      const std::string leftName = fresh("or_left");
      const std::string rightName = fresh("or_right");
      const std::string q = namedTerm(qName);
      return termLambda(
        qName,
        "(PROP)",
        proofLambda(
          leftName,
          formula(formulaImp(left.render(), q)),
          proofLambda(
            rightName,
            formula(formulaImp(right.render(), q)),
            proofApply(hypothesis(injectLeft ? leftName : rightName), proof))));
    };
    const auto andIntroduction = [&](const PreservedSexpr& left,
                                     const PreservedSexpr& right,
                                     const std::string& leftProof,
                                     const std::string& rightProof) {
      const std::string qName = fresh("and_q");
      const std::string handlerName = fresh("and_handler");
      const std::string q = namedTerm(qName);
      return termLambda(
        qName,
        "(PROP)",
        proofLambda(
          handlerName,
          formula(formulaImp(
            left.render(), formulaImp(right.render(), q))),
          proofApply(
            proofApply(hypothesis(handlerName), leftProof),
            rightProof)));
    };
    const auto dneg = [&](const PreservedSexpr& proposition,
                          const std::string& doubleNegation) {
      return proofApply(
        termApply(known(dnegHash), formula(proposition.render())),
        doubleNegation);
    };
    const auto notForallKnown = [](const std::string& type) {
      if (type == "(SET)") return std::string("vampire_not_forall_exists_set");
      if (type == "(PROP)") return std::string("vampire_not_forall_exists_prop");
      if (type == "(AR (SET) (PROP))") {
        return std::string("vampire_not_forall_exists_set_prop");
      }
      if (type == "(AR (SET) (SET))") {
        return std::string("vampire_not_forall_exists_set_set");
      }
      if (type == "(AR (SET) (AR (SET) (PROP)))") {
        return std::string("vampire_not_forall_exists_set_set_prop");
      }
      return std::string();
    };
    const auto quantified = [&](const PreservedSexpr& value,
                                const char* head,
                                std::string& name,
                                PreservedSexpr& type,
                                PreservedSexpr& body) {
      if (!sexprHead(value, head) || value.items.size() != 4
          || !preservedName(value.items[1], name)) {
        return false;
      }
      type = value.items[2];
      body = value.items[3];
      return true;
    };
    const auto existsFormula = [&](const PreservedSexpr& value,
                                   std::string& name,
                                   PreservedSexpr& type,
                                   PreservedSexpr& body) {
      return sexprHead(value, "AP") && value.items.size() == 3
        && namedTermSexpr(value.items[1], "vampire_exists_prop")
        && quantified(value.items[2], "VLAMV", name, type, body);
    };
    std::function<std::string(
      const MegalodonKernelSyntax::RenderedKernelEnnfTrace&,
      const std::string&)> convert;
    convert = [&](const auto& node, const std::string& input) -> std::string {
      PreservedSexpr source;
      PreservedSexpr target;
      if (!parseNode(node, source, target)
          || !primitiveIs(node, node.sourceConnective, node.polarity)) {
        if (error.empty()) error = "ENNF node has inconsistent exact metadata";
        return std::string();
      }
      const auto fail = [&](const std::string& message) {
        if (error.empty()) {
          error = "ENNF " + node.primitive + " node "
            + std::to_string(node.index) + " " + message;
        }
        return std::string();
      };
      const auto requireChild = [&](std::size_t index,
                                    const PreservedSexpr& childSource,
                                    bool childPolarity) {
        if (index >= node.children.size()) return false;
        PreservedSexpr childTarget;
        PreservedSexpr declaredSource;
        return parseNode(node.children[index], declaredSource, childTarget)
          && declaredSource == childSource
          && node.children[index].polarity == childPolarity;
      };

      if (node.sourceConnective == "literal"
          || node.sourceConnective == "bool_term"
          || node.sourceConnective == "true"
          || node.sourceConnective == "false") {
        if (!node.children.empty()) return fail("has children");
        PreservedSexpr expected = source;
        if (!node.polarity && !notFormula(source, expected)) {
          return fail("cannot render its negative leaf");
        }
        return target == expected ? input : fail("has the wrong leaf result");
      }

      if (node.sourceConnective == "not") {
        if (!sexprHead(source, "IMP") || source.items.size() != 3
            || !isFalse(source.items[2]) || node.children.size() != 1
            || !requireChild(0, source.items[1], !node.polarity)) {
          return fail("does not expose one negated child");
        }
        PreservedSexpr childSource;
        PreservedSexpr childTarget;
        if (!parseNode(node.children[0], childSource, childTarget)
            || target != childTarget) {
          return fail("does not preserve its child result");
        }
        const std::string childInput = node.polarity
          ? input : dneg(source.items[1], input);
        return convert(node.children[0], childInput);
      }

      if (node.sourceConnective == "imp") {
        if (!sexprHead(source, "IMP") || source.items.size() != 3
            || node.children.size() != 2
            || !requireChild(0, source.items[1], !node.polarity)
            || !requireChild(1, source.items[2], node.polarity)) {
          return fail("does not expose its two polarity-switched children");
        }
        PreservedSexpr leftTarget;
        PreservedSexpr rightTarget;
        PreservedSexpr ignored;
        if (!parseNode(node.children[0], ignored, leftTarget)
            || !parseNode(node.children[1], ignored, rightTarget)) {
          return fail("has malformed child formulas");
        }
        PreservedSexpr declaredLeft;
        PreservedSexpr declaredRight;
        if (node.polarity) {
          if (!binaryNamedApplicationSexpr(
                target, "vampire_or", declaredLeft, declaredRight)
              || declaredLeft != leftTarget || declaredRight != rightTarget) {
            return fail("does not declare the child disjunction result");
          }
          const std::string positiveName = fresh("imp_source_left");
          const std::string rightProof = convert(
            node.children[1],
            proofApply(input, hypothesis(positiveName)));
          if (rightProof.empty()) return rightProof;
          const std::string positiveProof = orIntroduction(
            leftTarget, rightTarget, rightProof, false);
          const std::string negativeName = fresh("imp_not_left");
          const std::string leftProof = convert(
            node.children[0], hypothesis(negativeName));
          if (leftProof.empty()) return leftProof;
          const std::string negativeProof = orIntroduction(
            leftTarget, rightTarget, leftProof, true);
          return excludedMiddle(
            source.items[1].render(),
            target.render(),
            positiveName,
            positiveProof,
            negativeName,
            negativeProof);
        }

        if (!binaryNamedApplicationSexpr(
              target, "vampire_and", declaredLeft, declaredRight)
            || declaredLeft != leftTarget || declaredRight != rightTarget) {
          return fail("does not declare the child conjunction result");
        }
        PreservedSexpr notLeft;
        if (!notFormula(source.items[1], notLeft)) {
          return fail("cannot render its negated premise");
        }
        const std::string notLeftName = fresh("imp_not_left");
        const std::string leftAssumption = fresh("imp_left");
        const std::string falseProof = proofApply(
          hypothesis(notLeftName), hypothesis(leftAssumption));
        const std::string sourceImplication = proofLambda(
          leftAssumption,
          formula(source.items[1].render()),
          termApply(falseProof, formula(source.items[2].render())));
        const std::string leftDoubleNegation = proofLambda(
          notLeftName,
          formula(notLeft.render()),
          proofApply(input, sourceImplication));
        const std::string sourceLeftProof = dneg(
          source.items[1], leftDoubleNegation);
        const std::string leftProof = convert(
          node.children[0], sourceLeftProof);
        if (leftProof.empty()) return leftProof;
        const std::string rightAssumption = fresh("imp_right");
        const std::string unusedLeft = fresh("imp_unused_left");
        const std::string notRightProof = proofLambda(
          rightAssumption,
          formula(source.items[2].render()),
          proofApply(
            input,
            proofLambda(
              unusedLeft,
              formula(source.items[1].render()),
              hypothesis(rightAssumption))));
        const std::string rightProof = convert(
          node.children[1], notRightProof);
        return rightProof.empty()
          ? rightProof
          : andIntroduction(leftTarget, rightTarget, leftProof, rightProof);
      }

      if (node.sourceConnective == "forall") {
        std::string sourceName;
        PreservedSexpr sourceType;
        PreservedSexpr sourceBody;
        if (!quantified(
              source, "ALLV", sourceName, sourceType, sourceBody)
            || node.children.size() != 1
            || !requireChild(0, sourceBody, node.polarity)) {
          return fail("does not expose one quantified child");
        }
        PreservedSexpr childSource;
        PreservedSexpr childTarget;
        if (!parseNode(node.children[0], childSource, childTarget)) {
          return fail("has malformed quantified child formulas");
        }
        if (node.polarity) {
          std::string targetName;
          PreservedSexpr targetType;
          PreservedSexpr targetBody;
          if (!quantified(
                target, "ALLV", targetName, targetType, targetBody)
              || sourceName != targetName || sourceType != targetType
              || targetBody != childTarget) {
            return fail("does not preserve its universal binder");
          }
          const std::string bodyProof = convert(
            node.children[0],
            termApply(input, rawTerm(namedTerm(sourceName))));
          return bodyProof.empty()
            ? bodyProof
            : termLambda(sourceName, sourceType.render(), bodyProof);
        }

        std::string targetName;
        PreservedSexpr targetType;
        PreservedSexpr targetBody;
        if (!existsFormula(target, targetName, targetType, targetBody)
            || sourceName != targetName || sourceType != targetType
            || targetBody != childTarget) {
          return fail("does not declare the child existential result");
        }
        const std::string theoremName = notForallKnown(sourceType.render());
        if (theoremName.empty()) {
          return fail("uses a quantifier type without a declared not-forall principle");
        }
        const std::string sourcePredicate =
          "(LAMV " + quote(sourceName) + " " + sourceType.render()
          + " " + sourceBody.render() + ")";
        const std::string targetPredicate =
          "(LAMV " + quote(targetName) + " " + targetType.render()
          + " " + targetBody.render() + ")";
        const std::string sourceNotName = fresh("forall_not_body");
        const std::string childProof = convert(
          node.children[0], hypothesis(sourceNotName));
        if (childProof.empty()) return childProof;
        const std::string pointwise = termLambda(
          sourceName,
          sourceType.render(),
          proofLambda(
            sourceNotName,
            formula(formulaImp(sourceBody.render(), falseFormula)),
            childProof));
        return proofApply(
          proofApply(
            termApply(
              termApply(
                known(theoremName), formula(sourcePredicate)),
              formula(targetPredicate)),
            pointwise),
          input);
      }

      return fail("is outside the direct producer ENNF basis");
    };

    std::string parentProof = instantiate(parent(parentId), parentArguments);
    result = convert(trace, parentProof);
    return !result.empty();
  }

  bool resolution(
    const std::string& leftParent,
    const std::vector<std::string>& leftParentArguments,
    const std::vector<std::string>& left,
    std::size_t leftPivot,
    const std::string& rightParent,
    const std::vector<std::string>& rightParentArguments,
    const std::vector<std::string>& right,
    std::size_t rightPivot,
    const std::vector<std::string>& target,
    std::string& result)
  {
    if (leftPivot >= left.size() || rightPivot >= right.size()
        || complement(left[leftPivot]) != right[rightPivot]) {
      return false;
    }
    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      left,
      0,
      instantiate(parent(leftParent), leftParentArguments),
      targetTerm,
      [&](std::size_t leftIndex, const std::string& leftProof) {
        if (leftIndex != leftPivot) {
          return injectLiteral(target, left[leftIndex], leftProof);
        }
        return eliminate(
          right,
          0,
          instantiate(parent(rightParent), rightParentArguments),
          targetTerm,
          [&](std::size_t rightIndex, const std::string& rightProof) {
            if (rightIndex != rightPivot) {
              return injectLiteral(target, right[rightIndex], rightProof);
            }
            const bool leftPositive = left[leftPivot].compare(0, 5, "(pos ") == 0;
            const std::string contradiction = leftPositive
              ? proofApply(rightProof, leftProof)
              : proofApply(leftProof, rightProof);
            return target.empty()
              ? contradiction
              : termApply(contradiction, targetTerm);
          });
      });
    return !result.empty();
  }

  bool equalityResolution(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::vector<std::string>& source,
    std::size_t selected,
    const std::vector<std::string>& target,
    std::string& result)
  {
    if (selected >= source.size()) return false;
    std::vector<std::string> expected = source;
    expected.erase(expected.begin() + selected);
    std::vector<std::string> expectedSorted = expected;
    std::vector<std::string> targetSorted = target;
    std::sort(expectedSorted.begin(), expectedSorted.end());
    std::sort(targetSorted.begin(), targetSorted.end());
    if (expectedSorted != targetSorted) return false;

    PreservedSexprParser parser;
    PreservedSexpr literal;
    PreservedSexpr type;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!parser.parse(source[selected], literal)
        || !sexprHead(literal, "neg") || literal.items.size() != 2
        || !typedEqualitySexpr(literal.items[1], type, left, right)
        || !(left == right)) {
      return false;
    }

    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      source,
      0,
      instantiate(parent(parentId), parentArguments),
      targetTerm,
      [&](std::size_t index, const std::string& proof) {
        if (index != selected) {
          return injectLiteral(target, source[index], proof);
        }
        const std::string relationName = fresh("eq_relation");
        const std::string premiseName = fresh("eq_premise");
        const std::string relation = "(TMH " + quote(relationName) + ")";
        const std::string premise =
          "(AP (AP " + relation + " " + left.render() + ") "
          + right.render() + ")";
        const std::string reflexivity = termLambda(
          relationName,
          "(AR " + type.render() + " (AR " + type.render() + " (PROP)))",
          proofLambda(
            premiseName,
            formula(premise),
            hypothesis(premiseName)));
        const std::string contradiction = proofApply(proof, reflexivity);
        return target.empty()
          ? contradiction
          : termApply(contradiction, targetTerm);
      });
    return !result.empty();
  }

  bool truthConflict(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::vector<std::string>& source,
    std::size_t selected,
    const std::vector<std::string>& target,
    std::string& result)
  {
    if (selected >= source.size()) return false;
    std::vector<std::string> expected = source;
    expected.erase(expected.begin() + selected);
    std::vector<std::string> expectedSorted = expected;
    std::vector<std::string> targetSorted = target;
    std::sort(expectedSorted.begin(), expectedSorted.end());
    std::sort(targetSorted.begin(), targetSorted.end());
    if (expectedSorted != targetSorted) return false;

    PreservedSexprParser parser;
    PreservedSexpr literal;
    PreservedSexpr type;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!parser.parse(source[selected], literal)
        || !sexprHead(literal, "pos") || literal.items.size() != 2
        || !typedEqualitySexpr(literal.items[1], type, left, right)
        || !sexprHead(type, "PROP") || type.items.size() != 1) {
      return false;
    }
    auto isNamedTerm = [](const PreservedSexpr& term,
                          const std::string& name) {
      return sexprHead(term, "TMH") && term.items.size() == 2
        && term.items[1].atom && term.items[1].token == quote(name);
    };
    const bool leftTrue =
      isNamedTerm(left, "f__true") || isNamedTerm(left, "vampire_true");
    const bool leftFalse =
      isNamedTerm(left, "f__false") || isNamedTerm(left, "vampire_false");
    const bool rightTrue =
      isNamedTerm(right, "f__true") || isNamedTerm(right, "vampire_true");
    const bool rightFalse =
      isNamedTerm(right, "f__false") || isNamedTerm(right, "vampire_false");
    if (!((leftTrue && rightFalse) || (leftFalse && rightTrue))) {
      return false;
    }

    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      source,
      0,
      instantiate(parent(parentId), parentArguments),
      targetTerm,
      [&](std::size_t index, const std::string& proof) {
        if (index != selected) {
          return injectLiteral(target, source[index], proof);
        }
        const std::string leftName = fresh("truth_left");
        const std::string rightName = fresh("truth_right");
        const std::string propositionName = fresh("truth_proposition");
        const std::string premiseName = fresh("truth_premise");
        const std::string motive =
          "(term (LAMV " + quote(leftName) + " (PROP)"
          + " (LAMV " + quote(rightName) + " (PROP) (TMH "
          + quote(leftTrue ? leftName : rightName) + "))))";
        const std::string trueProof = termLambda(
          propositionName,
          "(PROP)",
          proofLambda(
            premiseName,
            formula("(TMH " + quote(propositionName) + ")"),
            hypothesis(premiseName)));
        const std::string contradiction = proofApply(
          termApply(proof, motive), trueProof);
        return target.empty()
          ? contradiction
          : termApply(contradiction, targetTerm);
      });
    return !result.empty();
  }

  bool boolSimplification(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::vector<std::string>& source,
    std::size_t selected,
    const std::vector<unsigned>& position,
    const std::string& fromText,
    const std::string& toText,
    const std::vector<std::string>& target,
    std::string& result)
  {
    static const std::string propExtHash =
      "23ea4ad0d25e31cb704cd6f5752b77c544628e235c5c99d36647ab24d0d261c9";
    if (parentId.empty() || selected >= source.size()) return false;

    PreservedSexprParser parser;
    PreservedSexpr selectedLiteral;
    PreservedSexpr from;
    PreservedSexpr to;
    PreservedSexpr rewrittenAtom;
    PreservedSexpr selectedAtPosition;
    if (!parser.parse(source[selected], selectedLiteral)
        || (!sexprHead(selectedLiteral, "pos")
            && !sexprHead(selectedLiteral, "neg"))
        || selectedLiteral.items.size() != 2
        || !parser.parse(fromText, from)
        || !parser.parse(toText, to)
        || !replaceSexprTermAtPosition(
             selectedLiteral.items[1], position, to,
             rewrittenAtom, &selectedAtPosition)
        || selectedAtPosition != from) {
      return false;
    }
    const PreservedSexpr rewrittenLiteral = literalSexpr(
      sexprHead(selectedLiteral, "pos"), rewrittenAtom);
    std::vector<std::string> expected = source;
    expected[selected] = rewrittenLiteral.render();
    auto sortedExpected = expected;
    auto sortedTarget = target;
    std::sort(sortedExpected.begin(), sortedExpected.end());
    std::sort(sortedTarget.begin(), sortedTarget.end());
    if (sortedExpected != sortedTarget) return false;

    const auto isTrue = [](const PreservedSexpr& value) {
      return namedTermSexpr(value, "vampire_true")
        || namedTermSexpr(value, "f__true");
    };
    const auto isFalse = [](const PreservedSexpr& value) {
      return namedTermSexpr(value, "vampire_false")
        || namedTermSexpr(value, "f__false");
    };
    const auto truthProof = [&]() {
      const std::string proposition = fresh("bool_true_prop");
      const std::string premise = fresh("bool_true_proof");
      return termLambda(
        proposition,
        "(PROP)",
        proofLambda(
          premise,
          formula("(TMH " + quote(proposition) + ")"),
          hypothesis(premise)));
    };
    const auto exFalso = [&](const std::string& falseProof,
                             const PreservedSexpr& proposition) {
      return termApply(falseProof, formula(proposition.render()));
    };
    const auto propExt = [&](const std::string& leftToRight,
                             const std::string& rightToLeft) {
      return proofApply(
        proofApply(
          termApply(
            termApply(
              "(known " + quote(propExtHash) + ")",
              formula(from.render())),
            formula(to.render())),
          leftToRight),
        rightToLeft);
    };

    PreservedSexpr negated;
    const bool isNot = sexprHead(from, "AP") && from.items.size() == 3
      && namedTermSexpr(from.items[1], "vNOT");
    if (isNot) negated = from.items[2];
    std::string equalityProof;
    if (isNot && isTrue(negated) && isFalse(to)) {
      const std::string sourceHyp = fresh("bool_not_true");
      const std::string targetHyp = fresh("bool_false");
      const std::string sourceToTarget = proofLambda(
        sourceHyp,
        formula(from.render()),
        proofApply(hypothesis(sourceHyp), truthProof()));
      const std::string targetToSource = proofLambda(
        targetHyp,
        formula(to.render()),
        exFalso(hypothesis(targetHyp), from));
      equalityProof = propExt(sourceToTarget, targetToSource);
    } else if (isNot && isFalse(negated) && isTrue(to)) {
      const std::string sourceHyp = fresh("bool_not_false");
      const std::string targetHyp = fresh("bool_true");
      const std::string falseHyp = fresh("bool_false");
      const std::string sourceToTarget = proofLambda(
        sourceHyp,
        formula(from.render()),
        truthProof());
      const std::string targetToSource = proofLambda(
        targetHyp,
        formula(to.render()),
        proofLambda(
          falseHyp,
          formula(negated.render()),
          hypothesis(falseHyp)));
      equalityProof = propExt(sourceToTarget, targetToSource);
    } else {
      return false;
    }

    PreservedSexpr propType;
    if (!parser.parse("(PROP)", propType)) return false;
    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      source,
      0,
      instantiate(parent(parentId), parentArguments),
      targetTerm,
      [&](std::size_t index, const std::string& proof) {
        if (index != selected) {
          return injectLiteral(target, source[index], proof);
        }
        const std::string transported = equalityTransport(
          propType,
          selectedLiteral,
          rewrittenAtom,
          position,
          true,
          equalityProof,
          proof);
        return transported.empty()
          ? std::string()
          : injectLiteral(target, rewrittenLiteral.render(), transported);
      });
    return !result.empty();
  }

  bool equalitySymmetry(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::vector<std::string>& source,
    std::size_t selected,
    const std::vector<std::string>& target,
    std::string& result)
  {
    if (selected >= source.size()) return false;

    PreservedSexprParser parser;
    PreservedSexpr literal;
    PreservedSexpr type;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!parser.parse(source[selected], literal)
        || (!sexprHead(literal, "pos") && !sexprHead(literal, "neg"))
        || literal.items.size() != 2
        || !typedEqualitySexpr(literal.items[1], type, left, right)) {
      return false;
    }
    const PreservedSexpr swapped = literalSexpr(
      sexprHead(literal, "pos"),
      equalityAtomSexpr(type, right, left));
    std::vector<std::string> expected = source;
    expected[selected] = swapped.render();
    std::vector<std::string> expectedSorted = expected;
    std::vector<std::string> targetSorted = target;
    std::sort(expectedSorted.begin(), expectedSorted.end());
    std::sort(targetSorted.begin(), targetSorted.end());
    if (expectedSorted != targetSorted) return false;

    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      source,
      0,
      instantiate(parent(parentId), parentArguments),
      targetTerm,
      [&](std::size_t index, const std::string& proof) {
        if (index != selected) {
          return injectLiteral(target, source[index], proof);
        }
        const std::string symmetric = equalitySymmetry(literal, proof);
        return symmetric.empty()
          ? std::string()
          : injectLiteral(target, swapped.render(), symmetric);
      });
    return !result.empty();
  }

  bool instantiation(
    const std::string& parentId,
    const std::vector<std::string>& parentArgumentTerms,
    std::string& result)
  {
    if (parentId.empty()) return false;
    result = instantiateTerms(parent(parentId), parentArgumentTerms);
    return !result.empty();
  }

  bool equalityFactoring(
    const std::string& parentId,
    const std::vector<std::string>& parentArgumentTerms,
    const std::vector<std::string>& source,
    std::size_t selected,
    std::size_t other,
    const std::string& selectedSharedTerm,
    const std::string& otherOtherTerm,
    const std::vector<std::string>& target,
    std::string& result)
  {
    if (selected >= source.size() || other >= source.size()
        || selected == other || target.empty()) {
      return false;
    }
    PreservedSexprParser parser;
    PreservedSexpr selectedLiteral;
    PreservedSexpr otherLiteral;
    PreservedSexpr selectedType;
    PreservedSexpr selectedLeft;
    PreservedSexpr selectedRight;
    PreservedSexpr otherType;
    PreservedSexpr otherLeft;
    PreservedSexpr otherRight;
    PreservedSexpr shared;
    PreservedSexpr otherOther;
    if (!parser.parse(source[selected], selectedLiteral)
        || !parser.parse(source[other], otherLiteral)
        || !parser.parse(selectedSharedTerm, shared)
        || !parser.parse(otherOtherTerm, otherOther)
        || !sexprHead(selectedLiteral, "pos")
        || !sexprHead(otherLiteral, "pos")
        || selectedLiteral.items.size() != 2
        || otherLiteral.items.size() != 2
        || !typedEqualitySexpr(
             selectedLiteral.items[1], selectedType,
             selectedLeft, selectedRight)
        || !typedEqualitySexpr(
             otherLiteral.items[1], otherType,
             otherLeft, otherRight)
        || !(selectedType == otherType)) {
      return false;
    }

    PreservedSexpr selectedOther;
    if (selectedLeft == shared) {
      selectedOther = selectedRight;
    } else if (selectedRight == shared) {
      selectedOther = selectedLeft;
    } else {
      return false;
    }
    PreservedSexpr otherShared;
    if (otherLeft == otherOther) {
      otherShared = otherRight;
    } else if (otherRight == otherOther) {
      otherShared = otherLeft;
    } else {
      return false;
    }
    if (!(shared == otherShared)) return false;

    const PreservedSexpr selectedOriented = literalSexpr(
      true, equalityAtomSexpr(selectedType, shared, selectedOther));
    const PreservedSexpr otherOriented = literalSexpr(
      true, equalityAtomSexpr(selectedType, shared, otherOther));
    const PreservedSexpr introducedAtom = equalityAtomSexpr(
      selectedType, selectedOther, otherOther);
    const PreservedSexpr introducedNegative = literalSexpr(
      false, introducedAtom);
    const bool hasOtherLiteral = !injectLiteralOrSymmetry(
      target, otherOriented.render(), "proof_probe").empty();
    const bool hasDirectConstraint = !injectLiteralOrSymmetry(
      target, introducedNegative.render(), "proof_probe").empty();
    if (!hasOtherLiteral) {
      return false;
    }

    PreservedSexpr abstractionConstraint;
    PreservedSexpr abstractionConstraintType;
    std::string abstractionConstraintLiteral;
    std::vector<unsigned> abstractionPosition;
    bool abstractionLeftToRight = true;
    bool hasAbstractionConstraint = false;
    if (!hasDirectConstraint) {
      const auto rewritePosition = [&] (
          const PreservedSexpr& from,
          const PreservedSexpr& to,
          std::vector<unsigned>& resultPosition) {
        std::vector<unsigned> position;
        std::function<bool(const PreservedSexpr&)> visit =
          [&](const PreservedSexpr& current) {
            if (current == from) {
              PreservedSexpr rewritten;
              PreservedSexpr selectedAtPosition;
              if (replaceSexprTermAtPosition(
                    selectedOriented.items[1],
                    position,
                    to,
                    rewritten,
                    &selectedAtPosition)
                  && selectedAtPosition == from
                  && rewritten == otherOriented.items[1]) {
                resultPosition = position;
                return true;
              }
            }
            for (unsigned childIndex = 0; childIndex != 2; ++childIndex) {
              PreservedSexpr copy = current;
              PreservedSexpr* child = sexprTermChild(copy, childIndex);
              if (child == nullptr) continue;
              position.push_back(childIndex);
              if (visit(*child)) return true;
              position.pop_back();
            }
            return false;
          };
        return visit(selectedOriented.items[1]);
      };
      for (const std::string& candidateText : target) {
        PreservedSexpr candidate;
        PreservedSexpr constraintLeft;
        PreservedSexpr constraintRight;
        if (!parser.parse(candidateText, candidate)
            || !sexprHead(candidate, "neg")
            || candidate.items.size() != 2
            || !typedEqualitySexpr(
                 candidate.items[1],
                 abstractionConstraintType,
                 constraintLeft,
                 constraintRight)) {
          continue;
        }
        if (rewritePosition(
              constraintLeft, constraintRight, abstractionPosition)) {
          abstractionLeftToRight = true;
        } else if (rewritePosition(
                     constraintRight, constraintLeft, abstractionPosition)) {
          abstractionLeftToRight = false;
        } else {
          continue;
        }
        abstractionConstraint = candidate.items[1];
        abstractionConstraintLiteral = candidateText;
        hasAbstractionConstraint = true;
        break;
      }
      if (!hasAbstractionConstraint) return false;
    }

    std::string targetFormula;
    if (!clauseFormula(target, targetFormula)) return false;
    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      source,
      0,
      instantiateTerms(parent(parentId), parentArgumentTerms),
      targetTerm,
      [&](std::size_t index, const std::string& proof) {
        if (index != selected) {
          return injectLiteralOrSymmetry(target, source[index], proof);
        }
        const std::string selectedProof = orientEqualityProof(
          selectedLiteral, selectedOriented, proof);
        if (selectedProof.empty()) return std::string();

        if (hasAbstractionConstraint) {
          const std::string positiveName = fresh("factoring_constraint");
          const std::string negativeName = fresh("factoring_not_constraint");
          const std::string transported = equalityTransport(
            abstractionConstraintType,
            selectedOriented,
            otherOriented.items[1],
            abstractionPosition,
            abstractionLeftToRight,
            hypothesis(positiveName),
            selectedProof);
          const std::string positiveProof = injectLiteralOrSymmetry(
            target, otherOriented.render(), transported);
          const std::string negativeProof = injectLiteral(
            target,
            abstractionConstraintLiteral,
            hypothesis(negativeName));
          if (positiveProof.empty() || negativeProof.empty()) {
            return std::string();
          }
          return excludedMiddle(
            abstractionConstraint.render(),
            targetFormula,
            positiveName,
            positiveProof,
            negativeName,
            negativeProof);
        }

        const std::string positiveName = fresh("factoring_positive");
        const std::string negativeName = fresh("factoring_negative");
        std::string positiveProof = equalityFactoringOtherProof(
          selectedType,
          otherOther,
          selectedProof,
          hypothesis(positiveName));
        positiveProof = injectLiteralOrSymmetry(
          target, otherOriented.render(), positiveProof);
        std::string negativeProof = injectLiteralOrSymmetry(
          target, introducedNegative.render(), hypothesis(negativeName));
        if (positiveProof.empty() || negativeProof.empty()) {
          return std::string();
        }
        return excludedMiddle(
          introducedAtom.render(),
          targetFormula,
          positiveName,
          positiveProof,
          negativeName,
          negativeProof);
      });
    return !result.empty();
  }

  bool paramodulation(
    const std::string& equalityParent,
    const std::vector<std::string>& equalityParentArguments,
    const std::vector<std::string>& equalityClause,
    std::size_t equalityIndex,
    const std::string& targetParent,
    const std::vector<std::string>& targetParentArguments,
    const std::vector<std::string>& targetClause,
    std::size_t targetIndex,
    const std::vector<unsigned>& position,
    const std::string& from,
    const std::string& to,
    const std::string& rewrittenLiteral,
    const std::vector<std::string>& target,
    bool rewriteSymmetry,
    const std::string& scopedLambdaBodyType,
    std::string& result,
    bool allowScopedChoice = false,
    MegalodonKernelSyntax::ProducerScopedLambdaChoice* scopedChoice = nullptr,
    bool* usedScopedLambda = nullptr,
    std::string* scopedParentParameter = nullptr)
  {
    if (usedScopedLambda != nullptr) *usedScopedLambda = false;
    if (scopedParentParameter != nullptr) scopedParentParameter->clear();
    const auto fail = [&](const std::string& reason) {
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << "direct Ivy paramodulation " << equalityParent
                  << " + " << targetParent << " failed: " << reason
                  << std::endl;
      }
      return false;
    };
    const auto failProof = [&](const std::string& reason) {
      fail(reason);
      return std::string();
    };
    if (equalityIndex >= equalityClause.size()
        || targetIndex >= targetClause.size()) {
      return fail("selected literal index is outside its parent clause");
    }
    PreservedSexprParser parser;
    PreservedSexpr equality;
    PreservedSexpr selectedTarget;
    PreservedSexpr fromTerm;
    PreservedSexpr toTerm;
    PreservedSexpr declaredRewritten;
    if (!parser.parse(equalityClause[equalityIndex], equality)
        || !parser.parse(targetClause[targetIndex], selectedTarget)
        || !parser.parse(from, fromTerm)
        || !parser.parse(to, toTerm)
        || !parser.parse(rewrittenLiteral, declaredRewritten)
        || !sexprHead(equality, "pos") || equality.items.size() != 2
        || (!sexprHead(selectedTarget, "pos")
            && !sexprHead(selectedTarget, "neg"))
        || selectedTarget.items.size() != 2) {
      return fail("primitive terms or selected literals do not parse");
    }

    PreservedSexpr equalityType;
    PreservedSexpr equalityLeft;
    PreservedSexpr equalityRight;
    if (!typedEqualitySexpr(
          equality.items[1], equalityType, equalityLeft, equalityRight)) {
      return fail("selected equality literal is not a typed equality");
    }
    const bool leftToRight = equalityLeft == fromTerm && equalityRight == toTerm;
    const bool rightToLeft = equalityRight == fromTerm && equalityLeft == toTerm;
    if (!leftToRight && !rightToLeft) {
      return fail("declared from/to terms do not orient the equality");
    }

    PreservedSexpr directAtom;
    PreservedSexpr selectedAtPosition;
    if (!replaceSexprTermAtPosition(
          selectedTarget.items[1], position, toTerm,
          directAtom, &selectedAtPosition)
        || !(selectedAtPosition == fromTerm)) {
      std::string selectedScopedParentParameter;
      const bool scoped = scopedLambdaParamodulation(
            equalityParent,
            equalityParentArguments,
            equalityClause,
            equalityIndex,
            targetParent,
            targetParentArguments,
            targetClause,
            targetIndex,
            position,
            equalityType,
            equalityLeft,
            equalityRight,
            fromTerm,
            toTerm,
            declaredRewritten,
            target,
            rewriteSymmetry,
            scopedLambdaBodyType,
            allowScopedChoice,
            scopedChoice,
            result,
            &selectedScopedParentParameter);
      if (scoped) {
        if (usedScopedLambda != nullptr) *usedScopedLambda = true;
        if (scopedParentParameter != nullptr) {
          *scopedParentParameter = std::move(selectedScopedParentParameter);
        }
        return true;
      }
      return fail(
        "declared target position does not contain the from term, and "
        "producer lambda lifting did not apply");
    }
    const bool targetPositive = sexprHead(selectedTarget, "pos");
    const PreservedSexpr directLiteral = literalSexpr(targetPositive, directAtom);
    if (!rewriteSymmetry) {
      if (!(directLiteral == declaredRewritten)) {
        return fail("position rewrite does not produce the declared literal");
      }
    } else {
      PreservedSexpr directType;
      PreservedSexpr directLeft;
      PreservedSexpr directRight;
      if (!typedEqualitySexpr(
            directAtom, directType, directLeft, directRight)
          || !(literalSexpr(
                 targetPositive,
                 equalityAtomSexpr(directType, directRight, directLeft))
               == declaredRewritten)) {
        return fail("symmetric position rewrite does not produce the declared literal");
      }
    }

    const std::string targetTerm = clauseTerm(target);
    result = eliminate(
      equalityClause,
      0,
      instantiate(parent(equalityParent), equalityParentArguments),
      targetTerm,
      [&](std::size_t equalityLiteralIndex,
          const std::string& equalityProof) {
        if (equalityLiteralIndex != equalityIndex) {
          const std::string injected = injectLiteral(
            target,
            equalityClause[equalityLiteralIndex],
            equalityProof);
          return injected.empty()
            ? failProof("an equality-parent remainder is absent from the result clause")
            : injected;
        }
        return eliminate(
          targetClause,
          0,
          instantiate(parent(targetParent), targetParentArguments),
          targetTerm,
          [&](std::size_t targetLiteralIndex,
              const std::string& targetProof) {
            if (targetLiteralIndex != targetIndex) {
              const std::string injected = injectLiteral(
                target,
                targetClause[targetLiteralIndex],
                targetProof);
              return injected.empty()
                ? failProof("a target-parent remainder is absent from the result clause")
                : injected;
            }
            std::string directProof = equalityTransport(
              equalityType,
              selectedTarget,
              directAtom,
              position,
              leftToRight,
              equalityProof,
              targetProof);
            if (directProof.empty()) {
              return failProof("typed equality transport could not build a proof term");
            }
            if (rewriteSymmetry) {
              directProof = equalitySymmetry(directLiteral, directProof);
            }
            if (directProof.empty()) {
              return failProof("equality symmetry could not build a proof term");
            }
            const std::string injected =
              injectLiteral(target, rewrittenLiteral, directProof);
            return injected.empty()
              ? failProof("the rewritten literal is absent from the result clause")
              : injected;
          });
      });
    return !result.empty()
      ? true
      : fail("one or more primitive proof branches failed");
  }

private:
  bool scopedLambdaParamodulation(
    const std::string& equalityParent,
    const std::vector<std::string>& equalityParentArguments,
    const std::vector<std::string>& equalityClause,
    std::size_t equalityIndex,
    const std::string& targetParent,
    const std::vector<std::string>& targetParentArguments,
    const std::vector<std::string>& targetClause,
    std::size_t targetIndex,
    const std::vector<unsigned>& position,
    const PreservedSexpr& equalityType,
    const PreservedSexpr& equalityLeft,
    const PreservedSexpr& equalityRight,
    const PreservedSexpr& from,
    const PreservedSexpr& to,
    const PreservedSexpr& declaredRewritten,
    const std::vector<std::string>& target,
    bool rewriteSymmetry,
    const std::string& scopedLambdaBodyType,
    bool allowScopedChoice,
    MegalodonKernelSyntax::ProducerScopedLambdaChoice* scopedChoice,
    std::string& result,
    std::string* scopedParentParameter)
  {
    const auto reject = [&](const std::string& reason) {
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << "direct Ivy lambda lift " << equalityParent
                  << " + " << targetParent << " rejected: " << reason
                  << std::endl;
      }
      return false;
    };
    if (targetIndex >= targetClause.size() || position.empty()) {
      return reject("empty position or target literal out of range");
    }
    PreservedSexprParser parser;
    PreservedSexpr selectedTarget;
    if (!parser.parse(targetClause[targetIndex], selectedTarget)
        || (!sexprHead(selectedTarget, "pos")
            && !sexprHead(selectedTarget, "neg"))
        || selectedTarget.items.size() != 2) {
      return reject("target literal does not parse");
    }

    // Locate the nearest enclosing lambda.  The producer supplies the body
    // type from Vampire's typed term, so the proof object never has to infer
    // application types from rendered syntax.
    PreservedSexpr atom = selectedTarget.items[1];
    PreservedSexpr* cursor = &atom;
    PreservedSexpr lambdaBefore;
    std::vector<unsigned> lambdaPosition;
    std::vector<unsigned> lambdaBodyPosition;
    bool foundLambda = false;
    for (std::size_t depth = 0; depth < position.size(); ++depth) {
      if (position[depth] == 0
          && sexprHead(*cursor, "VLAMV")
          && cursor->items.size() == 4) {
        lambdaBefore = *cursor;
        lambdaPosition.assign(position.begin(), position.begin() + depth);
        lambdaBodyPosition.assign(
          position.begin() + depth + 1, position.end());
        foundLambda = true;
      }
      cursor = sexprTermChild(*cursor, position[depth]);
      if (cursor == nullptr) return reject("position leaves the target term");
    }
    if (!foundLambda) return reject("selected redex is not below a VLAMV body");

    std::string binder;
    if (!preservedName(lambdaBefore.items[1], binder)) {
      return reject("lambda binder has no producer name");
    }
    const PreservedSexpr binderType = lambdaBefore.items[2];
    const PreservedSexpr binderTerm = quotedTmh(quote(binder));

    std::string instantiatedParameter;
    PreservedSexpr scopedFrom;
    for (const std::string& parameter : equalityParentArguments) {
      PreservedSexpr candidate = substituteNamedVariableSexpr(
        from, parameter, binderTerm);
      if (candidate == *cursor) {
        if (!instantiatedParameter.empty()) {
          return reject("more than one parent parameter matches the lambda binder");
        }
        instantiatedParameter = parameter;
        scopedFrom = std::move(candidate);
      }
    }
    if (instantiatedParameter.empty()) {
      std::ostringstream detail;
      detail << "no parent parameter maps " << from.render()
             << " to " << cursor->render() << "; arguments=";
      for (const auto& argument : equalityParentArguments) {
        detail << ' ' << argument;
      }
      return reject(detail.str());
    }
    if (scopedParentParameter != nullptr) {
      *scopedParentParameter = instantiatedParameter;
    }
    const PreservedSexpr scopedTo = substituteNamedVariableSexpr(
      to, instantiatedParameter, binderTerm);

    PreservedSexpr directAtom;
    PreservedSexpr selectedAtPosition;
    if (!replaceSexprTermAtPosition(
          selectedTarget.items[1], position, scopedTo,
          directAtom, &selectedAtPosition)
        || selectedAtPosition != scopedFrom) {
      return reject("scoped replacement does not reproduce the target rewrite");
    }
    const bool targetPositive = sexprHead(selectedTarget, "pos");
    const PreservedSexpr directLiteral = literalSexpr(
      targetPositive, directAtom);
    if (!rewriteSymmetry) {
      if (directLiteral != declaredRewritten) {
        return reject("scoped replacement disagrees with the declared result literal");
      }
    } else {
      PreservedSexpr directType;
      PreservedSexpr directLeft;
      PreservedSexpr directRight;
      if (!typedEqualitySexpr(
            directAtom, directType, directLeft, directRight)
          || literalSexpr(
               targetPositive,
               equalityAtomSexpr(directType, directRight, directLeft))
             != declaredRewritten) {
        return reject("scoped replacement symmetry disagrees with the declared result literal");
      }
    }

    PreservedSexpr lambdaAfter;
    PreservedSexpr ignored;
    PreservedSexpr expectedLambdaBodyAfter;
    if (!replaceSexprTermAtPosition(
          lambdaBefore.items[3], lambdaBodyPosition, scopedTo,
          expectedLambdaBodyAfter, &ignored)
        || ignored != scopedFrom) {
      return reject("lambda-body context does not select the scoped redex");
    }
    if (!replaceSexprTermAtPosition(
          directAtom, lambdaPosition, lambdaBefore,
          ignored, &lambdaAfter)
        || !sexprHead(lambdaAfter, "VLAMV")
        || lambdaAfter.items.size() != 4
        || lambdaAfter.items[1] != lambdaBefore.items[1]
        || lambdaAfter.items[2] != binderType
        || lambdaAfter.items[3] != expectedLambdaBodyAfter) {
      return reject("rewritten lambda boundary is not structurally stable");
    }

    PreservedSexpr lambdaBodyType = equalityType;
    if (!scopedLambdaBodyType.empty()
        && !parser.parse(scopedLambdaBodyType, lambdaBodyType)) {
      return reject("producer lambda-body type does not parse");
    }
    if (lambdaBodyPosition.empty() && lambdaBodyType != equalityType) {
      return reject("complete lambda-body rewrite changes the body type");
    }
    if (!lambdaBodyPosition.empty() && scopedLambdaBodyType.empty()) {
      return reject("nested lambda-body rewrite lacks a producer body type");
    }

    std::vector<PreservedSexpr> instantiatedClauseSexpr;
    std::vector<std::string> instantiatedClause;
    instantiatedClauseSexpr.reserve(equalityClause.size());
    instantiatedClause.reserve(equalityClause.size());
    for (const std::string& literalText : equalityClause) {
      PreservedSexpr literal;
      if (!parser.parse(literalText, literal)) {
        return reject("equality-parent clause does not parse");
      }
      literal = substituteNamedVariableSexpr(
        literal, instantiatedParameter, binderTerm);
      instantiatedClause.push_back(literal.render());
      instantiatedClauseSexpr.push_back(std::move(literal));
    }
    if (equalityIndex >= instantiatedClauseSexpr.size()) {
      return reject("equality literal is out of range after instantiation");
    }
    PreservedSexpr instantiatedEqualityType;
    PreservedSexpr instantiatedLeft;
    PreservedSexpr instantiatedRight;
    if (!sexprHead(instantiatedClauseSexpr[equalityIndex], "pos")
        || instantiatedClauseSexpr[equalityIndex].items.size() != 2
        || !typedEqualitySexpr(
             instantiatedClauseSexpr[equalityIndex].items[1],
             instantiatedEqualityType,
             instantiatedLeft,
             instantiatedRight)
        || instantiatedEqualityType != equalityType) {
      return reject("instantiated selected literal is not the declared typed equality");
    }
    const bool scopedLeftToRight =
      instantiatedLeft == scopedFrom && instantiatedRight == scopedTo;
    const bool scopedRightToLeft =
      instantiatedRight == scopedFrom && instantiatedLeft == scopedTo;
    if (!scopedLeftToRight && !scopedRightToLeft) {
      return reject("instantiated equality does not orient the scoped rewrite");
    }

    std::vector<std::string> remainder;
    std::vector<std::string> remainderAtBinder;
    std::vector<std::size_t> remainderSourceIndices;
    bool dependentRemainder = false;
    for (std::size_t index = 0; index < equalityClause.size(); ++index) {
      if (index == equalityIndex) continue;
      remainder.push_back(equalityClause[index]);
      remainderAtBinder.push_back(instantiatedClause[index]);
      dependentRemainder = dependentRemainder
        || instantiatedClause[index] != equalityClause[index];
      remainderSourceIndices.push_back(index);
    }

    std::vector<std::string> effectiveTarget = target;
    PreservedSexpr choiceWitness;
    std::string choicePredicate;
    std::string choicePredicateBody;
    std::string choiceKnown;
    if (dependentRemainder) {
      if (!allowScopedChoice || scopedChoice == nullptr || remainder.empty()) {
        return reject("equality-parent remainder depends on the consumed open slot");
      }
      std::string predicateBody;
      if (!clauseFormula(remainderAtBinder, predicateBody)) {
        return reject("dependent remainder does not form a choice predicate");
      }
      choicePredicateBody = predicateBody;
      const std::string binderTypeText = binderType.render();
      std::string epsilon;
      if (binderTypeText == "(SET)") {
        epsilon = "Eps_i";
        choiceKnown = "vampire_exists_set_choice";
      } else if (binderTypeText == "(PROP)") {
        epsilon = "Eps_prop";
        choiceKnown = "vampire_exists_prop_choice";
      } else if (binderTypeText == "(AR (SET) (PROP))") {
        epsilon = "Eps_set_prop";
        choiceKnown = "vampire_exists_set_prop_choice";
      } else if (binderTypeText == "(AR (SET) (SET))") {
        epsilon = "Eps_set_set";
        choiceKnown = "vampire_exists_set_set_choice";
      } else if (binderTypeText
                 == "(AR (SET) (AR (SET) (PROP)))") {
        epsilon = "Eps_set_set_prop";
        choiceKnown = "vampire_exists_set_set_prop_choice";
      } else {
        return reject("dependent remainder has no typed choice operator");
      }
      choicePredicate = "(LAMV " + quote(binder) + " "
        + binderTypeText + " " + predicateBody + ")";
      if (!parser.parse(
            "(AP (TMH " + quote(epsilon) + ") "
              + choicePredicate + ")",
            choiceWitness)) {
        return reject("dependent remainder witness does not parse");
      }
      remainder.clear();
      for (std::size_t index = 0; index < equalityClause.size(); ++index) {
        if (index == equalityIndex) continue;
        PreservedSexpr literal;
        if (!parser.parse(equalityClause[index], literal)) return false;
        remainder.push_back(substituteNamedVariableSexpr(
          literal, instantiatedParameter, choiceWitness).render());
      }
      for (std::string& literalText : effectiveTarget) {
        PreservedSexpr literal;
        if (!parser.parse(literalText, literal)) {
          return reject("choice-normalized target literal does not parse");
        }
        literalText = substituteNamedVariableSexpr(
          literal, instantiatedParameter, choiceWitness).render();
      }
      scopedChoice->parameter = instantiatedParameter;
      scopedChoice->parameterType = binderTypeText;
      scopedChoice->witnessTerm = choiceWitness.render();
      scopedChoice->resultLiterals = effectiveTarget;
      scopedChoice->resultClause = clauseValue(effectiveTarget);
    }

    std::string liftedTypeText = "(AR " + binderType.render()
      + " " + lambdaBodyType.render() + ")";
    PreservedSexpr liftedType;
    if (!parser.parse(liftedTypeText, liftedType)) {
      return reject("lifted function type does not parse");
    }
    const PreservedSexpr bodyBefore = lambdaBefore.items[3];
    const PreservedSexpr bodyAfter = lambdaAfter.items[3];
    const PreservedSexpr pointwiseAtom = equalityAtomSexpr(
      lambdaBodyType, bodyBefore, bodyAfter);
    const std::string pointwiseFormula = formula(pointwiseAtom.render());
    std::vector<unsigned> bodyCongruencePosition{1};
    bodyCongruencePosition.insert(
      bodyCongruencePosition.end(),
      lambdaBodyPosition.begin(), lambdaBodyPosition.end());

    std::vector<std::string> scopedParentArguments =
      equalityParentArguments;
    for (std::string& argument : scopedParentArguments) {
      if (argument == instantiatedParameter) argument = binder;
    }
    const auto liftedEqualityProof =
      [&](const std::string& notRemainderName) {
        const std::string pointwise = eliminate(
          instantiatedClause,
          0,
          instantiate(parent(equalityParent), scopedParentArguments),
          pointwiseFormula,
          [&](std::size_t sourceIndex, const std::string& sourceProof) {
            if (sourceIndex == equalityIndex) {
              std::string redexEquality = scopedLeftToRight
                ? sourceProof
                : positiveEqualitySymmetry(
                    equalityType,
                    instantiatedLeft,
                    instantiatedRight,
                    sourceProof);
              if (redexEquality.empty() || lambdaBodyPosition.empty()) {
                return redexEquality;
              }
              const PreservedSexpr reflexiveAtom = equalityAtomSexpr(
                lambdaBodyType, bodyBefore, bodyBefore);
              const PreservedSexpr reflexiveLiteral = literalSexpr(
                true, reflexiveAtom);
              return equalityTransport(
                equalityType,
                reflexiveLiteral,
                pointwiseAtom,
                bodyCongruencePosition,
                true,
                redexEquality,
                positiveEqualityReflexivity(lambdaBodyType, bodyBefore));
            }
            auto found = std::find(
              remainderSourceIndices.begin(),
              remainderSourceIndices.end(),
              sourceIndex);
            if (found == remainderSourceIndices.end()
                || notRemainderName.empty()) {
              return std::string();
            }
            const std::size_t remainderIndex =
              static_cast<std::size_t>(
                found - remainderSourceIndices.begin());
            std::string remainderProof;
            if (dependentRemainder) {
              const std::string binderRemainder = inject(
                remainderAtBinder, remainderIndex, sourceProof);
              if (binderRemainder.empty()) return std::string();
              const std::string existsResult = fresh("lambda_exists_result");
              const std::string existsHandler = fresh("lambda_exists_handler");
              const std::string existsResultTerm =
                "(TMH " + quote(existsResult) + ")";
              const std::string existsProof = termLambda(
                existsResult,
                "(PROP)",
                proofLambda(
                  existsHandler,
                  formula(
                    "(ALLV " + quote(binder) + " "
                    + binderType.render() + " (IMP "
                    + choicePredicateBody + " "
                    + existsResultTerm + "))"),
                  proofApply(
                    termApply(
                      hypothesis(existsHandler),
                      "(term " + binderTerm.render() + ")"),
                    binderRemainder)));
              remainderProof = proofApply(
                termApply(
                  "(known " + quote(choiceKnown) + ")",
                  formula(choicePredicate)),
                existsProof);
            } else {
              remainderProof = inject(
                remainder, remainderIndex, sourceProof);
            }
            if (remainderProof.empty()) return std::string();
            const std::string contradiction = proofApply(
              hypothesis(notRemainderName), remainderProof);
            return termApply(contradiction, pointwiseFormula);
          });
        if (pointwise.empty()) return std::string();
        static const char* funcExtHash =
          "5626ac8cb7c90418f6c980ffedd6f45097048659977d8690c44f9d34feb6b2d3";
        std::string extensionality = typeApply(
          typeApply(
            "(known " + quote(funcExtHash) + ")",
            binderType.render()),
          lambdaBodyType.render());
        extensionality = termApply(
          extensionality, "(term " + lambdaBefore.render() + ")");
        extensionality = termApply(
          extensionality, "(term " + lambdaAfter.render() + ")");
        return proofApply(
          extensionality,
          termLambda(
            binder, binderType.render(), pointwise));
      };

    const std::string targetTerm = clauseTerm(effectiveTarget);
    const auto transportTarget = [&](const std::string& liftedProof) {
      if (liftedProof.empty()) return std::string();
      return eliminate(
        targetClause,
        0,
        instantiate(parent(targetParent), targetParentArguments),
        targetTerm,
        [&](std::size_t sourceIndex, const std::string& sourceProof) {
          if (sourceIndex != targetIndex) {
            return injectLiteral(
              effectiveTarget, targetClause[sourceIndex], sourceProof);
          }
          std::string transported = equalityTransport(
            liftedType,
            selectedTarget,
            directAtom,
            lambdaPosition,
            true,
            liftedProof,
            sourceProof);
          if (transported.empty()) return std::string();
          if (rewriteSymmetry) {
            transported = equalitySymmetry(directLiteral, transported);
          }
          return transported.empty()
            ? std::string()
            : injectLiteral(
                effectiveTarget, declaredRewritten.render(), transported);
        });
    };

    if (remainder.empty()) {
      result = transportTarget(liftedEqualityProof(std::string()));
      return !result.empty();
    }
    std::string remainderFormula;
    std::string targetFormula;
    if (!clauseFormula(remainder, remainderFormula)
        || !clauseFormula(effectiveTarget, targetFormula)) {
      return reject("lifted clause formula does not parse");
    }
    const std::string remainderName = fresh("lambda_remainder");
    const std::string notRemainderName = fresh("lambda_not_remainder");
    const std::string positiveProof = eliminate(
      remainder,
      0,
      hypothesis(remainderName),
      targetTerm,
      [&](std::size_t index, const std::string& proof) {
        return injectLiteral(effectiveTarget, remainder[index], proof);
      });
    const std::string negativeProof = transportTarget(
      liftedEqualityProof(notRemainderName));
    if (positiveProof.empty() || negativeProof.empty()) return false;
    result = excludedMiddle(
      remainderFormula,
      targetFormula,
      remainderName,
      positiveProof,
      notRemainderName,
      negativeProof);
    if (!result.empty() && dependentRemainder && scopedChoice != nullptr) {
      scopedChoice->producerProof = result;
    }
    return !result.empty();
  }

  std::size_t _fresh = 0;
  std::string _freshPrefix = "ivy_sat_";
  std::set<std::string> _reservedNames;

  static std::string quote(const std::string& value)
  {
    std::string rendered = "\"";
    for (char ch : value) {
      if (ch == '\\' || ch == '"') rendered += '\\';
      rendered += ch;
    }
    return rendered + '"';
  }

  static std::string complement(const std::string& literal)
  {
    if (literal.compare(0, 5, "(pos ") == 0) {
      return "(neg " + literal.substr(5);
    }
    if (literal.compare(0, 5, "(neg ") == 0) {
      return "(pos " + literal.substr(5);
    }
    return std::string();
  }

  static bool literalFormula(const std::string& literal, std::string& formula)
  {
    if (literal.size() < 7 || literal.back() != ')') return false;
    const bool positive = literal.compare(0, 5, "(pos ") == 0;
    const bool negative = literal.compare(0, 5, "(neg ") == 0;
    if (!positive && !negative) return false;
    const std::string atom = literal.substr(5, literal.size() - 6);
    formula = positive
      ? atom
      : "(IMP " + atom + " (TMH \"vampire_false\"))";
    return true;
  }

  static std::string formula(const std::string& value)
  {
    return "(formula " + value + ")";
  }

  static std::string literalTerm(const std::string& value)
  {
    return "(literal " + value + ")";
  }

  static std::string clauseTerm(const std::vector<std::string>& literals)
  {
    return "(clause " + clauseValue(literals) + ")";
  }

  static std::string clauseValue(const std::vector<std::string>& literals)
  {
    std::string value = "(clause";
    for (const std::string& literal : literals) value += " " + literal;
    return value + ")";
  }

  static std::string formulaImp(
    const std::string& left,
    const std::string& right)
  {
    return "(IMP " + left + " " + right + ")";
  }

  static std::string termApply(
    const std::string& proof,
    const std::string& term)
  {
    return "(term_apply " + proof + " " + term + ")";
  }

  static std::string typeApply(
    const std::string& proof,
    const std::string& type)
  {
    return "(type_apply " + proof + " " + type + ")";
  }

  static std::string instantiate(
    std::string proof,
    const std::vector<std::string>& arguments)
  {
    for (const std::string& argument : arguments) {
      proof = termApply(
        proof, "(term (TMH " + quote(argument) + "))");
    }
    return proof;
  }

  static std::string instantiateTerms(
    std::string proof,
    const std::vector<std::string>& arguments)
  {
    for (const std::string& argument : arguments) {
      proof = termApply(proof, "(term " + argument + ")");
    }
    return proof;
  }

  static std::string proofApply(
    const std::string& left,
    const std::string& right)
  {
    return "(proof_apply " + left + " " + right + ")";
  }

  std::string hypothesis(const std::string& name) const
  {
    return "(hyp " + quote(name) + ")";
  }

  std::string proofLambda(
    const std::string& name,
    const std::string& proposition,
    const std::string& body) const
  {
    return "(proof_lambda " + quote(name) + " " + proposition
      + " " + body + ")";
  }

  std::string termLambda(
    const std::string& name,
    const std::string& type,
    const std::string& body) const
  {
    return "(term_lambda " + quote(name) + " " + type
      + " " + body + ")";
  }

  std::string fresh(const char* stem)
  {
    std::string result;
    do {
      result = _freshPrefix + stem + std::to_string(_fresh++);
    } while (_reservedNames.find(result) != _reservedNames.end());
    _reservedNames.insert(result);
    return result;
  }

  std::string expandedEqualityProposition(
    const PreservedSexpr& type,
    const PreservedSexpr& left,
    const PreservedSexpr& right)
  {
    const std::string relationName = fresh("factoring_relation");
    const std::string relation = "(TMH " + quote(relationName) + ")";
    return
      "(ALLV " + quote(relationName)
      + " (AR " + type.render() + " (AR " + type.render() + " (PROP)))"
      + " (IMP (AP (AP " + relation + " " + left.render() + ") "
      + right.render() + ")"
      + " (AP (AP " + relation + " " + right.render() + ") "
      + left.render() + ")))";
  }

  std::string orientEqualityProof(
    const PreservedSexpr& sourceLiteral,
    const PreservedSexpr& targetLiteral,
    const std::string& proof)
  {
    if (sourceLiteral == targetLiteral) return proof;
    if ((!sexprHead(sourceLiteral, "pos")
         && !sexprHead(sourceLiteral, "neg"))
        || sourceLiteral.items.size() != 2) {
      return std::string();
    }
    PreservedSexpr type;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!typedEqualitySexpr(sourceLiteral.items[1], type, left, right)
        || !(literalSexpr(
               sexprHead(sourceLiteral, "pos"),
               equalityAtomSexpr(type, right, left)) == targetLiteral)) {
      return std::string();
    }
    return equalitySymmetry(sourceLiteral, proof);
  }

  std::string injectLiteralOrSymmetry(
    const std::vector<std::string>& target,
    const std::string& sourceLiteral,
    const std::string& proof)
  {
    const std::string direct = injectLiteral(target, sourceLiteral, proof);
    if (!direct.empty()) return direct;
    PreservedSexprParser parser;
    PreservedSexpr source;
    PreservedSexpr type;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!parser.parse(sourceLiteral, source)
        || (!sexprHead(source, "pos") && !sexprHead(source, "neg"))
        || source.items.size() != 2
        || !typedEqualitySexpr(source.items[1], type, left, right)) {
      return std::string();
    }
    const PreservedSexpr swapped = literalSexpr(
      sexprHead(source, "pos"), equalityAtomSexpr(type, right, left));
    const std::string swappedProof = equalitySymmetry(source, proof);
    return swappedProof.empty()
      ? std::string()
      : injectLiteral(target, swapped.render(), swappedProof);
  }

  std::string equalityFactoringOtherProof(
    const PreservedSexpr& type,
    const PreservedSexpr& otherOther,
    const std::string& selectedProof,
    const std::string& introducedProof)
  {
    const std::string leftName = fresh("factoring_left");
    const std::string rightName = fresh("factoring_right");
    const PreservedSexpr right = quotedTmh(quote(rightName));
    const std::string motive =
      "(term (LAMV " + quote(leftName) + " " + type.render()
      + " (LAMV " + quote(rightName) + " " + type.render() + " "
      + expandedEqualityProposition(type, right, otherOther) + ")))";
    return proofApply(termApply(selectedProof, motive), introducedProof);
  }

  std::string excludedMiddle(
    const std::string& proposition,
    const std::string& target,
    const std::string& positiveName,
    const std::string& positiveProof,
    const std::string& negativeName,
    const std::string& negativeProof)
  {
    static const char* dnegHash =
      "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0";
    const std::string qName = fresh("xm_q");
    const std::string leftName = fresh("xm_left");
    const std::string rightName = fresh("xm_right");
    const std::string notQName = fresh("xm_not_q");
    const std::string propositionName = fresh("xm_prop");
    const std::string q = "(TMH " + quote(qName) + ")";
    const std::string falseFormula = "(TMH \"vampire_false\")";
    const std::string leftResult = proofApply(
      hypothesis(leftName), hypothesis(propositionName));
    const std::string notProposition = proofLambda(
      propositionName,
      formula(proposition),
      proofApply(hypothesis(notQName), leftResult));
    const std::string rightResult = proofApply(
      hypothesis(rightName), notProposition);
    const std::string contradiction = proofApply(
      hypothesis(notQName), rightResult);
    const std::string dneg = proofApply(
      termApply("(known " + quote(dnegHash) + ")", formula(q)),
      proofLambda(
        notQName,
        formula(formulaImp(q, falseFormula)),
        contradiction));
    const std::string xm = termLambda(
      qName,
      "(PROP)",
      proofLambda(
        leftName,
        formula(formulaImp(proposition, q)),
        proofLambda(
          rightName,
          formula(formulaImp(
            formulaImp(proposition, falseFormula), q)),
          dneg)));
    return proofApply(
      proofApply(
        termApply(xm, formula(target)),
        proofLambda(positiveName, formula(proposition), positiveProof)),
      proofLambda(
        negativeName,
        formula(formulaImp(proposition, falseFormula)),
        negativeProof));
  }

  std::string equalityTransport(
    const PreservedSexpr& equalityType,
    const PreservedSexpr& selectedTarget,
    const PreservedSexpr& directAtom,
    const std::vector<unsigned>& position,
    bool leftToRight,
    const std::string& equalityProof,
    const std::string& targetProof)
  {
    const bool positive = sexprHead(selectedTarget, "pos");
    const std::string leftName = fresh("eq_left");
    const std::string rightName = fresh("eq_right");
    const std::string replacementName = positive
      ? (leftToRight ? leftName : rightName)
      : (leftToRight ? rightName : leftName);
    PreservedSexpr contextAtom;
    if (!replaceSexprTermAtPosition(
          selectedTarget.items[1],
          position,
          quotedTmh(quote(replacementName)),
          contextAtom)) {
      return std::string();
    }
    std::string contextFormula = contextAtom.render();
    PreservedSexpr contextType;
    PreservedSexpr contextLeft;
    PreservedSexpr contextRight;
    if (typedEqualitySexpr(
          contextAtom, contextType, contextLeft, contextRight)) {
      const std::string relationName = fresh("eq_relation");
      const std::string relation = "(TMH " + quote(relationName) + ")";
      contextFormula =
        "(ALLV " + quote(relationName)
        + " (AR " + contextType.render()
        + " (AR " + contextType.render() + " (PROP)))"
        + " (IMP (AP (AP " + relation + " " + contextLeft.render()
        + ") " + contextRight.render() + ")"
        + " (AP (AP " + relation + " " + contextRight.render()
        + ") " + contextLeft.render() + ")))";
    }
    const std::string motive =
      "(term (LAMV " + quote(leftName) + " " + equalityType.render()
      + " (LAMV " + quote(rightName) + " " + equalityType.render()
      + " " + contextFormula + ")))";
    if (positive) {
      return proofApply(termApply(equalityProof, motive), targetProof);
    }
    const std::string directName = fresh("direct");
    const std::string transported = proofApply(
      termApply(equalityProof, motive),
      hypothesis(directName));
    return proofLambda(
      directName,
      formula(directAtom.render()),
      proofApply(targetProof, transported));
  }

  std::string positiveEqualityReflexivity(
    const PreservedSexpr& type,
    const PreservedSexpr& value)
  {
    const std::string relationName = fresh("refl_relation");
    const std::string premiseName = fresh("refl_premise");
    const std::string relation = "(TMH " + quote(relationName) + ")";
    const std::string premise =
      "(AP (AP " + relation + " " + value.render() + ") "
      + value.render() + ")";
    return termLambda(
      relationName,
      "(AR " + type.render() + " (AR " + type.render() + " (PROP)))",
      proofLambda(
        premiseName,
        formula(premise),
        hypothesis(premiseName)));
  }

  std::string positiveEqualitySymmetry(
    const PreservedSexpr& type,
    const PreservedSexpr& left,
    const PreservedSexpr& right,
    const std::string& proof)
  {
    const std::string predicateName = fresh("eq_predicate");
    const std::string leftName = fresh("sym_left");
    const std::string rightName = fresh("sym_right");
    const std::string premiseName = fresh("sym_premise");
    const std::string predicate = "(TMH " + quote(predicateName) + ")";
    const std::string premise =
      "(AP (AP " + predicate + " " + right.render() + ") "
      + left.render() + ")";
    const std::string motive =
      "(term (LAMV " + quote(leftName) + " " + type.render()
      + " (LAMV " + quote(rightName) + " " + type.render()
      + " (AP (AP " + predicate + " (TMH " + quote(rightName)
      + ")) (TMH " + quote(leftName) + ")))))";
    return termLambda(
      predicateName,
      "(AR " + type.render() + " (AR " + type.render() + " (PROP)))",
      proofLambda(
        premiseName,
        formula(premise),
        proofApply(
          termApply(proof, motive),
          hypothesis(premiseName))));
  }

  std::string equalitySymmetry(
    const PreservedSexpr& literal,
    const std::string& proof)
  {
    if ((!sexprHead(literal, "pos") && !sexprHead(literal, "neg"))
        || literal.items.size() != 2) {
      return std::string();
    }
    PreservedSexpr type;
    PreservedSexpr left;
    PreservedSexpr right;
    if (!typedEqualitySexpr(literal.items[1], type, left, right)) {
      return std::string();
    }
    if (sexprHead(literal, "pos")) {
      return positiveEqualitySymmetry(type, left, right, proof);
    }
    const std::string swappedName = fresh("swapped");
    const PreservedSexpr swappedAtom = equalityAtomSexpr(type, right, left);
    const std::string sourceEquality = positiveEqualitySymmetry(
      type, right, left, hypothesis(swappedName));
    return proofLambda(
      swappedName,
      formula(swappedAtom.render()),
      proofApply(proof, sourceEquality));
  }

  bool clauseFormula(
    const std::vector<std::string>& literals,
    std::string& result) const
  {
    if (literals.empty()) {
      result = "(TMH \"vampire_false\")";
      return true;
    }
    std::vector<std::string> formulas(literals.size());
    for (std::size_t index = 0; index < literals.size(); ++index) {
      if (!literalFormula(literals[index], formulas[index])) return false;
    }
    result = formulas.back();
    for (std::size_t index = formulas.size() - 1; index > 0; --index) {
      result = "(AP (AP (TMH \"vampire_or\") "
        + formulas[index - 1] + ") " + result + ")";
    }
    return true;
  }

  std::string inject(
    const std::vector<std::string>& target,
    std::size_t targetIndex,
    const std::string& proof)
  {
    if (target.empty() || targetIndex >= target.size()) return std::string();
    if (target.size() == 1) return targetIndex == 0 ? proof : std::string();
    std::string leftFormula;
    std::string rightFormula;
    const std::vector<std::string> rest(target.begin() + 1, target.end());
    if (!literalFormula(target.front(), leftFormula)
        || !clauseFormula(rest, rightFormula)) {
      return std::string();
    }
    const std::string qName = fresh("q");
    const std::string leftName = fresh("left");
    const std::string rightName = fresh("right");
    const std::string q = "(TMH " + quote(qName) + ")";
    const std::string selected = targetIndex == 0
      ? proofApply(hypothesis(leftName), proof)
      : proofApply(
          hypothesis(rightName),
          inject(rest, targetIndex - 1, proof));
    return termLambda(
      qName,
      "(PROP)",
      proofLambda(
        leftName,
        formula(formulaImp(leftFormula, q)),
        proofLambda(
          rightName,
          formula(formulaImp(rightFormula, q)),
          selected)));
  }

  std::string injectLiteral(
    const std::vector<std::string>& target,
    const std::string& literal,
    const std::string& proof)
  {
    const auto found = std::find(target.begin(), target.end(), literal);
    return found == target.end()
      ? std::string()
      : inject(
          target,
          static_cast<std::size_t>(found - target.begin()),
          proof);
  }

  template<class Branch>
  std::string eliminate(
    const std::vector<std::string>& source,
    std::size_t offset,
    const std::string& proof,
    const std::string& target,
    const Branch& branch)
  {
    if (source.empty()) return std::string();
    if (source.size() == 1) return branch(offset, proof);
    const std::string leftName = fresh("source");
    const std::string restName = fresh("rest");
    const std::vector<std::string> rest(source.begin() + 1, source.end());
    const std::string leftBody = branch(offset, hypothesis(leftName));
    const std::string rightBody = eliminate(
      rest,
      offset + 1,
      hypothesis(restName),
      target,
      branch);
    if (leftBody.empty() || rightBody.empty()) return std::string();
    return proofApply(
      proofApply(
        termApply(proof, target),
        proofLambda(leftName, literalTerm(source.front()), leftBody)),
      proofLambda(restName, clauseTerm(rest), rightBody));
  }
};

}

bool buildPredicateDefinitionReplacement(
  const std::string& symbol,
  const std::vector<MegalodonKernelSyntax::RenderedKernelPredicateDefinitionBinder>& binders,
  const std::string& definiendumFormula,
  const std::string& bodyFormula,
  std::string& replacement,
  std::string& error)
{
  PreservedSexprParser parser;
  PreservedSexpr definiendum;
  PreservedSexpr body;
  if (!parser.parse(definiendumFormula, definiendum)
      || !parser.parse(bodyFormula, body)) {
    error = "producer could not parse its rendered definition endpoints";
    return false;
  }

  std::vector<PreservedSexpr> arguments;
  std::size_t matches = 0;
  std::function<void(const PreservedSexpr&)> findApplication;
  findApplication = [&](const PreservedSexpr& current) {
    const PreservedSexpr* head = &current;
    std::vector<PreservedSexpr> currentArguments;
    while (sexprHead(*head, "AP") && head->items.size() == 3) {
      currentArguments.push_back(head->items[2]);
      head = &head->items[1];
    }
    if (namedTermSexpr(*head, symbol)) {
      std::reverse(currentArguments.begin(), currentArguments.end());
      arguments = std::move(currentArguments);
      ++matches;
      return;
    }
    if (!current.atom) {
      for (std::size_t index = 1; index < current.items.size(); ++index) {
        findApplication(current.items[index]);
      }
    }
  };
  findApplication(definiendum);
  if (matches != 1) {
    error = "definiendum does not contain exactly one complete application of " + symbol;
    return false;
  }
  if (arguments.size() != binders.size()) {
    error = "definiendum arity does not match its universal binders";
    return false;
  }

  std::vector<const MegalodonKernelSyntax::RenderedKernelPredicateDefinitionBinder*>
    orderedBinders;
  std::set<std::string> used;
  for (const PreservedSexpr& argument : arguments) {
    const auto binder = std::find_if(
      binders.begin(), binders.end(),
      [&](const auto& candidate) {
        return namedTermSexpr(argument, candidate.variable);
      });
    if (binder == binders.end() || !used.insert(binder->variable).second) {
      error = "definiendum arguments are not a permutation of its universal binders";
      return false;
    }
    orderedBinders.push_back(&*binder);
  }

  replacement = body.render();
  for (auto binder = orderedBinders.rbegin(); binder != orderedBinders.rend(); ++binder) {
    replacement =
      "(LAMV " + quotePreservedName((*binder)->variable) + " "
      + (*binder)->type.sexpr + " " + replacement + ")";
  }
  PreservedSexpr parsedReplacement;
  if (!parser.parse(replacement, parsedReplacement)) {
    error = "producer generated an invalid predicate replacement term";
    return false;
  }
  replacement = parsedReplacement.render();
  return true;
}

bool expandPredicateDefinitionFoldProof(
  const std::string& parentId,
  const std::string& sourceFormula,
  const std::string& targetFormula,
  const std::vector<std::pair<std::string, std::string>>& definitions,
  std::string& result,
  std::string& error)
{
  const bool certificateDebug = std::getenv("MEGALODON_CERT_DEBUG") != nullptr;
  const auto debugPhase = [&](const char* phase) {
    if (certificateDebug) {
      std::cerr << "megalodon predicate fold expander: "
                << phase << std::endl;
    }
  };
  debugPhase("parse endpoints");
  PreservedSexprParser parser;
  PreservedSexpr source;
  PreservedSexpr target;
  if (parentId.empty()
      || !parser.parse(sourceFormula, source)
      || !parser.parse(targetFormula, target)
      || definitions.empty()) {
    error = "predicate fold has incomplete producer endpoints or definitions";
    return false;
  }

  std::map<std::string, PreservedSexpr> replacements;
  debugPhase("parse definitions");
  for (const auto& definition : definitions) {
    PreservedSexpr replacement;
    if (definition.first.empty()
        || !parser.parse(definition.second, replacement)
        || !replacements.emplace(definition.first, std::move(replacement)).second) {
      error = "predicate fold has an invalid or duplicate producer definition";
      return false;
    }
  }

  bool valid = true;
  std::set<std::string> expanding;
  std::function<PreservedSexpr(const PreservedSexpr&)> unfold;
  unfold = [&](const PreservedSexpr& current) -> PreservedSexpr {
    const PreservedSexpr* head = &current;
    std::vector<PreservedSexpr> arguments;
    while (sexprHead(*head, "AP") && head->items.size() == 3) {
      arguments.push_back(head->items[2]);
      head = &head->items[1];
    }
    std::reverse(arguments.begin(), arguments.end());
    const auto definition = std::find_if(
      replacements.begin(), replacements.end(),
      [&](const auto& candidate) {
        return namedTermSexpr(*head, candidate.first);
      });
    if (definition != replacements.end()) {
      if (!expanding.insert(definition->first).second) {
        valid = false;
        return current;
      }
      PreservedSexpr expanded = definition->second;
      for (const PreservedSexpr& argument : arguments) {
        expanded = preservedList(
          preservedAtom("AP"), std::move(expanded), unfold(argument));
      }
      expanded = betaNormalizeSexpr(expanded);
      expanded = unfold(expanded);
      expanding.erase(definition->first);
      return expanded;
    }
    if (current.atom) return current;
    PreservedSexpr rewritten = current;
    for (std::size_t index = 1; index < rewritten.items.size(); ++index) {
      rewritten.items[index] = unfold(rewritten.items[index]);
    }
    return rewritten;
  };

  debugPhase("unfold target");
  target = unfold(target);
  if (!valid) {
    error = "predicate fold producer definitions are cyclic";
    return false;
  }
  MegalodonKernelSyntax::RenderedKernelFoolProgram program;
  debugPhase("build atomic program");
  if (!buildFoolFormulaProgram(
        source.render(), target.render(), program, error, true)) {
    error = "predicate fold does not lower to atomic FOOL transport: " + error;
    return false;
  }
  debugPhase("expand atomic proof");
  if (!expandFoolFormulaProof(parentId, {}, program, result, error)) {
    error = "predicate fold atomic FOOL proof failed: " + error;
    return false;
  }
  debugPhase("complete");
  return true;
}

bool expandAvatarSatProjectionProof(
  const std::string& parentId,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  return expandClauseProjectionProof(
    parentId, {}, sourceLiterals, resultLiterals, result, error);
}

bool expandClauseProjectionProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (parentId.empty()
      || !builder.projection(
           parentId, parentArguments,
           sourceLiterals, resultLiterals, result)) {
    error = "AVATAR SAT projection is not a producer-explicit clause projection";
    return false;
  }
  return true;
}

bool expandClauseInequalitySplitProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<InequalitySplitProofItem>& splits,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (parentId.empty()
      || !builder.inequalitySplit(
           parentId, parentArguments, sourceLiterals,
           splits, resultLiterals, result)) {
    error = "inequality splitting does not lower to the producer local-name definition";
    return false;
  }
  return true;
}

bool expandInequalityNameIntroProof(
  const std::string& resultLiteral,
  const std::string& namedProposition,
  const std::string& splitTerm,
  const std::string& splitType,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (!builder.inequalityNameIntro(
        resultLiteral, namedProposition, splitTerm, splitType, result)) {
    error = "inequality name introduction does not lower to its producer definition";
    return false;
  }
  return true;
}

bool expandCnfFormulaClauseProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::string& sourceFormula,
  const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (!builder.cnfFormulaClause(
        parentId,
        parentArguments,
        sourceFormula,
        projection,
        resultLiterals,
        result)) {
    error = "CNF projection does not match the producer source and result";
    return false;
  }
  return true;
}

bool expandFoolFormulaProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (!builder.foolFormula(
        parentId, parentArguments, program, result)) {
    error = "FOOL program does not lower to an explicit Ivy proof";
    return false;
  }
  return true;
}

bool expandPositiveExistsContext(
  const PositiveExistsContextRequest& request,
  PositiveExistsContextExpansion& result,
  std::string& error)
{
  PreservedSexprParser parser;
  result = {};
  if (request.witnessVariable.empty() || request.witnessType.empty()
      || request.witnessBodyFormula.empty()
      || request.leafSourceFormula.empty()
      || request.leafScopeSourceFormula.empty()
      || request.leafScopeTargetFormula.empty()
      || request.leafScopeBridgeProof.empty()
      || request.canonicalWitness.empty()) {
    error = "positive-existential context request is incomplete";
    return false;
  }

  std::size_t fresh = 0;
  const auto name = [&](const char* stem) {
    return std::string("ivy_sm_p_") + stem + std::to_string(fresh++);
  };
  const auto formula = [](const std::string& value) {
    return "(formula " + value + ")";
  };
  const auto term = [](const std::string& value) {
    return "(term " + value + ")";
  };
  const auto tmh = [](const std::string& value) {
    return "(TMH " + quotePreservedName(value) + ")";
  };
  const auto hypothesis = [](const std::string& value) {
    return "(hyp " + quotePreservedName(value) + ")";
  };
  const auto proofApply = [](const std::string& left,
                             const std::string& right) {
    return "(proof_apply " + left + " " + right + ")";
  };
  const auto termApply = [](const std::string& proof,
                            const std::string& argument) {
    return "(term_apply " + proof + " " + argument + ")";
  };
  const auto proofLambda = [&](const std::string& variable,
                               const std::string& proposition,
                               const std::string& body) {
    return "(proof_lambda " + quotePreservedName(variable) + " "
      + formula(proposition) + " " + body + ")";
  };
  const auto termLambda = [](const std::string& variable,
                             const std::string& type,
                             const std::string& body) {
    return "(term_lambda " + quotePreservedName(variable) + " "
      + type + " " + body + ")";
  };
  const auto implication = [](const std::string& left,
                              const std::string& right) {
    return "(IMP " + left + " " + right + ")";
  };
  const auto forall = [](const std::string& variable,
                         const std::string& type,
                         const std::string& body) {
    return "(ALLV " + quotePreservedName(variable) + " " + type
      + " " + body + ")";
  };
  const auto exists = [](const std::string& variable,
                         const std::string& type,
                         const std::string& body) {
    return "(AP (TMH \"vampire_exists_prop\") (VLAMV "
      + quotePreservedName(variable) + " " + type + " " + body + "))";
  };
  const auto junction = [](bool conjunction,
                           const std::string& left,
                           const std::string& right) {
    return "(AP (AP (TMH \""
      + std::string(conjunction ? "vampire_and" : "vampire_or")
      + "\") " + left + ") " + right + ")";
  };
  const auto existsIntro = [&](const std::string& body,
                               const std::string& witness,
                               const std::string& bodyProof) {
    const std::string target = name("exists_target_");
    const std::string handler = name("exists_handler_");
    const std::string targetTerm = tmh(target);
    return termLambda(
      target,
      "(PROP)",
      proofLambda(
        handler,
        forall(
          request.witnessVariable,
          request.witnessType,
          implication(body, targetTerm)),
        proofApply(
          termApply(hypothesis(handler), term(witness)),
          bodyProof)));
  };
  const auto junctionIntro = [&](bool conjunction,
                                 const std::string& left,
                                 const std::string& right,
                                 const std::string& leftProof,
                                 const std::string& rightProof,
                                 bool selectLeft) {
    const std::string target = name("junction_target_");
    const std::string leftHandler = name("junction_left_");
    const std::string rightHandler = name("junction_right_");
    const std::string targetTerm = tmh(target);
    if (conjunction) {
      return termLambda(
        target,
        "(PROP)",
        proofLambda(
          leftHandler,
          implication(left, implication(right, targetTerm)),
          proofApply(
            proofApply(hypothesis(leftHandler), leftProof),
            rightProof)));
    }
    return termLambda(
      target,
      "(PROP)",
      proofLambda(
        leftHandler,
        implication(left, targetTerm),
        proofLambda(
          rightHandler,
          implication(right, targetTerm),
          proofApply(
            hypothesis(selectLeft ? leftHandler : rightHandler),
            selectLeft ? leftProof : rightProof))));
  };

  struct State {
    std::string source;
    std::string body;
    std::string theorem;
    std::string transform;
    std::vector<std::pair<std::string, std::string>> dependencies;
  } state;
  state.source = request.leafSourceFormula;
  state.body = request.witnessBodyFormula;
  state.theorem = exists(
    request.witnessVariable, request.witnessType, state.body);
  const std::string leafHypothesis = name("leaf_source_");
  state.transform = proofLambda(
    leafHypothesis, state.source, hypothesis(leafHypothesis));

  struct ScopeState {
    std::string source;
    std::string target;
    std::string bridge;
  } scope;
  scope.source = request.leafScopeSourceFormula;
  scope.target = request.leafScopeTargetFormula;
  scope.bridge = request.leafScopeBridgeProof;

  PreservedSexpr expectedLeaf;
  PreservedSexpr actualLeaf;
  if (!parser.parse(state.source, actualLeaf)
      || !parser.parse(state.theorem, expectedLeaf)
      || actualLeaf.render() != expectedLeaf.render()) {
    error = "positive-existential leaf is not its declared Church existential";
    return false;
  }

  const auto wrapDependencies = [&](std::string proof) {
    for (auto dependency = state.dependencies.rbegin();
         dependency != state.dependencies.rend();
         ++dependency) {
      proof = termLambda(dependency->first, dependency->second, proof);
    }
    return proof;
  };
  const auto applyDependencies = [&](std::string proof) {
    for (const auto& dependency : state.dependencies) {
      proof = termApply(proof, term(tmh(dependency.first)));
    }
    return proof;
  };

  for (auto frame = request.frames.rbegin();
       frame != request.frames.rend();
       ++frame) {
    if (frame->primitive == "skolem_forall_map") {
      if (frame->variable.empty() || frame->variableType.empty()) {
        error = "positive-existential forall frame is incomplete";
        return false;
      }
      const std::string source = forall(
        frame->variable, frame->variableType, state.source);
      const std::string theorem = forall(
        frame->variable, frame->variableType, state.theorem);
      const std::string input = name("forall_source_");
      state.transform = proofLambda(
        input,
        source,
        termLambda(
          frame->variable,
          frame->variableType,
          proofApply(
            state.transform,
            termApply(
              hypothesis(input),
              term(tmh(frame->variable))))));
      state.dependencies.insert(
        state.dependencies.begin(),
        {frame->variable, frame->variableType});
      state.source = source;
      state.theorem = theorem;
      continue;
    }

    const bool conjunction =
      frame->primitive == "skolem_and_left_map"
      || frame->primitive == "skolem_and_right_map";
    const bool disjunction =
      frame->primitive == "skolem_or_left_map"
      || frame->primitive == "skolem_or_right_map";
    if ((!conjunction && !disjunction) || frame->siblingFormula.empty()) {
      error = "positive-existential context has an unsupported frame";
      return false;
    }

    const std::string oldScopeSource = scope.source;
    const std::string oldScopeTarget = scope.target;
    const std::string oldScopeBridge = scope.bridge;
    const std::string scopeSourceLeft = frame->selectedLeft
      ? oldScopeSource : frame->siblingFormula;
    const std::string scopeSourceRight = frame->selectedLeft
      ? frame->siblingFormula : oldScopeSource;
    const std::string scopeTargetLeft = frame->selectedLeft
      ? oldScopeTarget : frame->siblingFormula;
    const std::string scopeTargetRight = frame->selectedLeft
      ? frame->siblingFormula : oldScopeTarget;
    const std::string scopeInput = name("scope_junction_source_");
    const std::string scopeLeft = name("scope_junction_left_");
    const std::string scopeRight = name("scope_junction_right_");
    const auto scopeIntroduction = [&](bool branchLeft) {
      std::string leftProof = hypothesis(scopeLeft);
      std::string rightProof = hypothesis(scopeRight);
      if (frame->selectedLeft && branchLeft) {
        leftProof = proofApply(oldScopeBridge, leftProof);
      } else if (!frame->selectedLeft && !branchLeft) {
        rightProof = proofApply(oldScopeBridge, rightProof);
      }
      return junctionIntro(
        conjunction,
        scopeTargetLeft,
        scopeTargetRight,
        leftProof,
        rightProof,
        branchLeft);
    };
    std::string scopeBody;
    const std::string scopeTarget = junction(
      conjunction, scopeTargetLeft, scopeTargetRight);
    if (conjunction) {
      scopeBody = proofApply(
        termApply(hypothesis(scopeInput), formula(scopeTarget)),
        proofLambda(
          scopeLeft,
          scopeSourceLeft,
          proofLambda(
            scopeRight,
            scopeSourceRight,
            scopeIntroduction(frame->selectedLeft))));
    } else {
      scopeBody = proofApply(
        proofApply(
          termApply(hypothesis(scopeInput), formula(scopeTarget)),
          proofLambda(
            scopeLeft,
            scopeSourceLeft,
            scopeIntroduction(true))),
        proofLambda(
          scopeRight,
          scopeSourceRight,
          scopeIntroduction(false)));
    }
    scope.source = junction(
      conjunction, scopeSourceLeft, scopeSourceRight);
    scope.target = scopeTarget;
    scope.bridge = proofLambda(scopeInput, scope.source, scopeBody);

    const std::string oldSource = state.source;
    const std::string oldBody = state.body;
    const std::string oldTransform = state.transform;
    const std::string left = frame->selectedLeft
      ? oldSource : frame->siblingFormula;
    const std::string right = frame->selectedLeft
      ? frame->siblingFormula : oldSource;
    const std::string newBody = frame->selectedLeft
      ? junction(conjunction, oldBody, frame->siblingFormula)
      : junction(conjunction, frame->siblingFormula, oldBody);
    std::string newTheorem = exists(
      request.witnessVariable, request.witnessType, newBody);
    for (auto dependency = state.dependencies.rbegin();
         dependency != state.dependencies.rend();
         ++dependency) {
      newTheorem = forall(
        dependency->first, dependency->second, newTheorem);
    }

    const auto selectedBranch = [&](const std::string& selectedProof,
                                    const std::string& siblingProof) {
      std::string oldExists = proofApply(oldTransform, selectedProof);
      oldExists = applyDependencies(std::move(oldExists));
      const std::string witnessBody = name("witness_body_");
      const std::string witnessProof = hypothesis(witnessBody);
      const std::string leftProof = frame->selectedLeft
        ? witnessProof : siblingProof;
      const std::string rightProof = frame->selectedLeft
        ? siblingProof : witnessProof;
      const std::string bodyProof = junctionIntro(
        conjunction,
        frame->selectedLeft ? oldBody : frame->siblingFormula,
        frame->selectedLeft ? frame->siblingFormula : oldBody,
        leftProof,
        rightProof,
        frame->selectedLeft);
      const std::string targetExists = exists(
        request.witnessVariable, request.witnessType, newBody);
      std::string mapped = proofApply(
        termApply(oldExists, formula(targetExists)),
        termLambda(
          request.witnessVariable,
          request.witnessType,
          proofLambda(
            witnessBody,
            oldBody,
            existsIntro(
              newBody,
              tmh(request.witnessVariable),
              bodyProof))));
      return wrapDependencies(std::move(mapped));
    };
    const auto siblingBranch = [&](const std::string& siblingProof) {
      const std::string leftProof = frame->selectedLeft
        ? std::string() : siblingProof;
      const std::string rightProof = frame->selectedLeft
        ? siblingProof : std::string();
      const std::string bodyProof = junctionIntro(
        false,
        frame->selectedLeft ? oldBody : frame->siblingFormula,
        frame->selectedLeft ? frame->siblingFormula : oldBody,
        leftProof,
        rightProof,
        !frame->selectedLeft);
      std::string introduced = existsIntro(
        newBody,
        tmh(request.witnessVariable),
        bodyProof);
      introduced = termApply(
        termLambda(
          request.witnessVariable,
          request.witnessType,
          introduced),
        term(request.canonicalWitness));
      return wrapDependencies(std::move(introduced));
    };

    const std::string input = name("junction_source_");
    const std::string leftName = name("junction_case_left_");
    const std::string rightName = name("junction_case_right_");
    std::string body;
    if (conjunction) {
      body = selectedBranch(
        hypothesis(frame->selectedLeft ? leftName : rightName),
        hypothesis(frame->selectedLeft ? rightName : leftName));
      body = proofApply(
        termApply(hypothesis(input), formula(newTheorem)),
        proofLambda(
          leftName,
          left,
          proofLambda(rightName, right, body)));
    } else {
      const std::string leftBranch = proofLambda(
        leftName,
        left,
        frame->selectedLeft
          ? selectedBranch(hypothesis(leftName), std::string())
          : siblingBranch(hypothesis(leftName)));
      const std::string rightBranch = proofLambda(
        rightName,
        right,
        frame->selectedLeft
          ? siblingBranch(hypothesis(rightName))
          : selectedBranch(hypothesis(rightName), std::string()));
      body = proofApply(
        proofApply(
          termApply(hypothesis(input), formula(newTheorem)),
          leftBranch),
        rightBranch);
    }
    state.source = junction(conjunction, left, right);
    state.body = newBody;
    state.theorem = newTheorem;
    state.transform = proofLambda(input, state.source, body);
  }

  PreservedSexpr parsedSource;
  PreservedSexpr parsedTheorem;
  PreservedSexpr parsedProof;
  PreservedSexpr parsedScopeSource;
  PreservedSexpr parsedScopeTarget;
  PreservedSexpr parsedScopeBridge;
  if (!parser.parse(state.source, parsedSource)
      || !parser.parse(state.theorem, parsedTheorem)
      || !parser.parse(state.transform, parsedProof)
      || !parser.parse(scope.source, parsedScopeSource)
      || !parser.parse(scope.target, parsedScopeTarget)
      || !parser.parse(scope.bridge, parsedScopeBridge)) {
    error = "positive-existential context expansion is not valid Ivy syntax";
    return false;
  }
  result.sourceFormula = parsedSource.render();
  result.theoremFormula = parsedTheorem.render();
  result.proofTransform = parsedProof.render();
  result.scopeSourceFormula = parsedScopeSource.render();
  result.scopeTargetFormula = parsedScopeTarget.render();
  result.scopeBridgeProof = parsedScopeBridge.render();
  return true;
}

namespace {

using RenderedChoiceNode =
  MegalodonKernelSyntax::RenderedKernelChoiceProofNode;

bool refineResolutionArguments(
  const RenderedChoiceNode& left,
  std::vector<std::string>& leftArguments,
  std::size_t leftPivot,
  const RenderedChoiceNode& right,
  std::vector<std::string>& rightArguments,
  std::size_t rightPivot,
  const std::vector<std::pair<std::string, std::string>>& localParameters,
  std::map<std::string, PreservedSexpr>* refinements = nullptr)
{
  PreservedSexprParser parser;
  const auto instantiatedPivot = [&]
    (const RenderedChoiceNode& parent,
     const std::vector<std::string>& arguments,
     std::size_t pivot,
     bool& positive,
     PreservedSexpr& atom) {
    PreservedSexpr renderedClause;
    if (!parent.hasResultClause
        || arguments.size() != parent.parameters.size()
        || !parser.parse(parent.resultClause, renderedClause)) {
      return false;
    }
    const PreservedSexpr* clause = &renderedClause;
    if (sexprHead(*clause, "clause")
        && clause->items.size() == 2
        && sexprHead(clause->items[1], "clause")) {
      clause = &clause->items[1];
    }
    if (!sexprHead(*clause, "clause")
        || pivot + 1 >= clause->items.size()) {
      return false;
    }
    PreservedSexpr literal = clause->items[pivot + 1];
    for (std::size_t index = 0; index < arguments.size(); ++index) {
      PreservedSexpr argument;
      if (!parser.parse(arguments[index], argument)) {
        return false;
      }
      const PreservedSexpr* term = &argument;
      if (sexprHead(argument, "term") && argument.items.size() == 2) {
        term = &argument.items[1];
      }
      literal = substituteNamedVariableSexpr(
        literal, parent.parameters[index].first, *term);
    }
    positive = sexprHead(literal, "pos");
    if ((!positive && !sexprHead(literal, "neg"))
        || literal.items.size() != 2) {
      return false;
    }
    atom = betaNormalizeSexpr(literal.items[1]);
    return true;
  };
  const auto complementaryPivots = [&]
    (const RenderedChoiceNode& first,
     const std::vector<std::string>& firstArguments,
     std::size_t firstPivot,
     const RenderedChoiceNode& second,
     const std::vector<std::string>& secondArguments,
     std::size_t secondPivot) {
    bool firstPositive = false;
    bool secondPositive = false;
    PreservedSexpr firstAtom;
    PreservedSexpr secondAtom;
    return instantiatedPivot(
             first, firstArguments, firstPivot,
             firstPositive, firstAtom)
      && instantiatedPivot(
           second, secondArguments, secondPivot,
           secondPositive, secondAtom)
      && firstPositive != secondPositive
      && alphaEquivalentSexpr(firstAtom, secondAtom);
  };
  const auto specialize = [&]
    (const RenderedChoiceNode& patternParent,
     std::vector<std::string>& patternArguments,
     std::size_t patternPivot,
     const RenderedChoiceNode& targetParent,
     const std::vector<std::string>& targetArguments,
     std::size_t targetPivot) {
    bool patternPositive = false;
    bool targetPositive = false;
    PreservedSexpr patternAtom;
    PreservedSexpr targetAtom;
    if (!instantiatedPivot(
          patternParent, patternArguments, patternPivot,
          patternPositive, patternAtom)
        || !instantiatedPivot(
          targetParent, targetArguments, targetPivot,
          targetPositive, targetAtom)
        || patternPositive == targetPositive) {
      return false;
    }

    std::set<std::string> matchVariables;
    for (std::size_t index = 0;
         index < patternArguments.size(); ++index) {
      PreservedSexpr argument;
      std::string variable;
      if (!parser.parse(patternArguments[index], argument)) {
        continue;
      }
      const PreservedSexpr* term = &argument;
      if (sexprHead(argument, "term") && argument.items.size() == 2) {
        term = &argument.items[1];
      }
      if (!sexprHead(*term, "TMH")
          || term->items.size() != 2
          || !preservedName(term->items[1], variable)) {
        continue;
      }
      auto local = std::find_if(
        localParameters.begin(), localParameters.end(),
        [&](const auto& parameter) {
          return parameter.first == variable;
        });
      if (local != localParameters.end()
          && local->second == patternParent.parameters[index].second) {
        matchVariables.insert(variable);
      }
    }
    if (matchVariables.empty()) return false;

    std::map<std::string, PreservedSexpr> bindings;
    std::set<std::string> boundVariables;
    std::function<bool(const PreservedSexpr&, const PreservedSexpr&)> match;
    match = [&](const PreservedSexpr& pattern,
                const PreservedSexpr& target) {
      if (alphaEquivalentSexpr(pattern, target)) return true;
      if (sexprHead(pattern, "TMH") && pattern.items.size() == 2) {
        std::string variable;
        if (preservedName(pattern.items[1], variable)
            && matchVariables.find(variable) != matchVariables.end()
            && boundVariables.find(variable) == boundVariables.end()) {
          auto binding = bindings.find(variable);
          if (binding != bindings.end()) {
            return alphaEquivalentSexpr(binding->second, target);
          }
          if (containsFreeNamedTermSexpr(target, variable)) return false;
          bindings.emplace(variable, target);
          return true;
        }
      }
      if (pattern.atom || target.atom
          || pattern.items.size() != target.items.size()
          || pattern.items.empty() || target.items.empty()
          || pattern.items.front() != target.items.front()) {
        return false;
      }
      const bool binder =
        (sexprHead(pattern, "ALLV")
         || sexprHead(pattern, "LAMV")
         || sexprHead(pattern, "VLAMV"))
        && pattern.items.size() == 4;
      std::string binderName;
      if (binder
          && (!preservedName(pattern.items[1], binderName)
              || pattern.items[1] != target.items[1]
              || pattern.items[2] != target.items[2])) {
        return false;
      }
      if (binder) boundVariables.insert(binderName);
      const std::size_t first = binder ? 3 : 1;
      for (std::size_t index = first;
           index < pattern.items.size(); ++index) {
        if (!match(pattern.items[index], target.items[index])) {
          if (binder) boundVariables.erase(binderName);
          return false;
        }
      }
      if (binder) boundVariables.erase(binderName);
      return true;
    };
    if (!match(patternAtom, targetAtom) || bindings.empty()) return false;

    std::vector<std::string> specialized;
    specialized.reserve(patternArguments.size());
    for (const std::string& argumentText : patternArguments) {
      PreservedSexpr argument;
      if (!parser.parse(argumentText, argument)) return false;
      for (const auto& binding : bindings) {
        argument = substituteNamedVariableSexpr(
          argument, binding.first, binding.second);
      }
      specialized.push_back(argument.render());
    }
    if (!complementaryPivots(
          patternParent, specialized, patternPivot,
          targetParent, targetArguments, targetPivot)) {
      return false;
    }
    if (refinements != nullptr) {
      for (const auto& binding : bindings) {
        const auto existing = refinements->find(binding.first);
        if (existing != refinements->end()
            && !alphaEquivalentSexpr(existing->second, binding.second)) {
          return false;
        }
      }
      refinements->insert(bindings.begin(), bindings.end());
    }
    patternArguments = std::move(specialized);
    return true;
  };

  if (complementaryPivots(
        left, leftArguments, leftPivot,
        right, rightArguments, rightPivot)) {
    return true;
  }
  std::vector<std::string> specialized = leftArguments;
  if (specialize(
        left, specialized, leftPivot,
        right, rightArguments, rightPivot)) {
    leftArguments = std::move(specialized);
    return true;
  }
  specialized = rightArguments;
  if (specialize(
        right, specialized, rightPivot,
        left, leftArguments, leftPivot)) {
    rightArguments = std::move(specialized);
    return true;
  }
  return false;
}

}

bool expandChoiceNormalizedProof(
  std::vector<ChoiceProofStep>& steps,
  const std::vector<MegalodonKernelSyntax::PrimitiveStep>& skolemSteps,
  const std::vector<ChoiceTermDefinition>& termDefinitions,
  const std::string& finalStep,
  MegalodonKernelSyntax::RenderedKernelChoiceProof& result,
  std::string& error)
{
  using PrimitiveStep = MegalodonKernelSyntax::PrimitiveStep;
  using IvyRule = MegalodonKernelSyntax::RenderedKernelIvyRule;
  using ChoiceNode =
    MegalodonKernelSyntax::RenderedKernelChoiceProofNode;
  PreservedSexprParser parser;
  result = {};
  if (steps.empty() || finalStep.empty()
      || (skolemSteps.empty() && termDefinitions.empty())) {
    error = "choice-normalized proof DAG has no steps, local definitions, or root";
    return false;
  }

  std::map<std::string, PreservedSexpr> replacements;
  std::vector<std::string> eliminated;
  std::size_t sharedTermDefinitionOrdinal = 0;
  const auto choiceOperator = [](const std::string& type) {
    if (type == "(SET)") return std::string("Eps_i");
    if (type == "(PROP)") return std::string("Eps_prop");
    if (type == "(AR (SET) (PROP))") return std::string("Eps_set_prop");
    if (type == "(AR (SET) (SET))") return std::string("Eps_set_set");
    if (type == "(AR (SET) (AR (SET) (PROP)))") {
      return std::string("Eps_set_set_prop");
    }
    return std::string();
  };
  const auto replaceConstants = [&](const PreservedSexpr& source,
                                    const auto& self) -> PreservedSexpr {
    if (sexprHead(source, "TMH") && source.items.size() == 2) {
      std::string name;
      if (preservedName(source.items[1], name)) {
        auto replacement = replacements.find(name);
        if (replacement != replacements.end()) return replacement->second;
      }
    }
    if (source.atom) return source;
    PreservedSexpr replaced;
    replaced.atom = false;
    replaced.items.reserve(source.items.size());
    if (!source.items.empty()) {
      replaced.items.push_back(source.items.front());
    }
    for (std::size_t index = 1; index < source.items.size(); ++index) {
      replaced.items.push_back(self(source.items[index], self));
    }
    return replaced;
  };
  const auto sharedTermType = [](const auto& parameters,
                                 std::string resultType) {
    for (auto parameter = parameters.rbegin();
         parameter != parameters.rend(); ++parameter) {
      resultType = "(AR " + parameter->second + " " + resultType + ")";
    }
    return resultType;
  };
  const auto installSharedTermDefinition =
    [&](const std::string& original,
        const std::string& type,
        PreservedSexpr body) {
      const std::string alias = "vampire_ivy_shared_term_"
        + std::to_string(sharedTermDefinitionOrdinal++);
      result.definitions.push_back({alias, type, body.render()});
      replacements.emplace(
        original, quotedTmh(quotePreservedName(alias)));
    };

  for (const PrimitiveStep& step : skolemSteps) {
    if (!step.builderOwned || step.rule != "skolem_formula"
        || step.producerSkolemChoiceDefinitions.empty()) {
      error = "choice-normalized proof DAG received an incomplete Skolem step";
      return false;
    }
    for (const auto& definition : step.producerSkolemChoiceDefinitions) {
      if (definition.symbol.empty()
          || replacements.find(definition.symbol) != replacements.end()) {
        error = "choice-normalized proof DAG repeats a Skolem symbol";
        return false;
      }
      PreservedSexpr source;
      if (!parser.parse(definition.sourceFormulaSexpr, source)
          || !sexprHead(source, "AP") || source.items.size() != 3
          || !namedTermSexpr(source.items[1], "vampire_exists_prop")
          || !(sexprHead(source.items[2], "VLAMV")
               || sexprHead(source.items[2], "LAMV"))
          || source.items[2].items.size() != 4) {
        error = "choice definition for " + definition.symbol
          + " is not an exact producer existential";
        return false;
      }
      std::string witnessVariable;
      if (!preservedName(source.items[2].items[1], witnessVariable)
          || source.items[2].items[2].render()
             != definition.witnessTypeSexpr) {
        error = "choice definition for " + definition.symbol
          + " has the wrong producer witness binder";
        return false;
      }
      const std::string epsilon = choiceOperator(definition.witnessTypeSexpr);
      if (epsilon.empty()) {
        error = "choice definition for " + definition.symbol
          + " uses an unsupported witness type";
        return false;
      }
      const PreservedSexpr body =
        replaceConstants(source.items[2].items[3], replaceConstants);
      std::string rendered =
        "(AP (TMH " + quotePreservedName(epsilon) + ")"
        + " (LAMV " + quotePreservedName(witnessVariable) + " "
        + definition.witnessTypeSexpr + " " + body.render() + "))";
      for (auto parameter = definition.parameters.rbegin();
           parameter != definition.parameters.rend(); ++parameter) {
        if (parameter->first.empty() || parameter->second.empty()) {
          error = "choice definition for " + definition.symbol
            + " has an incomplete dependency binder";
          return false;
        }
        rendered =
          "(LAMV " + quotePreservedName(parameter->first) + " "
          + parameter->second + " " + rendered + ")";
      }
      PreservedSexpr replacement;
      if (!parser.parse(rendered, replacement)) {
        error = "choice definition for " + definition.symbol
          + " cannot be represented in the Ivy term language";
        return false;
      }
      installSharedTermDefinition(
        definition.symbol,
        sharedTermType(definition.parameters, definition.witnessTypeSexpr),
        std::move(replacement));
      eliminated.push_back(definition.symbol);
    }
  }

  std::map<std::string, const ChoiceTermDefinition*> termDefinitionBySymbol;
  for (const ChoiceTermDefinition& definition : termDefinitions) {
    if (definition.stepId.empty() || definition.symbol.empty()
        || definition.resultType.empty() || definition.body.empty()
        || (definition.emitDefinitionClaim && definition.resultClause.empty())
        || replacements.find(definition.symbol) != replacements.end()
        || !termDefinitionBySymbol.emplace(
              definition.symbol, &definition).second) {
      error = "choice-normalized proof DAG has an invalid producer term definition";
      return false;
    }
  }
  std::map<std::string, unsigned> termDefinitionState;
  std::function<bool(const std::string&)> expandTermDefinition;
  expandTermDefinition = [&](const std::string& symbol) {
    const unsigned state = termDefinitionState[symbol];
    if (state == 1) {
      error = "choice-normalized proof DAG has cyclic producer term definitions";
      return false;
    }
    if (state == 2) return true;
    termDefinitionState[symbol] = 1;
    const ChoiceTermDefinition& definition =
      *termDefinitionBySymbol.at(symbol);
    PreservedSexpr body;
    if (!parser.parse(definition.body, body)) {
      error = "choice-normalized producer term definition " + symbol
        + " has an unreadable body";
      return false;
    }
    std::function<bool(PreservedSexpr&)> expandBody;
    expandBody = [&](PreservedSexpr& source) {
      std::string referenced;
      if (sexprHead(source, "TMH") && source.items.size() == 2
          && preservedName(source.items[1], referenced)) {
        auto local = termDefinitionBySymbol.find(referenced);
        if (local != termDefinitionBySymbol.end()) {
          if (!expandTermDefinition(referenced)) return false;
          source = replacements.at(referenced);
          return true;
        }
        auto replacement = replacements.find(referenced);
        if (replacement != replacements.end()) {
          source = replacement->second;
          return true;
        }
      }
      if (source.atom) return true;
      for (std::size_t index = 1; index < source.items.size(); ++index) {
        if (!expandBody(source.items[index])) return false;
      }
      return true;
    };
    if (!expandBody(body)) return false;
    std::string rendered = body.render();
    for (auto parameter = definition.parameters.rbegin();
         parameter != definition.parameters.rend(); ++parameter) {
      if (parameter->first.empty() || parameter->second.empty()) {
        error = "choice-normalized producer term definition " + symbol
          + " has an incomplete parameter contract";
        return false;
      }
      rendered =
        "(LAMV " + quotePreservedName(parameter->first) + " "
        + parameter->second + " " + rendered + ")";
    }
    PreservedSexpr replacement;
    if (!parser.parse(rendered, replacement)) {
      error = "choice-normalized producer term definition " + symbol
        + " cannot be represented in the Ivy term language";
      return false;
    }
    installSharedTermDefinition(
      symbol,
      sharedTermType(definition.parameters, definition.resultType),
      std::move(replacement));
    termDefinitionState[symbol] = 2;
    return true;
  };
  for (const ChoiceTermDefinition& definition : termDefinitions) {
    if (!expandTermDefinition(definition.symbol)) return false;
  }
  for (const ChoiceTermDefinition& definition : termDefinitions) {
    if (definition.includeInEliminatedInventory) {
      eliminated.push_back(definition.symbol);
    }
  }

  std::map<std::string, ChoiceProofStep*> byId;
  for (ChoiceProofStep& step : steps) {
    if (step.primitive.id.empty()) {
      error = "choice-normalized proof DAG has an unnamed step";
      return false;
    }
    if (!step.primitive.builderOwned) {
      error = "choice-normalized proof DAG step " + step.primitive.id
        + " is not builder-owned";
      return false;
    }
    if (!byId.emplace(step.primitive.id, &step).second) {
      error = "choice-normalized proof DAG repeats step " + step.primitive.id;
      return false;
    }
  }
  if (byId.find(finalStep) == byId.end()) {
    error = "choice-normalized proof DAG does not contain its final step";
    return false;
  }

  // AVATAR clauses with split dependencies can be absent from the ordinary
  // native step stream.  Their split_dependency primitive is the explicit,
  // clause-identical certificate object that later Ivy steps must cite.  Keep
  // this producer-owned identity map so prooftrans never leaves the consumer
  // to recover the replacement from an unavailable owner name.
  std::map<std::string, std::string> splitDependencyByOwner;
  for (const auto& entry : byId) {
    const PrimitiveStep& identity = entry.second->primitive;
    if (identity.rule != "split_dependency") continue;
    if (identity.parentIds.size() != 1
        || !identity.hasResultClause || identity.hasResultFormula) {
      error = "choice-normalized split dependency " + identity.id
        + " has an incomplete identity contract";
      return false;
    }
    const std::string& ownerId = identity.parentIds.front();
    auto owner = byId.find(ownerId);
    if (owner == byId.end()) {
      error = "choice-normalized split dependency " + identity.id
        + " has no typed producer owner " + ownerId;
      return false;
    }
    const PrimitiveStep& ownerStep = owner->second->primitive;
    if (!ownerStep.hasResultClause || ownerStep.hasResultFormula
        || ownerStep.resultClause != identity.resultClause) {
      error = "choice-normalized split dependency " + identity.id
        + " does not reproduce owner " + ownerId;
      return false;
    }
    if (!splitDependencyByOwner.emplace(ownerId, identity.id).second) {
      error = "choice-normalized proof DAG has multiple split identities for owner "
        + ownerId;
      return false;
    }
  }

  std::set<std::string> ancestors;
  std::function<bool(const std::string&)> collectAncestors;
  collectAncestors = [&](const std::string& id) {
    if (!ancestors.insert(id).second) return true;
    auto found = byId.find(id);
    if (found == byId.end()) return true;
    for (const std::string& parent : found->second->primitive.parentIds) {
      if (byId.find(parent) != byId.end() && !collectAncestors(parent)) {
        return false;
      }
    }
    return true;
  };
  if (!collectAncestors(finalStep)) {
    error = "choice-normalized proof DAG ancestor traversal failed";
    return false;
  }

  // Split dependencies are explicit identity objects in the native
  // certificate.  Keep every such object whose owner is on the refutation
  // path, even when no later inference selected the identity as its parent.
  // This makes the producer DAG replace the complete local-symbol-bearing
  // native slice instead of leaving the consumer to infer that it is dead.
  std::vector<std::string> ownerLinkedObjects;
  bool addedOwnerLinkedObject = true;
  while (addedOwnerLinkedObject) {
    addedOwnerLinkedObject = false;
    for (const auto& entry : byId) {
      const PrimitiveStep& step = entry.second->primitive;
      const bool identity =
        step.rule == "split_dependency" && step.parentIds.size() == 1;
      const bool component =
        step.rule == "avatar_component" && !step.parentIds.empty();
      const bool linked = std::any_of(
        step.parentIds.begin(), step.parentIds.end(),
        [&](const std::string& parent) {
          return parent != finalStep
            && ancestors.find(parent) != ancestors.end();
        });
      if ((identity || component) && linked
          && ancestors.insert(step.id).second) {
        ownerLinkedObjects.push_back(step.id);
        addedOwnerLinkedObject = true;
      }
    }
  }

  std::vector<ChoiceProofStep*> ordered;
  std::set<std::string> visiting;
  std::set<std::string> visited;
  std::function<bool(const std::string&)> order;
  order = [&](const std::string& id) {
    if (visited.find(id) != visited.end()) return true;
    if (!visiting.insert(id).second) return false;
    ChoiceProofStep& step = *byId.at(id);
    for (const std::string& parent : step.primitive.parentIds) {
      if (ancestors.find(parent) != ancestors.end()
          && byId.find(parent) != byId.end()
          && !order(parent)) {
        return false;
      }
    }
    visiting.erase(id);
    visited.insert(id);
    ordered.push_back(&step);
    return true;
  };
  for (const std::string& id : ownerLinkedObjects) {
    if (!order(id)) {
      error = "choice-normalized proof DAG is cyclic";
      return false;
    }
  }
  if (!order(finalStep)) {
    error = "choice-normalized proof DAG is cyclic";
    return false;
  }

  // A superposition remainder may contain the de Bruijn slot that was moved
  // below a lambda.  Vampire records an explicit epsilon repair on that root.
  // Carry its substitution only through descendants whose original result
  // still mentions the slot, and through the AVATAR definition consumed at
  // the first closing split.  This is prooftrans dataflow, not a consumer-side
  // search: conflicting branch witnesses fail closed.
  using ScopedChoiceEnvironment = std::map<std::string, PreservedSexpr>;
  std::map<std::string, ScopedChoiceEnvironment> scopedChoiceInput;
  std::map<std::string, ScopedChoiceEnvironment> scopedChoiceOutput;
  const auto mergeScopedChoice =
    [&](ScopedChoiceEnvironment& target,
        const ScopedChoiceEnvironment& source) {
      for (const auto& item : source) {
        auto inserted = target.emplace(item.first, item.second);
        if (!inserted.second && inserted.first->second != item.second) {
          return false;
        }
      }
      return true;
    };
  const auto parsedConclusion =
    [&](const PrimitiveStep& step, PreservedSexpr& conclusion) {
      const std::string& rendered = step.hasResultClause
        ? step.resultClause : step.resultFormula;
      return step.hasResultClause != step.hasResultFormula
        && parser.parse(rendered, conclusion);
    };
  for (ChoiceProofStep* wrapped : ordered) {
    PrimitiveStep& step = wrapped->primitive;
    ScopedChoiceEnvironment input;
    for (const std::string& parent : step.parentIds) {
      auto found = scopedChoiceOutput.find(parent);
      if (found != scopedChoiceOutput.end()
          && !mergeScopedChoice(input, found->second)) {
        error = "choice-normalized proof DAG merges distinct scoped lambda witnesses at "
          + step.id;
        return false;
      }
    }
    scopedChoiceInput.emplace(step.id, input);
    ScopedChoiceEnvironment output = input;
    if (step.producerScopedLambdaChoice != nullptr) {
      PreservedSexpr witness;
      const auto& choice = *step.producerScopedLambdaChoice;
      if (choice.parameter.empty() || choice.parameterType.empty()
          || choice.witnessTerm.empty() || choice.resultClause.empty()
          || choice.producerProof.empty()
          || !parser.parse(choice.witnessTerm, witness)
          || !output.emplace(choice.parameter, witness).second) {
        error = "choice-normalized proof DAG has an invalid scoped lambda witness at "
          + step.id;
        return false;
      }
    }
    PreservedSexpr conclusion;
    ScopedChoiceEnvironment retained;
    if (!parsedConclusion(step, conclusion)) {
      error = "choice-normalized proof DAG cannot read scoped lambda conclusion at "
        + step.id;
      return false;
    }
    for (const auto& item : output) {
      if (step.producerScopedLambdaChoice != nullptr
          || containsFreeNamedTermSexpr(conclusion, item.first)) {
        retained.insert(item);
      }
    }
    scopedChoiceOutput.emplace(step.id, std::move(retained));
  }

  std::map<std::string, ScopedChoiceEnvironment> scopedChoiceDefinitionInput;
  for (ChoiceProofStep* wrapped : ordered) {
    auto environment = scopedChoiceInput.find(wrapped->primitive.id);
    if (environment == scopedChoiceInput.end() || environment->second.empty()) {
      continue;
    }
    for (const std::string& parent : wrapped->primitive.parentIds) {
      auto found = byId.find(parent);
      if (found == byId.end()
          || found->second->primitive.rule != "avatar_definition") {
        continue;
      }
      PreservedSexpr conclusion;
      if (!parsedConclusion(found->second->primitive, conclusion)) return false;
      ScopedChoiceEnvironment relevant;
      for (const auto& item : environment->second) {
        if (containsFreeNamedTermSexpr(conclusion, item.first)) {
          relevant.insert(item);
        }
      }
      if (!relevant.empty()
          && !mergeScopedChoice(
               scopedChoiceDefinitionInput[parent], relevant)) {
        error = "choice-normalized AVATAR definition receives distinct scoped lambda witnesses at "
          + parent;
        return false;
      }
    }
  }

  const auto applyScopedChoice =
    [&](std::string& rendered,
        const ScopedChoiceEnvironment& environment) {
      if (rendered.empty() || environment.empty()) return true;
      PreservedSexpr value;
      if (!parser.parse(rendered, value)) return false;
      for (const auto& item : environment) {
        value = substituteNamedVariableSexpr(
          value, item.first, item.second);
      }
      rendered = value.render();
      return true;
    };
  for (ChoiceProofStep* wrapped : ordered) {
    PrimitiveStep& step = wrapped->primitive;
    ScopedChoiceEnvironment environment = scopedChoiceInput[step.id];
    auto definitionEnvironment = scopedChoiceDefinitionInput.find(step.id);
    if (definitionEnvironment != scopedChoiceDefinitionInput.end()
        && !mergeScopedChoice(environment, definitionEnvironment->second)) {
      return false;
    }
    if (step.producerScopedLambdaChoice != nullptr) {
      const auto choice = step.producerScopedLambdaChoice;
      PreservedSexpr witness;
      if (!parser.parse(choice->witnessTerm, witness)
          || !environment.emplace(choice->parameter, witness).second) {
        return false;
      }
      step.resultClause = choice->resultClause;
      step.producerResultLiterals = choice->resultLiterals;
      step.producerProof = choice->producerProof;
      step.rule = "scoped_lambda_choice";
      step.forceChoiceNormalization = true;
      step.producerScopedLambdaChoice.reset();
    }
    if (environment.empty()) continue;
    if (!applyScopedChoice(step.resultClause, environment)
        || !applyScopedChoice(step.resultFormula, environment)
        || !applyScopedChoice(step.producerProof, environment)
        || !applyScopedChoice(step.producerCnfSourceFormula, environment)) {
      error = "choice-normalized proof DAG cannot apply its scoped lambda witness at "
        + step.id;
      return false;
    }
    for (auto& claim : step.producerProofClaims) {
      if (!applyScopedChoice(claim.resultFormula, environment)
          || !applyScopedChoice(claim.resultClause, environment)
          || !applyScopedChoice(claim.producerProof, environment)) {
        return false;
      }
    }
    for (auto& field : step.fields) {
      PreservedSexpr parsed;
      if (!parser.parse(field.second, parsed)) continue;
      for (const auto& item : environment) {
        parsed = substituteNamedVariableSexpr(
          parsed, item.first, item.second);
      }
      field.second = parsed.render();
    }
  }

  // Parse AVATAR split names into explicit Ivy definition objects.  Definitions
  // remain shared names in the certificate.  Any Skolem constants in their
  // bodies are redirected to the producer's preceding shared choice aliases.
  std::map<std::string, PreservedSexpr> splitDefinitions;
  std::set<std::string> choiceDependentSplitDefinitions;
  for (ChoiceProofStep* wrapped : ordered) {
    const PrimitiveStep& step = wrapped->primitive;
    if (step.rule != "avatar_definition") continue;
    const auto definition = std::find_if(
      step.producerProofClaims.begin(), step.producerProofClaims.end(),
      [&](const auto& claim) {
        return claim.replacesDefinition == step.id
          && !claim.resultFormula.empty();
      });
    PreservedSexpr relation;
    if (definition == step.producerProofClaims.end()
        || !parser.parse(definition->resultFormula, relation)) {
      error = "choice-normalized AVATAR definition " + step.id
        + " has no exact relation formula";
      return false;
    }
    const PreservedSexpr originalRelation = relation;
    relation = replaceConstants(relation, replaceConstants);
    // A producer-private alias need not be part of the serialized eliminated
    // inventory, but replacing it still changes the split's meaning.  Such a
    // split must stay unfolded throughout the normalized proof DAG.
    const bool choiceDependent = relation != originalRelation;
    if (std::any_of(
          eliminated.begin(), eliminated.end(),
          [&](const std::string& symbol) {
            return containsNamedTermSexpr(relation, symbol);
          })) {
      error = "choice-normalized AVATAR definition " + step.id
        + " retains a certificate-local symbol after aliasing";
      return false;
    }
    if (!sexprHead(relation, "AP") || relation.items.size() != 3
        || !sexprHead(relation.items[1], "AP")
        || relation.items[1].items.size() != 3
        || !namedTermSexpr(relation.items[1].items[1], "vampire_and")) {
      error = "choice-normalized AVATAR definition " + step.id
        + " is not an exact conjunction of implications";
      return false;
    }
    const PreservedSexpr& left = relation.items[1].items[2];
    const PreservedSexpr& right = relation.items[2];
    if (!sexprHead(left, "IMP") || left.items.size() != 3
        || !sexprHead(right, "IMP") || right.items.size() != 3
        || left.items[2].render() != right.items[1].render()
        || left.items[1].render() != right.items[2].render()
        || !sexprHead(left.items[1], "TMH")
        || left.items[1].items.size() != 2) {
      error = "choice-normalized AVATAR definition " + step.id
        + " does not identify one exact split component";
      return false;
    }
    std::string split;
    if (!preservedName(left.items[1].items[1], split)
        || split.compare(0, 6, "split_") != 0
        || !splitDefinitions.emplace(split, left.items[2]).second) {
      error = "choice-normalized AVATAR definition " + step.id
        + " repeats or misnames its split proposition";
      return false;
    }
    if (choiceDependent) choiceDependentSplitDefinitions.insert(split);
  }
  for (const auto& definition : splitDefinitions) {
    result.definitions.push_back(
      {definition.first, "(PROP)", definition.second.render()});
  }

  const std::set<std::string> eliminatedSet(
    eliminated.begin(), eliminated.end());
  const auto containsEliminated = [&](const PreservedSexpr& source,
                                      const auto& self) -> bool {
    if (sexprHead(source, "TMH") && source.items.size() == 2) {
      std::string name;
      if (preservedName(source.items[1], name)
          && eliminatedSet.find(name) != eliminatedSet.end()) {
        return true;
      }
    }
    if (source.atom) return false;
    for (const auto& item : source.items) {
      if (self(item, self)) return true;
    }
    return false;
  };
  const auto containsSplitDefinition = [&](const PreservedSexpr& source,
                                           const auto& self) -> bool {
    if (sexprHead(source, "TMH") && source.items.size() == 2) {
      std::string name;
      if (preservedName(source.items[1], name)
          && name.compare(0, 6, "split_") == 0) {
        return true;
      }
    }
    if (source.atom) return false;
    for (const auto& item : source.items) {
      if (self(item, self)) return true;
    }
    return false;
  };
  std::set<std::string> affected;
  std::set<std::string> skolemIds;
  std::map<std::string, const PrimitiveStep*> skolemStepById;
  for (const PrimitiveStep& step : skolemSteps) {
    skolemIds.insert(step.id);
    skolemStepById.emplace(step.id, &step);
  }
  std::set<std::string> reusableOriginalClaims;
  for (ChoiceProofStep* wrapped : ordered) {
    const PrimitiveStep& step = wrapped->primitive;
    PreservedSexpr conclusion;
    const std::string& renderedConclusion = step.hasResultClause
      ? step.resultClause : step.resultFormula;
    if (step.hasResultClause == step.hasResultFormula
        || !parser.parse(renderedConclusion, conclusion)) {
      error = "choice-normalized proof DAG step " + step.id
        + " has no exact producer conclusion";
      return false;
    }
    const bool parentAffected = std::any_of(
      step.parentIds.begin(), step.parentIds.end(),
      [&](const std::string& parent) {
        return affected.find(parent) != affected.end();
      });
    const bool originalParentsReusable = std::all_of(
      step.parentIds.begin(), step.parentIds.end(),
      [&](const std::string& parent) {
        if (skolemIds.find(parent) != skolemIds.end()) return false;
        return byId.find(parent) == byId.end()
          || reusableOriginalClaims.find(parent) != reusableOriginalClaims.end();
      });
    if (!step.forceChoiceNormalization
        && skolemIds.find(step.id) == skolemIds.end()
        && step.producerProofClaims.empty()
        && !containsEliminated(conclusion, containsEliminated)
        && !containsSplitDefinition(conclusion, containsSplitDefinition)
        && originalParentsReusable) {
      reusableOriginalClaims.insert(step.id);
    }
    if (step.forceChoiceNormalization
        || skolemIds.find(step.id) != skolemIds.end()
        || containsEliminated(conclusion, containsEliminated)
        || parentAffected) {
      affected.insert(step.id);
    }
  }
  if (affected.find(finalStep) == affected.end()) {
    error = "choice-normalized proof DAG root is independent of its local definitions";
    return false;
  }

  // Definition users consume an explicit relation claim in the small proof
  // DAG. Retain every producer definition that supports an affected step even
  // when that definition itself contains no eliminated Skolem symbol.
  for (ChoiceProofStep* wrapped : ordered) {
    if (affected.find(wrapped->primitive.id) == affected.end()) continue;
    for (const std::string& parent : wrapped->primitive.parentIds) {
      auto found = byId.find(parent);
      if (found != byId.end()
          && !found->second->primitive.producerProofClaims.empty()) {
        affected.insert(parent);
      }
    }
  }
  // A retained definition can make an explicitly emitted, otherwise-dead
  // AVATAR component relevant.  Propagate once more in topological order so
  // those producer objects and their identity records replace the complete
  // native local-symbol slice.
  for (ChoiceProofStep* wrapped : ordered) {
    if (affected.find(wrapped->primitive.id) != affected.end()) continue;
    const bool parentAffected = std::any_of(
      wrapped->primitive.parentIds.begin(),
      wrapped->primitive.parentIds.end(),
      [&](const std::string& parent) {
        return affected.find(parent) != affected.end();
      });
    if (parentAffected) affected.insert(wrapped->primitive.id);
  }
  // Keep the replayable producer ancestry of every local-symbol step.  These
  // nodes are needed when a later finite-scope pass abstracts a ground term:
  // an otherwise ordinary copy or normalization parent may then depend on the
  // bound witness and can no longer remain an external concrete theorem.
  bool addedReplayableAncestor = true;
  while (addedReplayableAncestor) {
    addedReplayableAncestor = false;
    for (auto item = ordered.rbegin(); item != ordered.rend(); ++item) {
      const PrimitiveStep& child = (*item)->primitive;
      if (affected.find(child.id) == affected.end()) continue;
      for (const std::string& parent : child.parentIds) {
        auto found = byId.find(parent);
        if (found == byId.end()) continue;
        const PrimitiveStep& candidate = found->second->primitive;
        const bool replayable = !candidate.producerProof.empty()
          || ((candidate.rule == "formula_copy"
               || candidate.rule == "formula_term_copy")
              && candidate.parentIds.size() == 1);
        if (replayable && affected.insert(parent).second) {
          addedReplayableAncestor = true;
        }
      }
    }
  }

  const std::string normalizedPrefix = "ivy_choice_";
  const auto normalizedId = [&](const std::string& id) {
    return affected.find(id) == affected.end() ? id : normalizedPrefix + id;
  };
  std::map<std::string, std::string> definitionClaims;
  std::set<std::string> generatedClaimIds;
  for (ChoiceProofStep* wrapped : ordered) {
    const PrimitiveStep& step = wrapped->primitive;
    if (affected.find(step.id) == affected.end()) continue;
    for (const auto& claim : step.producerProofClaims) {
      const std::string claimId = normalizedPrefix + claim.id;
      if (claim.id.empty()
          || claim.resultFormula.empty() == claim.resultClause.empty()
          || claim.producerProof.empty()
          || !generatedClaimIds.insert(claimId).second
          || byId.find(claim.id) != byId.end()) {
        error = "choice-normalized proof DAG step " + step.id
          + " has an invalid producer support claim";
        return false;
      }
      if (!claim.replacesDefinition.empty()
          && !definitionClaims.emplace(
                claim.replacesDefinition, claimId).second) {
        error = "choice-normalized proof DAG has duplicate producer definition claims";
        return false;
      }
    }
  }
  const auto normalize = [&](PreservedSexpr source,
                             const std::map<std::string, std::string>& supportClaims,
                             bool compressDefinitions,
                             const auto& self) -> PreservedSexpr {
    if (sexprHead(source, "TMH") && source.items.size() == 2) {
      std::string name;
      if (preservedName(source.items[1], name)) {
        if (choiceDependentSplitDefinitions.find(name)
              != choiceDependentSplitDefinitions.end()) {
          return self(
            splitDefinitions.at(name), supportClaims,
            compressDefinitions, self);
        }
        auto replacement = replacements.find(name);
        if (replacement != replacements.end()) return replacement->second;
      }
    }
    if (sexprHead(source, "parent") && source.items.size() == 2) {
      std::string parent;
      if (preservedName(source.items[1], parent)) {
        auto support = supportClaims.find(parent);
        if (support != supportClaims.end()) {
          PreservedSexpr redirected;
          parser.parse(
            "(parent " + quotePreservedName(support->second) + ")",
            redirected);
          return redirected;
        }
        auto splitIdentity = splitDependencyByOwner.find(parent);
        if (affected.find(parent) == affected.end()
            && splitIdentity != splitDependencyByOwner.end()) {
          PreservedSexpr redirected;
          parser.parse(
            "(parent " + quotePreservedName(splitIdentity->second) + ")",
            redirected);
          return redirected;
        }
        if (affected.find(parent) != affected.end()) {
          PreservedSexpr redirected;
          parser.parse(
            "(parent " + quotePreservedName(normalizedId(parent)) + ")",
            redirected);
          return redirected;
        }
      }
    }
    if (sexprHead(source, "definition") && source.items.size() == 2) {
      std::string definition;
      if (preservedName(source.items[1], definition)) {
        auto found = definitionClaims.find(definition);
        if (found != definitionClaims.end()) {
          PreservedSexpr redirected;
          parser.parse(
            "(parent " + quotePreservedName(found->second) + ")",
            redirected);
          return redirected;
        }
      }
    }
    if (source.atom) return source;
    for (std::size_t index = 1; index < source.items.size(); ++index) {
      source.items[index] = self(
        std::move(source.items[index]),
        supportClaims,
        compressDefinitions,
        self);
    }
    if (compressDefinitions) {
      for (const auto& definition : splitDefinitions) {
        if (choiceDependentSplitDefinitions.find(definition.first)
              == choiceDependentSplitDefinitions.end()
            && source == definition.second) {
          return quotedTmh(quotePreservedName(definition.first));
        }
      }
    }
    return source;
  };

  const auto proofParents = [&](const PreservedSexpr& source,
                                std::set<std::string>& parents,
                                const auto& self) -> void {
    if (sexprHead(source, "parent") && source.items.size() == 2) {
      std::string parent;
      if (preservedName(source.items[1], parent)) parents.insert(parent);
      return;
    }
    if (source.atom) return;
    for (const auto& item : source.items) self(item, parents, self);
  };
  const auto proofInstantiation = [&](const PreservedSexpr& source,
                                      std::string& parent,
                                      std::vector<std::string>& arguments) {
    const PreservedSexpr* current = &source;
    while (sexprHead(*current, "term_apply")
           && current->items.size() == 3) {
      const PreservedSexpr& argument = current->items[2];
      if (!sexprHead(argument, "term") || argument.items.size() != 2) {
        return false;
      }
      arguments.push_back(argument.render());
      current = &current->items[1];
    }
    if (arguments.empty()
        || !sexprHead(*current, "parent")
        || current->items.size() != 2
        || !preservedName(current->items[1], parent)) {
      return false;
    }
    std::reverse(arguments.begin(), arguments.end());
    return true;
  };

  for (ChoiceProofStep* wrapped : ordered) {
    PrimitiveStep& step = wrapped->primitive;
    if (affected.find(step.id) == affected.end()) continue;
    if (!wrapped->hasParameterContract) {
      error = "choice-normalized proof DAG step " + step.id
        + " lacks a producer variable contract";
      return false;
    }
    std::map<std::string, std::string> supportClaims;
    for (const auto& claim : step.producerProofClaims) {
      if (!claim.replacesParent.empty()
          && !supportClaims.emplace(
                claim.replacesParent, normalizedPrefix + claim.id).second) {
        error = "choice-normalized proof DAG step " + step.id
          + " has duplicate local support claims";
        return false;
      }
    }
    for (const auto& claim : step.producerProofClaims) {
      PreservedSexpr claimProof;
      PreservedSexpr claimConclusion;
      const std::string& renderedClaimConclusion =
        claim.resultClause.empty() ? claim.resultFormula : claim.resultClause;
      const bool compactClaim =
        claim.ivyJustification.rule != IvyRule::None;
      if (!parser.parse(renderedClaimConclusion, claimConclusion)
          || (!compactClaim
              && !parser.parse(claim.producerProof, claimProof))) {
        error = "choice-normalized proof DAG step " + step.id
          + " has an unreadable producer support claim";
        return false;
      }
      const bool quotientDefinition = !claim.replacesDefinition.empty();
      if (!compactClaim) {
        claimProof = normalize(
          std::move(claimProof), supportClaims, quotientDefinition, normalize);
      }
      claimConclusion = normalize(
        std::move(claimConclusion), supportClaims, false, normalize);
      if ((!compactClaim
           && containsEliminated(claimProof, containsEliminated))
          || containsEliminated(claimConclusion, containsEliminated)) {
        error = "choice-normalized proof DAG support claim " + claim.id
          + " retains a certificate-local Skolem symbol";
        return false;
      }
      MegalodonKernelSyntax::RenderedKernelChoiceProofNode claimNode;
      claimNode.index = result.nodes.size();
      claimNode.step = normalizedPrefix + claim.id;
      claimNode.parameters = claim.hasParameterContract
        ? claim.parameters : wrapped->parameters;
      claimNode.hasResultFormula = !claim.resultFormula.empty();
      claimNode.hasResultClause = !claim.resultClause.empty();
      if (claimNode.hasResultFormula) {
        claimNode.resultFormula = claimConclusion.render();
      } else {
        claimNode.resultClause = claimConclusion.render();
      }
      claimNode.ivyJustification = claim.ivyJustification;
      const auto normalizeClaimParent = [&](const std::string& parent) {
        auto support = supportClaims.find(parent);
        if (support != supportClaims.end()) return support->second;
        auto splitIdentity = splitDependencyByOwner.find(parent);
        if (affected.find(parent) == affected.end()
            && splitIdentity != splitDependencyByOwner.end()) {
          return splitIdentity->second;
        }
        return normalizedId(parent);
      };
      if (claimNode.ivyJustification.rule != IvyRule::None) {
        for (std::string& parent : claimNode.ivyJustification.parents) {
          parent = normalizeClaimParent(parent);
        }
        claimNode.parents = claimNode.ivyJustification.parents;
        std::sort(claimNode.parents.begin(), claimNode.parents.end());
        claimNode.parents.erase(
          std::unique(claimNode.parents.begin(), claimNode.parents.end()),
          claimNode.parents.end());
      } else {
        claimNode.producerProof = claimProof.render();
        std::set<std::string> referencedParents;
        proofParents(claimProof, referencedParents, proofParents);
        claimNode.parents.assign(
          referencedParents.begin(), referencedParents.end());
      }
      result.nodes.push_back(std::move(claimNode));
    }
    std::string synthesizedProofText;
    const std::string* proofText = &step.producerProof;
    if (proofText->empty()
        && (step.rule == "formula_copy"
            || step.rule == "formula_term_copy")
        && step.parentIds.size() == 1) {
      synthesizedProofText =
        "(parent " + quotePreservedName(step.parentIds.front()) + ")";
      for (const auto& parameter : wrapped->parameters) {
        synthesizedProofText = "(term_apply " + synthesizedProofText
          + " (term (TMH " + quotePreservedName(parameter.first) + ")))";
      }
      proofText = &synthesizedProofText;
    }
    PreservedSexpr proof;
    PreservedSexpr conclusion;
    const std::string& renderedConclusion = step.hasResultClause
      ? step.resultClause : step.resultFormula;
    if (proofText->empty() || !parser.parse(*proofText, proof)
        || !parser.parse(renderedConclusion, conclusion)) {
      error = "choice-normalized proof DAG step " + step.id
        + " has no direct producer proof";
      return false;
    }
    proof = normalize(std::move(proof), supportClaims, false, normalize);
    conclusion = normalize(
      std::move(conclusion), supportClaims, false, normalize);
    if (containsEliminated(proof, containsEliminated)
        || containsEliminated(conclusion, containsEliminated)) {
      error = "choice-normalized proof DAG step " + step.id
        + " retains a certificate-local Skolem symbol";
      return false;
    }
    MegalodonKernelSyntax::RenderedKernelChoiceProofNode node;
    node.index = result.nodes.size();
    node.step = normalizedId(step.id);
    node.producerProofParentAliases.assign(
      supportClaims.begin(), supportClaims.end());
    node.producerProofDefinitionAliases.assign(
      definitionClaims.begin(), definitionClaims.end());
    std::set<std::string> referencedParents;
    proofParents(proof, referencedParents, proofParents);
    node.parents.assign(referencedParents.begin(), referencedParents.end());
    node.parameters = wrapped->parameters;
    node.hasResultClause = step.hasResultClause;
    node.hasResultFormula = step.hasResultFormula;
    node.producerShareAcrossGroundInstances =
      reusableOriginalClaims.find(step.id) != reusableOriginalClaims.end()
      && !containsSplitDefinition(conclusion, containsSplitDefinition)
      && !containsSplitDefinition(proof, containsSplitDefinition);
    if (step.hasResultClause) node.resultClause = conclusion.render();
    if (step.hasResultFormula) node.resultFormula = conclusion.render();
    // Compact Ivy nodes carry only their small rule payload.  Direct proof
    // terms are retained below solely for nodes without a compact rule (and
    // for exact CNF scope boundaries, which require the direct transformer).
    if (step.producerCnfProjection != nullptr
        && !step.producerCnfSourceFormula.empty()) {
      PreservedSexpr cnfSource;
      if (!parser.parse(step.producerCnfSourceFormula, cnfSource)) {
        error = "choice-normalized CNF source is unreadable at " + step.id;
        return false;
      }
      cnfSource = normalize(
        std::move(cnfSource), supportClaims, false, normalize);
      auto projection = std::make_shared<
        MegalodonKernelSyntax::RenderedKernelCnfProjection>(
          *step.producerCnfProjection);
      std::function<bool(
        MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
        normalizeProjection;
      normalizeProjection = [&](auto& item) {
      const auto normalizeField = [&](auto& field, bool compressDefinitions) {
          PreservedSexpr value;
          if (!parser.parse(field.sexpr, value)) return false;
          value = normalize(
            std::move(value), supportClaims, compressDefinitions, normalize);
          if (containsEliminated(value, containsEliminated)) return false;
          field.sexpr = value.render();
          return true;
        };
        if (item.hasWitnessTerm
            && !normalizeField(item.witnessTerm, false)) {
          return false;
        }
        if (item.hasSourceLiteral
            && !normalizeField(item.sourceLiteral, false)) {
          return false;
        }
        for (auto& child : item.children) {
          if (!normalizeProjection(child)) return false;
        }
        return true;
      };
      if (containsEliminated(cnfSource, containsEliminated)
          || !normalizeProjection(*projection)) {
        error = "choice-normalized CNF projection retains a local symbol at "
          + step.id;
        return false;
      }
      node.producerCnfProjection = std::move(projection);
      node.producerCnfSourceFormula = cnfSource.render();
    }
    const auto normalizedParent = [&](const std::string& parent) {
      auto support = supportClaims.find(parent);
      if (support != supportClaims.end()) return support->second;
      auto splitIdentity = splitDependencyByOwner.find(parent);
      if (affected.find(parent) == affected.end()
          && splitIdentity != splitDependencyByOwner.end()) {
        return splitIdentity->second;
      }
      return normalizedId(parent);
    };
    const auto indexField = [&](const std::string& name,
                                std::size_t& value) {
      auto found = std::find_if(
        step.fields.begin(), step.fields.end(),
        [&](const auto& item) { return item.first == name; });
      if (found == step.fields.end() || found->second.empty()) return false;
      char* end = nullptr;
      const unsigned long parsed = std::strtoul(
        found->second.c_str(), &end, 10);
      if (end == nullptr || *end != '\0') return false;
      value = static_cast<std::size_t>(parsed);
      return true;
    };
    const auto textField = [&](const std::string& name,
                               std::string& value) {
      auto found = std::find_if(
        step.fields.begin(), step.fields.end(),
        [&](const auto& item) { return item.first == name; });
      if (found == step.fields.end() || found->second.empty()) return false;
      value = found->second;
      return true;
    };
    const auto normalizedSexprField = [&](const std::string& name,
                                          std::string& value) {
      std::string source;
      PreservedSexpr parsed;
      if (!textField(name, source) || !parser.parse(source, parsed)) {
        return false;
      }
      parsed = normalize(
        std::move(parsed), supportClaims, false, normalize);
      if (containsEliminated(parsed, containsEliminated)) return false;
      value = parsed.render();
      return true;
    };
    const auto identityArguments = [&](const std::string& parent,
                                       std::vector<std::string>& arguments) {
      auto found = byId.find(parent);
      if (found == byId.end()) return false;
      for (const auto& parameter : found->second->parameters) {
        if (std::find(
              wrapped->parameters.begin(), wrapped->parameters.end(),
              parameter) == wrapped->parameters.end()) {
          return false;
        }
        arguments.push_back(
          "(term (TMH " + quotePreservedName(parameter.first) + "))");
      }
      return true;
    };
    const auto renderedNode = [&](const std::string& id) -> const ChoiceNode* {
      auto found = std::find_if(
        result.nodes.begin(), result.nodes.end(),
        [&](const ChoiceNode& candidate) { return candidate.step == id; });
      return found == result.nodes.end() ? nullptr : &*found;
    };
    const auto exactResolutionArguments = [&]
      (const std::string& leftParent,
       std::vector<std::string>& leftArguments,
       std::size_t leftPivot,
       const std::string& rightParent,
       std::vector<std::string>& rightArguments,
       std::size_t rightPivot) {
      const ChoiceNode* left = renderedNode(leftParent);
      const ChoiceNode* right = renderedNode(rightParent);
      return left != nullptr
        && right != nullptr
        && refineResolutionArguments(
             *left, leftArguments, leftPivot,
             *right, rightArguments, rightPivot,
             wrapped->parameters);
    };
    const auto parentClauseNormalizationStable = [&](const std::string& parent) {
      if (affected.find(parent) != affected.end()
          || supportClaims.find(parent) != supportClaims.end()) {
        return true;
      }
      auto found = byId.find(parent);
      if (found == byId.end() || !found->second->primitive.hasResultClause) {
        return false;
      }
      PreservedSexpr original;
      if (!parser.parse(found->second->primitive.resultClause, original)) {
        return false;
      }
      return normalize(original, supportClaims, false, normalize).render()
        == original.render();
    };
    std::string instantiatedParent;
    std::vector<std::string> instantiationArguments;
    if (referencedParents.size() == 1
        && sexprHead(proof, "parent")
        && proof.items.size() == 2) {
      node.ivyJustification.rule = IvyRule::Copy;
      node.ivyJustification.parents.assign(
        referencedParents.begin(), referencedParents.end());
    } else if (referencedParents.size() == 1
               && proofInstantiation(
                    proof, instantiatedParent, instantiationArguments)
               && referencedParents.count(instantiatedParent) == 1) {
      node.ivyJustification.rule = IvyRule::Instantiate;
      node.ivyJustification.parents = {instantiatedParent};
      node.ivyJustification.terms = std::move(instantiationArguments);
    } else if (step.rule == "resolve"
               && step.hasResultClause
               && step.parentIds.size() == 2) {
      const std::vector<std::string> parents{
        normalizedParent(step.parentIds[0]),
        normalizedParent(step.parentIds[1]),
      };
      std::size_t leftPivot = 0;
      std::size_t rightPivot = 0;
      std::vector<std::string> leftArguments;
      std::vector<std::string> rightArguments;
      std::set<std::string> expectedParents(parents.begin(), parents.end());
      if (parentClauseNormalizationStable(step.parentIds[0])
          && parentClauseNormalizationStable(step.parentIds[1])
          && identityArguments(step.parentIds[0], leftArguments)
          && identityArguments(step.parentIds[1], rightArguments)
          && expectedParents == referencedParents
          && indexField("pivot_left", leftPivot)
          && indexField("pivot_right", rightPivot)
          && exactResolutionArguments(
               parents[0], leftArguments, leftPivot,
               parents[1], rightArguments, rightPivot)) {
        node.ivyJustification.rule = IvyRule::Resolve;
        node.ivyJustification.parents = parents;
        node.ivyJustification.indices = {leftPivot, rightPivot};
        node.ivyJustification.parentArguments = {
          std::move(leftArguments), std::move(rightArguments),
        };
      } else {
        node.producerProof = proof.render();
      }
    } else if (step.rule == "factor"
               && step.hasResultClause
               && step.parentIds.size() == 1) {
      const std::string parent = normalizedParent(step.parentIds.front());
      auto parentStep = byId.find(step.parentIds.front());
      std::size_t leftLiteral = 0;
      std::size_t rightLiteral = 0;
      if (parentStep != byId.end()
          && parentStep->second->parameters == wrapped->parameters
          && parentClauseNormalizationStable(step.parentIds.front())
          && referencedParents == std::set<std::string>{parent}
          && indexField("literal_left", leftLiteral)
          && indexField("literal_right", rightLiteral)) {
        node.ivyJustification.rule = IvyRule::Factor;
        node.ivyJustification.parents = {parent};
        node.ivyJustification.indices = {leftLiteral, rightLiteral};
        for (const auto& parameter : wrapped->parameters) {
          node.ivyJustification.terms.push_back(
            "(term (TMH " + quotePreservedName(parameter.first) + "))");
        }
      } else {
        node.producerProof = proof.render();
      }
    } else if ((step.rule == "equality_resolution"
                || step.rule == "equality_symmetry")
               && step.hasResultClause
               && step.parentIds.size() == 1) {
      const std::string parent = normalizedParent(step.parentIds.front());
      std::vector<std::string> arguments;
      std::size_t literal = 0;
      if (referencedParents == std::set<std::string>{parent}
          && parentClauseNormalizationStable(step.parentIds.front())
          && identityArguments(step.parentIds.front(), arguments)
          && indexField("literal", literal)) {
        node.ivyJustification.rule = step.rule == "equality_resolution"
          ? IvyRule::EqualityResolution : IvyRule::EqualitySymmetry;
        node.ivyJustification.parents = {parent};
        node.ivyJustification.indices = {literal};
        node.ivyJustification.terms = std::move(arguments);
      } else {
        node.producerProof = proof.render();
      }
    } else if (step.rule == "truth_conflict"
               && step.hasResultClause
               && step.parentIds.size() == 1) {
      const std::string parent = normalizedParent(step.parentIds.front());
      std::vector<std::string> arguments;
      std::size_t literal = 0;
      if (referencedParents == std::set<std::string>{parent}
          && parentClauseNormalizationStable(step.parentIds.front())
          && identityArguments(step.parentIds.front(), arguments)
          && indexField("literal", literal)) {
        node.ivyJustification.rule = IvyRule::TruthConflict;
        node.ivyJustification.parents = {parent};
        node.ivyJustification.indices = {literal};
        node.ivyJustification.terms = std::move(arguments);
      } else {
        node.producerProof = proof.render();
      }
    } else if (step.rule == "paramodulate"
               && step.hasResultClause
               && step.parentIds.size() == 2) {
      const std::vector<std::string> parents{
        normalizedParent(step.parentIds[0]),
        normalizedParent(step.parentIds[1]),
      };
      std::vector<std::string> equalityArguments;
      std::vector<std::string> targetArguments;
      std::size_t equalityLiteral = 0;
      std::size_t targetLiteral = 0;
      std::size_t resultLiteral = 0;
      std::string position;
      std::string from;
      std::string to;
      if (referencedParents == std::set<std::string>(parents.begin(), parents.end())
          && parentClauseNormalizationStable(step.parentIds[0])
          && parentClauseNormalizationStable(step.parentIds[1])
          && identityArguments(step.parentIds[0], equalityArguments)
          && identityArguments(step.parentIds[1], targetArguments)
          && indexField("equality_literal", equalityLiteral)
          && indexField("target_literal", targetLiteral)
          && indexField("result_literal", resultLiteral)
          && normalizedSexprField("position", position)
          && normalizedSexprField("from", from)
          && normalizedSexprField("to", to)) {
        node.ivyJustification.rule = IvyRule::Paramodulate;
        node.ivyJustification.parents = parents;
        node.ivyJustification.indices = {
          equalityLiteral, targetLiteral, resultLiteral,
        };
        node.ivyJustification.parentArguments = {
          equalityArguments, targetArguments,
        };
        node.ivyJustification.position = position;
        node.ivyJustification.from = from;
        node.ivyJustification.to = to;
      } else {
        node.producerProof = proof.render();
      }
    } else {
      node.producerProof = proof.render();
    }
    if (node.ivyJustification.rule != IvyRule::None
        && node.producerCnfProjection != nullptr) {
      node.producerProof = proof.render();
    } else if (node.ivyJustification.rule != IvyRule::None) {
      // The builder omits this field for compact Ivy nodes. Keep the original
      // term solely as lazy producer-private input for finite-scope replay;
      // the explicit alias tables above normalize its local references then.
      if (proofText == &step.producerProof) {
        node.producerProof = std::move(step.producerProof);
      } else {
        node.producerProof = *proofText;
      }
    }

    // This pass owns the detached producer slice. Once a node has been
    // lowered, retain only the transformed result and release the large
    // source proof payload before processing the rest of the DAG.
    std::string().swap(step.producerProof);
    for (auto& claim : step.producerProofClaims) {
      std::string().swap(claim.producerProof);
      std::string().swap(claim.resultFormula);
      std::string().swap(claim.resultClause);
    }

    // Lower every Skolem witness to a support existential followed by one
    // contextual target.  Both proof transformers are producer-generated Ivy
    // terms; the consumer only opens the declared root existential scope.
    auto skolem = skolemStepById.find(step.id);
    if (skolem != skolemStepById.end()
        && step.parentIds.size() == 1
        && node.hasResultFormula) {
      const auto& definitions =
        skolem->second->producerSkolemChoiceDefinitions;
      std::vector<MegalodonKernelSyntax::RenderedKernelChoiceProofNode> stages;
      std::string stageParent = normalizedParent(step.parentIds.front());
      std::string previousTarget;
      bool exactStages = !definitions.empty();
      std::string stageFailure = exactStages ? "" : "no witness definitions";
      const auto applyTransform = [&](const PreservedSexpr& transform,
                                      const std::string& parent,
                                      PreservedSexpr& applied) {
        std::string inputName;
        if (!sexprHead(transform, "proof_lambda")
            || transform.items.size() != 4
            || !preservedName(transform.items[1], inputName)) {
          return false;
        }
        PreservedSexpr parentProof;
        if (!parser.parse(
              "(parent " + quotePreservedName(parent) + ")",
              parentProof)) {
          return false;
        }
        for (const auto& parameter : wrapped->parameters) {
          PreservedSexpr next;
          if (!parser.parse(
                "(term_apply " + parentProof.render()
                  + " (term (TMH "
                  + quotePreservedName(parameter.first) + ")))",
                next)) {
            return false;
          }
          parentProof = std::move(next);
        }
        const auto substituteInput = [&](const PreservedSexpr& source,
                                         const auto& self) -> PreservedSexpr {
          std::string hypothesisName;
          if (sexprHead(source, "hyp") && source.items.size() == 2
              && preservedName(source.items[1], hypothesisName)
              && hypothesisName == inputName) {
            return parentProof;
          }
          if (sexprHead(source, "proof_lambda")
              && source.items.size() == 4
              && preservedName(source.items[1], hypothesisName)
              && hypothesisName == inputName) {
            return source;
          }
          if (source.atom) return source;
          PreservedSexpr result;
          result.atom = false;
          result.items.reserve(source.items.size());
          if (!source.items.empty()) {
            result.items.push_back(source.items.front());
          }
          for (std::size_t child = 1;
               child < source.items.size();
               ++child) {
            result.items.push_back(self(source.items[child], self));
          }
          return result;
        };
        applied = substituteInput(transform.items[3], substituteInput);
        return true;
      };
      for (std::size_t index = 0;
           exactStages && index < definitions.size();
           ++index) {
        const auto& definition = definitions[index];
        PreservedSexpr contextSource;
        PreservedSexpr contextTarget;
        PreservedSexpr contextTransform;
        PreservedSexpr scopeParent;
        PreservedSexpr scopeParentTransform;
        PreservedSexpr witness;
        PreservedSexpr scopeSource;
        PreservedSexpr scopeTarget;
        PreservedSexpr scopeBridge;
        exactStages =
          !definition.contextSourceFormulaSexpr.empty()
          && !definition.contextTargetFormulaSexpr.empty()
          && !definition.contextTransformProof.empty()
          && !definition.scopeParentFormulaSexpr.empty()
          && !definition.scopeParentTransformProof.empty()
          && !definition.witnessTermSexpr.empty()
          && !definition.contextScopeSourceFormulaSexpr.empty()
          && !definition.contextScopeTargetFormulaSexpr.empty()
          && !definition.contextScopeBridgeProof.empty()
          && parser.parse(
               definition.contextSourceFormulaSexpr, contextSource)
          && parser.parse(
               definition.contextTargetFormulaSexpr, contextTarget)
          && parser.parse(definition.contextTransformProof, contextTransform)
          && parser.parse(definition.scopeParentFormulaSexpr, scopeParent)
          && parser.parse(
               definition.scopeParentTransformProof, scopeParentTransform)
          && parser.parse(definition.witnessTermSexpr, witness)
          && parser.parse(
               definition.contextScopeSourceFormulaSexpr, scopeSource)
          && parser.parse(
               definition.contextScopeTargetFormulaSexpr, scopeTarget)
          && parser.parse(
               definition.contextScopeBridgeProof, scopeBridge);
        if (!exactStages) {
          stageFailure = "incomplete or unreadable witness stage";
          break;
        }
        contextSource = normalize(
          std::move(contextSource), supportClaims, false, normalize);
        contextTarget = normalize(
          std::move(contextTarget), supportClaims, false, normalize);
        contextTransform = normalize(
          std::move(contextTransform), supportClaims, false, normalize);
        scopeParent = normalize(
          std::move(scopeParent), supportClaims, false, normalize);
        scopeParentTransform = normalize(
          std::move(scopeParentTransform), supportClaims, false, normalize);
        witness = normalize(
          std::move(witness), supportClaims, false, normalize);
        scopeSource = normalize(
          std::move(scopeSource), supportClaims, false, normalize);
        scopeTarget = normalize(
          std::move(scopeTarget), supportClaims, false, normalize);
        scopeBridge = normalize(
          std::move(scopeBridge), supportClaims, false, normalize);
        if (index != 0 && contextSource.render() != previousTarget) {
          stageFailure = "adjacent witness stages do not compose";
          exactStages = false;
          break;
        }
        if (containsEliminated(contextSource, containsEliminated)
            || containsEliminated(contextTarget, containsEliminated)
            || containsEliminated(contextTransform, containsEliminated)
            || containsEliminated(scopeParent, containsEliminated)
            || containsEliminated(scopeParentTransform, containsEliminated)
            || containsEliminated(witness, containsEliminated)
            || containsEliminated(scopeSource, containsEliminated)
            || containsEliminated(scopeTarget, containsEliminated)
            || containsEliminated(scopeBridge, containsEliminated)) {
          stageFailure = "normalized witness stage retains a local symbol";
          exactStages = false;
          break;
        }
        MegalodonKernelSyntax::RenderedKernelChoiceProofNode support;
        support.index = result.nodes.size() + stages.size();
        support.step = normalizedPrefix + step.id + "_skolem_support_"
          + std::to_string(index);
        support.parents = {stageParent};
        support.parameters = wrapped->parameters;
        support.hasResultFormula = true;
        support.resultFormula = scopeParent.render();
        PreservedSexpr supportProof;
        if (!applyTransform(
              scopeParentTransform, stageParent, supportProof)) {
          stageFailure = "cannot assemble existential support application";
          exactStages = false;
          break;
        }
        support.producerProof = supportProof.render();
        const std::string supportStep = support.step;
        stages.push_back(std::move(support));

        MegalodonKernelSyntax::RenderedKernelChoiceProofNode stage;
        stage.index = result.nodes.size() + stages.size();
        stage.step = index + 1 == definitions.size()
          ? normalizedId(step.id)
          : normalizedPrefix + step.id + "_skolem_stage_"
              + std::to_string(index);
        stage.parents = {stageParent};
        stage.parameters = wrapped->parameters;
        stage.hasResultFormula = true;
        stage.resultFormula = contextTarget.render();
        PreservedSexpr stageProof;
        if (!applyTransform(contextTransform, stageParent, stageProof)) {
          stageFailure = "cannot assemble stage application";
          exactStages = false;
          break;
        }
        stage.producerProof = stageProof.render();
        stage.hasRootExistsScope = true;
        stage.rootExistsScopeParent = supportStep;
        stage.rootExistsScopeWitnessType = definition.witnessTypeSexpr;
        stage.rootExistsScopeWitnessTerm = witness.render();
        stage.rootExistsScopeSourceFormula = scopeSource.render();
        stage.rootExistsScopeTargetFormula = scopeTarget.render();
        stage.rootExistsScopeBridgeProof = scopeBridge.render();
        stage.rootExistsScopeBranchIndex = definition.branchIndex;
        stage.rootExistsScopeWitnessIndex = definition.witnessIndex;
        stage.rootExistsScopePath = definition.scopePath;
        stage.rootExistsScopeAmbient = definition.scopeAmbient;
        previousTarget = contextTarget.render();
        stageParent = stage.step;
        stages.push_back(std::move(stage));
      }
      if (exactStages && previousTarget == conclusion.render()) {
        for (auto& stage : stages) result.nodes.push_back(std::move(stage));
        continue;
      }
      if (exactStages) stageFailure = "final witness stage is contextual";
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << "megalodon root stage lowering skipped " << step.id
                  << " (" << definitions.size() << " witnesses): "
                  << stageFailure << std::endl;
      }
    }

    result.nodes.push_back(std::move(node));
  }
  if (result.nodes.empty()
      || result.nodes.back().step != normalizedId(finalStep)) {
    error = "choice-normalized proof DAG does not end at its declared root";
    return false;
  }
  const bool hasRootExistsScope = std::any_of(
    result.nodes.begin(), result.nodes.end(),
    [](const auto& node) { return node.hasRootExistsScope; });
  result.version = result.definitions.empty()
    ? (hasRootExistsScope ? "ivy_choice_dag_v2" : "ivy_choice_dag_v1")
    : "ivy_choice_dag_v3";
  result.finalStep = normalizedId(finalStep);
  for (const auto& replacement : replacements) {
    result.producerGroundSubstitutions.push_back({
      replacement.first,
      replacement.second.render(),
    });
  }
  for (const std::string& split : choiceDependentSplitDefinitions) {
    result.producerGroundSubstitutions.push_back({
      split,
      splitDefinitions.at(split).render(),
    });
  }
  result.eliminatedSymbols = std::move(eliminated);
  return true;
}

bool expandFiniteSkolemProof(
  MegalodonKernelSyntax::RenderedKernelFiniteSkolemProof& proof,
  std::string& error)
{
  PreservedSexprParser parser;
  if (proof.version == "ivy_atomic_choice_v1") {
    if (proof.finalStep.value.empty()
        || !proof.applications.empty()
        || !proof.dischargeOrder.empty()) {
      error = "atomic choice replay received a malformed producer plan";
      return false;
    }
    return true;
  }
  if (proof.version != "smolka_finite_v7"
      || proof.applications.empty()
      || proof.dischargeOrder.size() != proof.applications.size()) {
    error = "finite Skolem prooftrans received an incomplete typed plan";
    return false;
  }
  for (std::size_t expected = 0; expected < proof.applications.size(); ++expected) {
    auto& application = proof.applications[expected];
    const auto& definition = application.producerChoiceDefinition;
    if (application.index != expected
        || definition.branchIndex != application.branchIndex
        || definition.witnessIndex != application.witnessIndex
        || definition.symbol != application.symbol
        || definition.witnessTypeSexpr != application.witnessTypeSexpr
        || definition.parameters.size() != application.dependencies.size()) {
      error = "finite Skolem application disagrees with its producer witness program";
      return false;
    }
    std::map<std::string, PreservedSexpr> bindings;
    for (const auto& dependency : application.dependencies) {
      PreservedSexpr term;
      if (dependency.variable.empty()
          || !parser.parse(dependency.term.sexpr, term)
          || !bindings.emplace(dependency.variable, std::move(term)).second) {
        error = "finite Skolem application has an invalid dependency substitution";
        return false;
      }
    }
    for (const auto& parameter : definition.parameters) {
      if (bindings.find(parameter.first) == bindings.end()) {
        error = "finite Skolem witness program has an undeclared dependency parameter";
        return false;
      }
    }
    const auto specialize = [&](const std::string& source,
                                PreservedSexpr& result) {
      if (source.empty() || !parser.parse(source, result)) return false;
      for (const auto& binding : bindings) {
        result = substituteNamedVariableSexpr(
          result, binding.first, binding.second);
      }
      return true;
    };
    PreservedSexpr witness;
    PreservedSexpr stageSource;
    PreservedSexpr stageTarget;
    PreservedSexpr source;
    PreservedSexpr target;
    PreservedSexpr support;
    PreservedSexpr supportProof;
    PreservedSexpr scopeSource;
    PreservedSexpr scopeTarget;
    PreservedSexpr scopeBridge;
    const auto fieldError = [&](const std::string& field) {
      error = "finite Skolem application " + std::to_string(application.index)
        + " cannot specialize producer " + field;
      return false;
    };
    if (!specialize(definition.witnessTermSexpr, witness)) {
      return fieldError("witness term");
    }
    if (witness.render() != application.term.sexpr) {
      error = "finite Skolem application " + std::to_string(application.index)
        + " producer witness term differs from its canonical application";
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << error << "\n  witness: " << witness.render()
                  << "\n  application: " << application.term.sexpr << std::endl;
      }
      return false;
    }
    if (!specialize(definition.sourceFormulaSexpr, stageSource)) {
      return fieldError("stage source");
    }
    if (!specialize(definition.scopeTargetFormulaSexpr, stageTarget)) {
      return fieldError("stage target");
    }
    PreservedSexpr applicationStageSource;
    PreservedSexpr applicationStageTarget;
    if (!parser.parse(
          application.stageSourceInstance.sexpr, applicationStageSource)
        || !parser.parse(
          application.stageTargetInstance.sexpr, applicationStageTarget)) {
      error = "finite Skolem application has malformed recorded stage formulas";
      return false;
    }
    const auto orientationTransform = [&]
      (const PreservedSexpr& from,
       const PreservedSexpr& to,
       const std::string& suffix,
       std::string& transform) {
      MegalodonKernelSyntax::RenderedKernelFoolProgram program;
      std::size_t nextIndex = 0;
      if (!buildFoolProgramNode(from, to, true, {}, nextIndex, program.root)) {
        return false;
      }
      const std::string input =
        "ivy_sm_finite_" + std::to_string(application.index) + "_" + suffix;
      IvyClauseProofBuilder builder;
      std::string body;
      if (!builder.foolFormulaProof(
            program,
            "(hyp " + quotePreservedName(input) + ")",
            body)) {
        return false;
      }
      transform = "(proof_lambda " + quotePreservedName(input)
        + " (formula " + from.render() + ") " + body + ")";
      return true;
    };
    if (!orientationTransform(
          stageSource, applicationStageSource,
          "source_to_application", application.programStageSourceToApplicationProof)
        || !orientationTransform(
          applicationStageSource, stageSource,
          "source_to_program", application.applicationStageSourceToProgramProof)
        || !orientationTransform(
          stageTarget, applicationStageTarget,
          "target_to_application", application.programStageTargetToApplicationProof)
        || !orientationTransform(
          applicationStageTarget, stageTarget,
          "target_to_program", application.applicationStageTargetToProgramProof)) {
      error = "finite Skolem application " + std::to_string(application.index)
        + " cannot lower its exact producer equality-orientation bridge";
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << error
                  << "\n  program source: " << stageSource.render()
                  << "\n  application source: " << applicationStageSource.render()
                  << "\n  program target: " << stageTarget.render()
                  << "\n  application target: " << applicationStageTarget.render()
                  << std::endl;
      }
      return false;
    }
    if (!specialize(definition.contextSourceFormulaSexpr, source)) {
      return fieldError("context source");
    }
    if (!specialize(definition.contextTargetFormulaSexpr, target)) {
      return fieldError("context target");
    }
    if (!specialize(definition.scopeParentFormulaSexpr, support)) {
      return fieldError("support formula");
    }
    if (!specialize(definition.scopeParentTransformProof, supportProof)) {
      return fieldError("support proof");
    }
    if (!specialize(definition.contextScopeSourceFormulaSexpr, scopeSource)) {
      return fieldError("scope source");
    }
    if (!specialize(definition.contextScopeTargetFormulaSexpr, scopeTarget)) {
      return fieldError("scope target");
    }
    if (!specialize(definition.contextScopeBridgeProof, scopeBridge)) {
      return fieldError("scope bridge proof");
    }
    if (source.render().empty() || support.render().empty()
        || supportProof.render().empty() || scopeSource.render().empty()
        || scopeTarget.render().empty() || scopeBridge.render().empty()) {
      error = "finite Skolem application has an empty specialized producer program";
      return false;
    }
    application.hasProducerProgram = true;
    application.programStageSourceFormula =
      MegalodonKernelSyntax::formula(stageSource.render());
    application.programStageTargetFormula =
      MegalodonKernelSyntax::formula(stageTarget.render());
    application.programSourceFormula =
      MegalodonKernelSyntax::formula(source.render());
    application.programTargetFormula =
      MegalodonKernelSyntax::formula(target.render());
    application.programSupportFormula =
      MegalodonKernelSyntax::formula(support.render());
    application.programSupportProof = supportProof.render();
    application.programScopeSourceFormula =
      MegalodonKernelSyntax::formula(scopeSource.render());
    application.programScopeTargetFormula =
      MegalodonKernelSyntax::formula(scopeTarget.render());
    application.programScopeBridgeProof = scopeBridge.render();
  }
  return true;
}

struct UniformSkolemScopeExpansion {
  PreservedSexpr body;
  PreservedSexpr theorem;
  PreservedSexpr proof;
};

bool expandUniformSkolemScope(
  const std::string& id,
  const PreservedSexpr& witnessType,
  const PreservedSexpr& needle,
  const PreservedSexpr& leafSource,
  const std::vector<std::size_t>& path,
  const PreservedSexpr& source,
  const PreservedSexpr& target,
  const PreservedSexpr& sourceProof,
  UniformSkolemScopeExpansion& expansion,
  std::string& error)
{
  PreservedSexprParser parser;
  std::size_t nextName = 0;
  const auto fresh = [&](const char* stem) {
    return "ivy_uniform_" + id + "_" + stem
      + std::to_string(nextName++);
  };
  const auto formula = [](const std::string& value) {
    return "(formula " + value + ")";
  };
  const auto term = [](const std::string& value) {
    return "(term " + value + ")";
  };
  const auto tmh = [](const std::string& name) {
    return "(TMH " + quotePreservedName(name) + ")";
  };
  const auto hypothesis = [](const std::string& name) {
    return "(hyp " + quotePreservedName(name) + ")";
  };
  const auto proofApply = [](const std::string& left,
                             const std::string& right) {
    return "(proof_apply " + left + " " + right + ")";
  };
  const auto termApply = [](const std::string& proof,
                            const std::string& argument) {
    return "(term_apply " + proof + " " + argument + ")";
  };
  const auto proofLambda = [&](const std::string& name,
                               const std::string& proposition,
                               const std::string& body) {
    return "(proof_lambda " + quotePreservedName(name) + " "
      + formula(proposition) + " " + body + ")";
  };
  const auto termLambda = [](const std::string& name,
                             const std::string& type,
                             const std::string& body) {
    return "(term_lambda " + quotePreservedName(name) + " "
      + type + " " + body + ")";
  };
  const auto implication = [](const std::string& left,
                              const std::string& right) {
    return "(IMP " + left + " " + right + ")";
  };
  const auto forall = [](const std::string& name,
                         const std::string& type,
                         const std::string& body) {
    return "(ALLV " + quotePreservedName(name) + " "
      + type + " " + body + ")";
  };
  const auto exists = [&](const std::string& name,
                          const std::string& body) {
    return "(AP (TMH \"vampire_exists_prop\") (VLAMV "
      + quotePreservedName(name) + " " + witnessType.render()
      + " " + body + "))";
  };
  const std::string witnessName = fresh("witness_");
  PreservedSexpr witnessVariable;
  if (!parser.parse(tmh(witnessName), witnessVariable)) return false;
  std::size_t replacements = 0;
  std::function<bool(
    const PreservedSexpr&, std::size_t, bool, PreservedSexpr&)>
    abstractScoped;
  abstractScoped = [&](const PreservedSexpr& current,
                       std::size_t pathIndex,
                       bool follow,
                       PreservedSexpr& result) {
    if (follow && pathIndex == path.size() && current == needle) {
      result = witnessVariable;
      ++replacements;
      return true;
    }
    result = current;
    if (current.atom) return true;
    if (follow && pathIndex < path.size()) {
      if (sexprHead(current, "ALLV") && current.items.size() == 4) {
        if (path[pathIndex] != 0) return false;
        return abstractScoped(
          current.items[3], pathIndex + 1, true, result.items[3]);
      }
      PreservedSexpr left;
      PreservedSexpr right;
      const bool conjunction = binaryNamedApplicationSexpr(
        current, "vampire_and", left, right);
      const bool disjunction = !conjunction
        && binaryNamedApplicationSexpr(current, "vampire_or", left, right);
      if (!conjunction && !disjunction) return false;
      const std::size_t branch = path[pathIndex];
      if (branch > 1) return false;
      PreservedSexpr& child = branch == 0
        ? result.items[1].items[2] : result.items[2];
      return abstractScoped(
        branch == 0 ? left : right,
        pathIndex + 1,
        true,
        child);
    }
    for (std::size_t index = 1; index < current.items.size(); ++index) {
      if (!abstractScoped(
            current.items[index], pathIndex, follow,
            result.items[index])) {
        return false;
      }
    }
    return true;
  };
  PreservedSexpr transformed;
  if (!abstractScoped(target, 0, true, transformed)
      || replacements == 0) {
    error = "uniform Skolem scope " + id
      + " does not contain its exact recorded witness at the scoped path";
    return false;
  }

  const auto existsIntro = [&](const std::string& body,
                               const std::string& witness,
                               const std::string& bodyProof) {
    const std::string resultName = fresh("exists_result_");
    const std::string handlerName = fresh("exists_handler_");
    const std::string resultTerm = tmh(resultName);
    return termLambda(
      resultName,
      "(PROP)",
      proofLambda(
        handlerName,
        forall(
          witnessName,
          witnessType.render(),
          implication(body, resultTerm)),
        proofApply(
          termApply(hypothesis(handlerName), term(witness)),
          bodyProof)));
  };
  const auto andIntroduction = [&](const PreservedSexpr& left,
                                   const PreservedSexpr& right,
                                   const std::string& leftProof,
                                   const std::string& rightProof) {
    const std::string resultName = fresh("and_result_");
    const std::string handlerName = fresh("and_handler_");
    return termLambda(
      resultName,
      "(PROP)",
      proofLambda(
        handlerName,
        implication(
          left.render(), implication(right.render(), tmh(resultName))),
        proofApply(
          proofApply(hypothesis(handlerName), leftProof),
          rightProof)));
  };
  const auto andElimination = [&](const PreservedSexpr& left,
                                  const PreservedSexpr& right,
                                  const std::string& proof,
                                  bool selectLeft) {
    const std::string leftName = fresh("and_left_");
    const std::string rightName = fresh("and_right_");
    const PreservedSexpr& selected = selectLeft ? left : right;
    return proofApply(
      termApply(proof, formula(selected.render())),
      proofLambda(
        leftName,
        left.render(),
        proofLambda(
          rightName,
          right.render(),
          hypothesis(selectLeft ? leftName : rightName))));
  };
  const auto orIntroduction = [&](const PreservedSexpr& left,
                                  const PreservedSexpr& right,
                                  const std::string& proof,
                                  bool selectLeft) {
    const std::string resultName = fresh("or_result_");
    const std::string leftName = fresh("or_left_");
    const std::string rightName = fresh("or_right_");
    return termLambda(
      resultName,
      "(PROP)",
      proofLambda(
        leftName,
        implication(left.render(), tmh(resultName)),
        proofLambda(
          rightName,
          implication(right.render(), tmh(resultName)),
          proofApply(
            hypothesis(selectLeft ? leftName : rightName), proof))));
  };
  const auto excludedMiddle = [&](const std::string& proposition,
                                  const std::string& resultFormula,
                                  const std::string& positiveName,
                                  const std::string& positiveProof,
                                  const std::string& negativeName,
                                  const std::string& negativeProof) {
    static const char* dnegHash =
      "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0";
    const std::string qName = fresh("xm_result_");
    const std::string leftName = fresh("xm_left_");
    const std::string rightName = fresh("xm_right_");
    const std::string notQName = fresh("xm_not_result_");
    const std::string propositionName = fresh("xm_proposition_");
    const std::string falseFormula = "(TMH \"vampire_false\")";
    const std::string positiveResult = proofApply(
      hypothesis(leftName), hypothesis(propositionName));
    const std::string notProposition = proofLambda(
      propositionName,
      proposition,
      proofApply(hypothesis(notQName), positiveResult));
    const std::string negativeResult = proofApply(
      hypothesis(rightName), notProposition);
    const std::string contradiction = proofApply(
      hypothesis(notQName), negativeResult);
    const std::string dneg = proofApply(
      termApply(
        "(known " + quotePreservedName(dnegHash) + ")",
        formula(tmh(qName))),
      proofLambda(
        notQName,
        implication(tmh(qName), falseFormula),
        contradiction));
    const std::string xm = termLambda(
      qName,
      "(PROP)",
      proofLambda(
        leftName,
        implication(proposition, tmh(qName)),
        proofLambda(
          rightName,
          implication(implication(proposition, falseFormula), tmh(qName)),
          dneg)));
    return proofApply(
      proofApply(
        termApply(xm, formula(resultFormula)),
        proofLambda(positiveName, proposition, positiveProof)),
      proofLambda(
        negativeName,
        implication(proposition, falseFormula),
        negativeProof));
  };

  std::string leafVariableName;
  PreservedSexpr leafBody;
  if (!sexprHead(leafSource, "AP") || leafSource.items.size() != 3
      || !namedTermSexpr(leafSource.items[1], "vampire_exists_prop")
      || !sexprHead(leafSource.items[2], "VLAMV")
      || leafSource.items[2].items.size() != 4
      || !preservedName(leafSource.items[2].items[1], leafVariableName)
      || leafSource.items[2].items[2] != witnessType) {
    error = "uniform Skolem scope " + id
      + " has no exact producer leaf existential";
    return false;
  }
  leafBody = leafSource.items[2].items[3];
  const PreservedSexpr leafBodyAtWitness = substituteNamedVariableSexpr(
    leafBody, leafVariableName, witnessVariable);

  enum class LeafMode { Positive, Negative };
  std::string liftFailure;
  const auto orient = [&](const PreservedSexpr& from,
                          const PreservedSexpr& to,
                          const std::string& proof) {
    if (from == to) return proof;
    MegalodonKernelSyntax::RenderedKernelFoolProgram program;
    std::size_t nextIndex = 0;
    IvyClauseProofBuilder builder;
    std::string mapped;
    return buildFoolProgramNode(
             from, to, true, {}, nextIndex, program.root)
        && builder.foolFormulaProof(program, proof, mapped)
      ? mapped : std::string();
  };
  std::function<std::string(
    const PreservedSexpr&,
    const PreservedSexpr&,
    std::size_t,
    const std::string&,
    LeafMode,
    const std::string&)> lift;
  lift = [&](const PreservedSexpr& currentSource,
             const PreservedSexpr& currentTarget,
             std::size_t pathIndex,
             const std::string& currentProof,
             LeafMode mode,
             const std::string& leafProof) -> std::string {
    if (pathIndex == path.size()) {
      std::string sourceVariable;
      if (!sexprHead(currentSource, "AP")
          || currentSource.items.size() != 3
          || !namedTermSexpr(
               currentSource.items[1], "vampire_exists_prop")
          || !sexprHead(currentSource.items[2], "VLAMV")
          || currentSource.items[2].items.size() != 4
          || !preservedName(
               currentSource.items[2].items[1], sourceVariable)
          || currentSource.items[2].items[2] != witnessType) {
        liftFailure = "leaf source is not the declared existential";
        return std::string();
      }
      if (mode == LeafMode::Positive) {
        const PreservedSexpr sourceBody = substituteNamedVariableSexpr(
          currentSource.items[2].items[3],
          sourceVariable,
          witnessVariable);
        const std::string oriented = orient(
          sourceBody, currentTarget, leafProof);
        if (oriented.empty()) {
          liftFailure = "positive leaf body differs from the abstracted target"
            "\n  source body: " + sourceBody.render()
            + "\n  target body: " + currentTarget.render();
          return std::string();
        }
        return oriented;
      }
      const std::string falseProof = proofApply(leafProof, currentProof);
      return termApply(falseProof, formula(currentTarget.render()));
    }

    if (sexprHead(currentSource, "ALLV")
        && currentSource.items.size() == 4
        && sexprHead(currentTarget, "ALLV")
        && currentTarget.items.size() == 4
        && path[pathIndex] == 0) {
      std::string sourceName;
      std::string targetName;
      if (!preservedName(currentSource.items[1], sourceName)
          || !preservedName(currentTarget.items[1], targetName)
          || sourceName != targetName
          || currentSource.items[2] != currentTarget.items[2]) {
        liftFailure = "forall path frame differs between source and target";
        return std::string();
      }
      const std::string body = lift(
        currentSource.items[3],
        currentTarget.items[3],
        pathIndex + 1,
        termApply(currentProof, term(tmh(sourceName))),
        mode,
        leafProof);
      return body.empty()
        ? std::string()
        : termLambda(sourceName, currentSource.items[2].render(), body);
    }

    PreservedSexpr sourceLeft;
    PreservedSexpr sourceRight;
    PreservedSexpr targetLeft;
    PreservedSexpr targetRight;
    const bool sourceAnd = binaryNamedApplicationSexpr(
      currentSource, "vampire_and", sourceLeft, sourceRight);
    const bool targetAnd = binaryNamedApplicationSexpr(
      currentTarget, "vampire_and", targetLeft, targetRight);
    const bool sourceOr = !sourceAnd && binaryNamedApplicationSexpr(
      currentSource, "vampire_or", sourceLeft, sourceRight);
    const bool targetOr = !targetAnd && binaryNamedApplicationSexpr(
      currentTarget, "vampire_or", targetLeft, targetRight);
    const std::size_t selected = path[pathIndex];
    if (selected > 1
        || sourceAnd != targetAnd || sourceOr != targetOr
        || (!sourceAnd && !sourceOr)) {
      liftFailure = "junction path frame differs between source and target";
      return std::string();
    }
    const PreservedSexpr& sourceChild = selected == 0
      ? sourceLeft : sourceRight;
    const PreservedSexpr& sourceSibling = selected == 0
      ? sourceRight : sourceLeft;
    const PreservedSexpr& targetChild = selected == 0
      ? targetLeft : targetRight;
    const PreservedSexpr& targetSibling = selected == 0
      ? targetRight : targetLeft;
    if (sourceAnd) {
      const std::string childProof = andElimination(
        sourceLeft, sourceRight, currentProof, selected == 0);
      const std::string siblingProof = orient(
        sourceSibling,
        targetSibling,
        andElimination(
          sourceLeft, sourceRight, currentProof, selected != 0));
      const std::string liftedChild = lift(
        sourceChild,
        targetChild,
        pathIndex + 1,
        childProof,
        mode,
        leafProof);
      if (liftedChild.empty() || siblingProof.empty()) {
        if (liftFailure.empty()) {
          liftFailure = "cannot orient the unselected conjunction sibling";
        }
        return std::string();
      }
      return selected == 0
        ? andIntroduction(
            targetChild, targetSibling, liftedChild, siblingProof)
        : andIntroduction(
            targetSibling, targetChild, siblingProof, liftedChild);
    }

    const std::string leftName = fresh("or_case_left_");
    const std::string rightName = fresh("or_case_right_");
    const auto branch = [&](std::size_t branchIndex,
                            const PreservedSexpr& sourceFormula,
                            const PreservedSexpr& targetFormula,
                            const std::string& name) {
      std::string branchProof;
      if (branchIndex == selected) {
        branchProof = lift(
          sourceFormula,
          targetFormula,
          pathIndex + 1,
          hypothesis(name),
          mode,
          leafProof);
      } else {
        branchProof = orient(
          sourceFormula, targetFormula, hypothesis(name));
      }
      return branchProof.empty()
        ? std::string()
        : orIntroduction(
            targetLeft,
            targetRight,
            branchProof,
            branchIndex == 0);
    };
    const std::string leftProof = branch(
      0, sourceLeft, targetLeft, leftName);
    const std::string rightProof = branch(
      1, sourceRight, targetRight, rightName);
    if (leftProof.empty() || rightProof.empty()) return std::string();
    return proofApply(
      proofApply(
        termApply(currentProof, formula(currentTarget.render())),
        proofLambda(leftName, sourceLeft.render(), leftProof)),
      proofLambda(rightName, sourceRight.render(), rightProof));
  };

  const std::string resultExists = exists(
    witnessName, transformed.render());
  const std::string positiveName = fresh("leaf_exists_");
  const std::string positiveBodyName = fresh("leaf_body_");
  const std::string liftedPositive = lift(
    source,
    transformed,
    0,
    sourceProof.render(),
    LeafMode::Positive,
    hypothesis(positiveBodyName));
  if (liftedPositive.empty()) {
    error = "uniform Skolem scope " + id
      + " cannot replay its positive context path: " + liftFailure;
    return false;
  }
  const std::string positivePointwise = termLambda(
    witnessName,
    witnessType.render(),
    proofLambda(
      positiveBodyName,
      leafBodyAtWitness.render(),
      existsIntro(
        transformed.render(), tmh(witnessName), liftedPositive)));
  const std::string positiveProof = proofApply(
    termApply(hypothesis(positiveName), formula(resultExists)),
    positivePointwise);

  PreservedSexpr canonical;
  if (!canonicalInhabitantSexpr(
        witnessType,
        "ivy_uniform_" + id + "_canonical",
        0,
        canonical)) {
    error = "uniform Skolem scope " + id
      + " has no canonical negative-branch witness";
    return false;
  }
  const PreservedSexpr transformedAtCanonical =
    substituteNamedVariableSexpr(
      transformed, witnessName, canonical);
  const std::string negativeName = fresh("not_leaf_exists_");
  const std::string liftedNegative = lift(
    source,
    transformedAtCanonical,
    0,
    sourceProof.render(),
    LeafMode::Negative,
    hypothesis(negativeName));
  if (liftedNegative.empty()) {
    error = "uniform Skolem scope " + id
      + " cannot replay its negative context path";
    return false;
  }
  const std::string negativeProof = existsIntro(
    transformed.render(), canonical.render(), liftedNegative);
  const std::string proof = excludedMiddle(
    leafSource.render(),
    resultExists,
    positiveName,
    positiveProof,
    negativeName,
    negativeProof);
  if (!parser.parse(resultExists, expansion.theorem)
      || !parser.parse(proof, expansion.proof)) {
    error = "uniform Skolem scope " + id
      + " did not emit valid Ivy syntax";
    return false;
  }
  expansion.body = std::move(transformed);
  return true;
}

bool shareRepeatedChoicePropositions(
  MegalodonKernelSyntax::RenderedKernelChoiceProof& proof,
  std::string& error)
{
  using ChoiceNode = MegalodonKernelSyntax::RenderedKernelChoiceProofNode;
  using Environment = std::vector<std::pair<std::string, std::string>>;
  PreservedSexprParser parser;
  struct Candidate {
    std::string key;
    std::string formula;
    Environment parameters;
    std::size_t count = 0;
    std::size_t size = 0;
    std::size_t saving = 0;
    std::string alias;
  };
  std::map<std::string, Candidate> candidates;

  const auto extendEnvironment = [](Environment source,
                                    const std::string& variable,
                                    const std::string& type) {
    source.erase(
      std::remove_if(
        source.begin(), source.end(),
        [&](const auto& item) { return item.first == variable; }),
      source.end());
    source.emplace_back(variable, type);
    return source;
  };
  const auto formulaParameters = [&](const PreservedSexpr& formula,
                                     const Environment& environment) {
    std::set<std::string> freeNames;
    std::map<std::string, std::size_t> boundNames;
    std::function<void(const PreservedSexpr&)> collectFreeNames;
    collectFreeNames = [&](const PreservedSexpr& value) {
      if (sexprHead(value, "TMH") && value.items.size() == 2) {
        std::string name;
        if (preservedName(value.items[1], name)
            && boundNames.find(name) == boundNames.end()) {
          freeNames.insert(std::move(name));
        }
        return;
      }
      if (value.atom) return;
      if ((sexprHead(value, "ALLV")
           || sexprHead(value, "LAMV")
           || sexprHead(value, "VLAMV")
           || sexprHead(value, "term_lambda"))
          && value.items.size() == 4) {
        collectFreeNames(value.items[2]);
        std::string binder;
        if (preservedName(value.items[1], binder)) {
          ++boundNames[binder];
          collectFreeNames(value.items[3]);
          auto bound = boundNames.find(binder);
          if (--bound->second == 0) boundNames.erase(bound);
          return;
        }
      }
      for (std::size_t index = 1; index < value.items.size(); ++index) {
        collectFreeNames(value.items[index]);
      }
    };
    collectFreeNames(formula);
    Environment result;
    for (const auto& parameter : environment) {
      if (freeNames.find(parameter.first) != freeNames.end()) {
        result.push_back(parameter);
      }
    }
    return result;
  };
  const auto formulaKey = [&](const PreservedSexpr& formula,
                              const Environment& environment,
                              Environment& parameters) {
    parameters = formulaParameters(formula, environment);
    std::string key = formula.render();
    for (const auto& parameter : parameters) {
      key += '\x1f' + std::to_string(parameter.first.size()) + ':'
        + parameter.first + ':' + std::to_string(parameter.second.size())
        + ':' + parameter.second;
    }
    return key;
  };
  const auto binaryFormula = [](const PreservedSexpr& formula) {
    const PreservedSexpr* left = nullptr;
    const PreservedSexpr* right = nullptr;
    return binaryNamedApplicationSexprView(
             formula, "vampire_and", left, right)
      || binaryNamedApplicationSexprView(
             formula, "vampire_or", left, right)
      || binaryNamedApplicationSexprView(
             formula, "vampire_eq_prop", left, right);
  };
  const auto existentialFormula = [](const PreservedSexpr& formula) {
    if (!sexprHead(formula, "AP") || formula.items.size() != 3
        || !sexprHead(formula.items[2], "VLAMV")
        || formula.items[2].items.size() != 4) {
      return false;
    }
    return namedTermSexpr(formula.items[1], "vampire_exists_prop")
      || namedTermSexpr(formula.items[1], "vampire_exists_set");
  };
  const auto definiteFormula = [&](const PreservedSexpr& formula) {
    return sexprHead(formula, "ALLV")
      || sexprHead(formula, "IMP")
      || namedTermSexpr(formula, "vampire_true")
      || namedTermSexpr(formula, "vampire_false")
      || namedTermSexpr(formula, "f__true")
      || namedTermSexpr(formula, "f__false")
      || binaryFormula(formula)
      || existentialFormula(formula);
  };
  std::function<void(const PreservedSexpr&, const Environment&)> visitAny;
  std::function<void(const PreservedSexpr&, const Environment&)> visitFormula;
  visitFormula = [&](const PreservedSexpr& formula,
                     const Environment& environment) {
    const std::string rendered = formula.render();
    if (rendered.size() >= 160) {
      Environment parameters;
      const std::string key = formulaKey(formula, environment, parameters);
      auto inserted = candidates.emplace(
        key, Candidate{key, rendered, parameters, 0, rendered.size(), 0, {}});
      ++inserted.first->second.count;
    }
    if (sexprHead(formula, "ALLV") && formula.items.size() == 4) {
      std::string variable;
      if (preservedName(formula.items[1], variable)) {
        visitFormula(
          formula.items[3],
          extendEnvironment(
            environment, variable, formula.items[2].render()));
      }
      return;
    }
    if (sexprHead(formula, "IMP") && formula.items.size() == 3) {
      visitFormula(formula.items[1], environment);
      visitFormula(formula.items[2], environment);
      return;
    }
    const PreservedSexpr* left = nullptr;
    const PreservedSexpr* right = nullptr;
    if (binaryNamedApplicationSexprView(
          formula, "vampire_and", left, right)
        || binaryNamedApplicationSexprView(
          formula, "vampire_or", left, right)
        || binaryNamedApplicationSexprView(
          formula, "vampire_eq_prop", left, right)) {
      visitFormula(*left, environment);
      visitFormula(*right, environment);
      return;
    }
    if (existentialFormula(formula)) {
      const PreservedSexpr& lambda = formula.items[2];
      std::string variable;
      if (preservedName(lambda.items[1], variable)) {
        visitFormula(
          lambda.items[3],
          extendEnvironment(
            environment, variable, lambda.items[2].render()));
      }
    }
  };
  visitAny = [&](const PreservedSexpr& value,
                 const Environment& environment) {
    if (value.atom) return;
    if (sexprHead(value, "formula") && value.items.size() == 2) {
      if (definiteFormula(value.items[1])) {
        visitFormula(value.items[1], environment);
      } else {
        visitAny(value.items[1], environment);
      }
      return;
    }
    if (sexprHead(value, "term") && value.items.size() == 2
        && definiteFormula(value.items[1])) {
      visitFormula(value.items[1], environment);
      return;
    }
    if ((sexprHead(value, "term_lambda")
         || sexprHead(value, "LAMV")
         || sexprHead(value, "VLAMV"))
        && value.items.size() == 4) {
      std::string variable;
      if (preservedName(value.items[1], variable)) {
        visitAny(
          value.items[3],
          extendEnvironment(
            environment, variable, value.items[2].render()));
      }
      return;
    }
    if (definiteFormula(value)) {
      visitFormula(value, environment);
      return;
    }
    for (std::size_t index = 1; index < value.items.size(); ++index) {
      visitAny(value.items[index], environment);
    }
  };
  const auto visitText = [&](const std::string& text,
                             const Environment& environment,
                             bool formula) {
    if (text.empty()) return true;
    PreservedSexpr parsed;
    if (!parser.parse(text, parsed)) return false;
    if (formula) visitFormula(parsed, environment);
    else visitAny(parsed, environment);
    return true;
  };
  for (const ChoiceNode& node : proof.nodes) {
    const Environment environment = node.parameters;
    if (!visitText(node.producerProof, environment, false)
        || !visitText(node.resultFormula, environment, true)
        || !visitText(node.resultClause, environment, false)
        || !visitText(node.rootExistsScopeSourceFormula, environment, true)
        || !visitText(node.rootExistsScopeTargetFormula, environment, true)
        || !visitText(node.rootExistsScopeBridgeProof, environment, false)) {
      error = "choice proof proposition sharing cannot parse node " + node.step;
      return false;
    }
  }

  std::vector<Candidate*> selected;
  for (auto& item : candidates) {
    Candidate& candidate = item.second;
    if (candidate.count < 2) continue;
    const bool hasHigherOrderParameter = std::any_of(
      candidate.parameters.begin(), candidate.parameters.end(),
      [](const auto& parameter) {
        return parameter.second.compare(0, 4, "(AR ") == 0;
      });
    if (hasHigherOrderParameter) continue;
    std::size_t applicationSize = 42;
    for (const auto& parameter : candidate.parameters) {
      applicationSize += parameter.first.size() + 17;
    }
    const std::size_t before = candidate.count * candidate.size;
    const std::size_t after = candidate.size + 96
      + candidate.count * applicationSize;
    if (before > after + 4096) {
      candidate.saving = before - after;
      selected.push_back(&candidate);
    }
  }
  std::sort(
    selected.begin(), selected.end(),
    [](const Candidate* left, const Candidate* right) {
      return std::tie(right->saving, left->key)
        < std::tie(left->saving, right->key);
    });
  if (selected.size() > 512) selected.resize(512);
  if (selected.empty()) return true;

  std::set<std::string> definitionNames;
  for (const auto& definition : proof.definitions) {
    definitionNames.insert(definition.symbol);
  }
  std::size_t ordinal = 0;
  std::map<std::string, Candidate*> selectedByKey;
  for (Candidate* candidate : selected) {
    do {
      candidate->alias = "vampire_ivy_shared_prop_"
        + std::to_string(ordinal++);
    } while (!definitionNames.insert(candidate->alias).second);
    selectedByKey.emplace(candidate->key, candidate);
  }
  const auto application = [&](const Candidate& candidate) {
    std::string result = "(TMH " + quotePreservedName(candidate.alias) + ")";
    for (const auto& parameter : candidate.parameters) {
      result = "(AP " + result + " (TMH "
        + quotePreservedName(parameter.first) + "))";
    }
    PreservedSexpr parsed;
    parser.parse(result, parsed);
    return parsed;
  };
  std::function<PreservedSexpr(
    PreservedSexpr, const Environment&, bool)> rewriteAny;
  std::function<PreservedSexpr(
    PreservedSexpr, const Environment&, bool)> rewriteFormula;
  rewriteFormula = [&](PreservedSexpr formula,
                       const Environment& environment,
                       bool replaceRoot) -> PreservedSexpr {
    Environment parameters;
    const std::string key = formulaKey(formula, environment, parameters);
    auto selectedItem = selectedByKey.find(key);
    if (replaceRoot && selectedItem != selectedByKey.end()) {
      return application(*selectedItem->second);
    }
    PreservedSexpr result = std::move(formula);
    if (sexprHead(result, "ALLV") && result.items.size() == 4) {
      std::string variable;
      if (preservedName(result.items[1], variable)) {
        result.items[3] = rewriteFormula(
          std::move(result.items[3]),
          extendEnvironment(
            environment, variable, result.items[2].render()), true);
      }
      return result;
    }
    if (sexprHead(result, "IMP") && result.items.size() == 3) {
      result.items[1] = rewriteFormula(
        std::move(result.items[1]), environment, true);
      result.items[2] = rewriteFormula(
        std::move(result.items[2]), environment, true);
      return result;
    }
    const PreservedSexpr* left = nullptr;
    const PreservedSexpr* right = nullptr;
    const bool logicalBinary = binaryNamedApplicationSexprView(
        result, "vampire_and", left, right)
      || binaryNamedApplicationSexprView(
           result, "vampire_or", left, right)
      || binaryNamedApplicationSexprView(
           result, "vampire_eq_prop", left, right);
    if (logicalBinary) {
      result.items[1].items[2] =
        rewriteFormula(
          std::move(result.items[1].items[2]), environment, true);
      result.items[2] = rewriteFormula(
        std::move(result.items[2]), environment, true);
      return result;
    }
    if (existentialFormula(result)) {
      PreservedSexpr& lambda = result.items[2];
      std::string variable;
      if (preservedName(lambda.items[1], variable)) {
        lambda.items[3] = rewriteFormula(
          std::move(lambda.items[3]),
          extendEnvironment(
            environment, variable, lambda.items[2].render()), true);
      }
    }
    return result;
  };
  rewriteAny = [&](PreservedSexpr value,
                   const Environment& environment,
                   bool replaceRoot) -> PreservedSexpr {
    if (value.atom) return value;
    PreservedSexpr result = std::move(value);
    if (sexprHead(result, "formula") && result.items.size() == 2) {
      result.items[1] = definiteFormula(result.items[1])
        ? rewriteFormula(std::move(result.items[1]), environment, true)
        : rewriteAny(std::move(result.items[1]), environment, true);
      return result;
    }
    if (sexprHead(result, "term") && result.items.size() == 2
        && definiteFormula(result.items[1])) {
      result.items[1] = rewriteFormula(
        std::move(result.items[1]), environment, true);
      return result;
    }
    if ((sexprHead(result, "term_lambda")
         || sexprHead(result, "LAMV")
         || sexprHead(result, "VLAMV"))
        && result.items.size() == 4) {
      std::string variable;
      if (preservedName(result.items[1], variable)) {
        result.items[3] = rewriteAny(
          std::move(result.items[3]),
          extendEnvironment(
            environment, variable, result.items[2].render()), true);
      }
      return result;
    }
    if (definiteFormula(result)) {
      return rewriteFormula(std::move(result), environment, replaceRoot);
    }
    for (std::size_t index = 1; index < result.items.size(); ++index) {
      result.items[index] = rewriteAny(
        std::move(result.items[index]), environment, true);
    }
    return result;
  };
  const auto rewriteText = [&](std::string& text,
                               const Environment& environment,
                               bool formula) {
    if (text.empty()) return true;
    PreservedSexpr parsed;
    if (!parser.parse(text, parsed)) return false;
    parsed = formula
      ? rewriteFormula(std::move(parsed), environment, true)
      : rewriteAny(std::move(parsed), environment, true);
    text = parsed.render();
    return true;
  };

  std::sort(
    selected.begin(), selected.end(),
    [](const Candidate* left, const Candidate* right) {
      return std::tie(left->size, left->key)
        < std::tie(right->size, right->key);
    });
  for (const Candidate* candidate : selected) {
    PreservedSexpr body;
    if (!parser.parse(candidate->formula, body)) {
      error = "choice proof proposition sharing cannot parse selected formula";
      return false;
    }
    body = rewriteFormula(
      std::move(body), candidate->parameters, false);
    std::string bodyText = body.render();
    std::string type = "(PROP)";
    for (auto item = candidate->parameters.rbegin();
         item != candidate->parameters.rend(); ++item) {
      bodyText = "(LAMV " + quotePreservedName(item->first) + " "
        + item->second + " " + bodyText + ")";
      type = "(AR " + item->second + " " + type + ")";
    }
    proof.definitions.push_back(
      {candidate->alias, std::move(type), std::move(bodyText)});
  }
  for (ChoiceNode& node : proof.nodes) {
    const Environment environment = node.parameters;
    if (!rewriteText(node.producerProof, environment, false)
        || !rewriteText(node.resultFormula, environment, true)
        || !rewriteText(node.resultClause, environment, false)
        || !rewriteText(node.rootExistsScopeSourceFormula, environment, true)
        || !rewriteText(node.rootExistsScopeTargetFormula, environment, true)
        || !rewriteText(node.rootExistsScopeBridgeProof, environment, false)) {
      error = "choice proof proposition sharing cannot rewrite node "
        + node.step;
      return false;
    }
  }
  return true;
}

bool expandGroundChoiceProof(
  const MegalodonKernelSyntax::RenderedKernelChoiceProof& source,
  const MegalodonKernelSyntax::RenderedKernelGroundProof& groundProof,
  const MegalodonKernelSyntax::RenderedKernelFiniteSkolemProof& finiteProof,
  MegalodonKernelSyntax::RenderedKernelChoiceProof& result,
  std::string& error)
{
  using ChoiceNode = MegalodonKernelSyntax::RenderedKernelChoiceProofNode;
  using GroundInstance = MegalodonKernelSyntax::RenderedKernelGroundInstance;
  using IvyRule = MegalodonKernelSyntax::RenderedKernelIvyRule;
  PreservedSexprParser parser;
  const std::function<bool(
    const PreservedSexpr&, const PreservedSexpr&)>
    containsAlphaEquivalentNormalized = [&]
      (const PreservedSexpr& value, const PreservedSexpr& needle) {
      if (alphaEquivalentSexpr(value, needle)) return true;
      if (value.atom) return false;
      for (std::size_t index = 1; index < value.items.size(); ++index) {
        if (containsAlphaEquivalentNormalized(
              value.items[index], needle)) return true;
      }
      return false;
    };
  const auto containsAlphaEquivalent = [&]
    (const PreservedSexpr& value, const PreservedSexpr& needle) {
      const PreservedSexpr normalizedNeedle = betaNormalizeSexpr(needle);
      return containsAlphaEquivalentNormalized(
        betaNormalizeSexpr(value), normalizedNeedle);
    };
  const std::function<PreservedSexpr(
    const PreservedSexpr&,
    const PreservedSexpr&,
    const PreservedSexpr&,
    std::size_t&)>
    replaceAlphaEquivalentNormalized = [&]
      (const PreservedSexpr& value,
       const PreservedSexpr& needle,
       const PreservedSexpr& replacement,
       std::size_t& replacements) {
      if (alphaEquivalentSexpr(value, needle)) {
        ++replacements;
        return replacement;
      }
      if (value.atom) return value;
      PreservedSexpr result;
      result.atom = false;
      result.items.reserve(value.items.size());
      if (!value.items.empty()) {
        result.items.push_back(value.items.front());
      }
      for (std::size_t index = 1; index < value.items.size(); ++index) {
        result.items.push_back(replaceAlphaEquivalentNormalized(
          value.items[index], needle, replacement, replacements));
      }
      return result;
    };
  const auto replaceAlphaEquivalent = [&]
    (const PreservedSexpr& value,
     const PreservedSexpr& needle,
     const PreservedSexpr& replacement,
      std::size_t& replacements) {
      return replaceAlphaEquivalentNormalized(
        value, betaNormalizeSexpr(needle), replacement, replacements);
    };
  result = {};
  const bool atomicChoicePlan =
    finiteProof.version == "ivy_atomic_choice_v1";
  if ((source.version != "ivy_choice_dag_v1"
       && source.version != "ivy_choice_dag_v2"
       && source.version != "ivy_choice_dag_v3")
      || source.nodes.empty() || source.finalStep.empty()
      || groundProof.version != "ivy_instance_v3"
      || groundProof.instances.empty()
      || groundProof.finalStep.value.empty()
      || (!atomicChoicePlan && finiteProof.version != "smolka_finite_v7")
      || (!atomicChoicePlan && finiteProof.applications.empty())
      || (atomicChoicePlan && !finiteProof.applications.empty())
      || finiteProof.dischargeOrder.size() != finiteProof.applications.size()
      || finiteProof.finalStep.value != groundProof.finalStep.value) {
    error = "ground choice prooftrans received an incomplete source DAG or instance graph";
    return false;
  }
  std::set<std::string> choiceDefinitionNames;
  for (const auto& definition : source.definitions) {
    PreservedSexpr body;
    const bool split = definition.symbol.compare(0, 6, "split_") == 0;
    const bool sharedTerm =
      definition.symbol.compare(0, 24, "vampire_ivy_shared_term_") == 0;
    if ((!split && !sharedTerm)
        || (split && definition.type != "(PROP)")
        || definition.type.empty()
        || !parser.parse(definition.body, body)
        || !choiceDefinitionNames.insert(definition.symbol).second) {
      error = "ground choice prooftrans received an invalid shared definition";
      return false;
    }
  }
  for (std::size_t index = 0; index < groundProof.instances.size(); ++index) {
    if (groundProof.instances[index].index != index) {
      error = "ground choice prooftrans requires contiguous instance indices";
      return false;
    }
  }
  std::vector<std::size_t> dischargeRank(
    finiteProof.applications.size(), finiteProof.applications.size());
  for (std::size_t rank = 0; rank < finiteProof.dischargeOrder.size(); ++rank) {
    const std::size_t application = finiteProof.dischargeOrder[rank];
    if (application >= finiteProof.applications.size()
        || dischargeRank[application] != finiteProof.applications.size()) {
      error = "ground choice prooftrans finite discharge order is not a permutation";
      return false;
    }
    dischargeRank[application] = rank;
  }
  std::vector<std::vector<std::size_t>> finiteApplicationsByInstance(
    groundProof.instances.size());
  for (std::size_t expected = 0;
       expected < finiteProof.applications.size();
       ++expected) {
    const auto& application = finiteProof.applications[expected];
    const auto& definition = application.producerChoiceDefinition;
    if (application.index != expected
        || application.ownerInstance >= groundProof.instances.size()
        || application.skolemStep.value.empty()
        || application.symbol.empty()
        || application.term.sexpr.empty()
        || definition.branchIndex != application.branchIndex
        || definition.witnessIndex != application.witnessIndex
        || definition.symbol != application.symbol
        || definition.witnessTypeSexpr != application.witnessTypeSexpr
        || definition.scopeParentFormulaSexpr.empty()
        || definition.scopeParentTransformProof.empty()
        || definition.contextScopeSourceFormulaSexpr.empty()
        || definition.contextScopeTargetFormulaSexpr.empty()
        || definition.contextScopeBridgeProof.empty()) {
      error = "ground choice prooftrans finite application lacks its exact producer witness program";
      return false;
    }
    const GroundInstance& owner = groundProof.instances[application.ownerInstance];
    if (owner.unit.value != application.skolemStep.value) {
      error = "ground choice prooftrans finite application owner is not its Skolem step";
      return false;
    }
    bool hasOwnerOccurrence = false;
    for (std::size_t occurrenceIndex = 0;
         occurrenceIndex < application.occurrences.size();
         ++occurrenceIndex) {
      const auto& occurrence = application.occurrences[occurrenceIndex];
      if (occurrence.index != occurrenceIndex
          || occurrence.instance >= groundProof.instances.size()
          || occurrence.unit.value
             != groundProof.instances[occurrence.instance].unit.value) {
        error = "ground choice prooftrans finite occurrence has invalid instance ownership";
        return false;
      }
      const auto& groundApplications =
        groundProof.instances[occurrence.instance].applications;
      const bool declared = std::any_of(
        groundApplications.begin(), groundApplications.end(),
        [&](const auto& groundApplication) {
          return groundApplication.skolemStep == application.skolemStep.value
            && groundApplication.symbol == application.symbol
            && groundApplication.term.sexpr == occurrence.term.sexpr;
        });
      if (!declared) {
        error = "ground choice prooftrans finite occurrence is absent from its producer instance";
        return false;
      }
      if (occurrence.instance == application.ownerInstance
          && occurrence.term.sexpr == application.term.sexpr) {
        hasOwnerOccurrence = true;
      }
      finiteApplicationsByInstance[occurrence.instance].push_back(expected);
    }
    if (!hasOwnerOccurrence) {
      error = "ground choice prooftrans finite application omits its owner occurrence";
      return false;
    }
    for (const auto& dependency : application.dependencies) {
      for (std::size_t nested : dependency.nestedApplications) {
        if (nested >= finiteProof.applications.size()
            || dischargeRank[nested] >= dischargeRank[expected]) {
          error = "ground choice prooftrans finite dependency is not discharged first";
          return false;
        }
      }
    }
  }

  std::map<std::string, const ChoiceNode*> nodeById;
  for (const ChoiceNode& node : source.nodes) {
    if (node.step.empty() || !nodeById.emplace(node.step, &node).second) {
      error = "ground choice prooftrans source has duplicate nodes";
      return false;
    }
  }
  const std::string prefix = "ivy_choice_";
  const auto mainNodeId = [&](const std::string& unit) {
    const std::string normalized = prefix + unit;
    return nodeById.find(normalized) == nodeById.end() ? unit : normalized;
  };
  if (mainNodeId(groundProof.finalStep.value) != source.finalStep) {
    error = "ground choice prooftrans roots disagree";
    return false;
  }

  std::map<std::string, PreservedSexpr> producerSubstitutions;
  for (const auto& binding : source.producerGroundSubstitutions) {
    PreservedSexpr term;
    if (binding.first.empty() || !parser.parse(binding.second, term)
        || !producerSubstitutions.emplace(
             binding.first, std::move(term)).second) {
      error = "ground choice prooftrans cannot parse the producer normalization map";
      return false;
    }
  }
  const auto normalizeProducerTerms = [&](const PreservedSexpr& value,
                                          const auto& self) -> PreservedSexpr {
    if (sexprHead(value, "TMH") && value.items.size() == 2) {
      std::string name;
      if (preservedName(value.items[1], name)) {
        auto binding = producerSubstitutions.find(name);
        if (binding != producerSubstitutions.end()) return binding->second;
      }
    }
    if (value.atom) return value;
    PreservedSexpr result;
    result.atom = false;
    result.items.reserve(value.items.size());
    if (!value.items.empty()) {
      result.items.push_back(value.items.front());
    }
    for (std::size_t index = 1; index < value.items.size(); ++index) {
      result.items.push_back(self(value.items[index], self));
    }
    return result;
  };
  const auto normalizePrivateProofReferences = [&]
    (const ChoiceNode& node,
     const PreservedSexpr& value,
     const auto& self) -> PreservedSexpr {
    const auto replaceReference = [&](const char* head,
                                      const auto& aliases,
                                      PreservedSexpr& replacement) {
      if (!sexprHead(value, head) || value.items.size() != 2) return false;
      std::string name;
      if (!preservedName(value.items[1], name)) return false;
      auto alias = std::find_if(
        aliases.begin(), aliases.end(),
        [&](const auto& item) { return item.first == name; });
      return alias != aliases.end()
        && parser.parse(
             "(parent " + quotePreservedName(alias->second) + ")",
             replacement);
    };
    PreservedSexpr replacement;
    if (replaceReference(
          "parent", node.producerProofParentAliases, replacement)
        || replaceReference(
             "definition", node.producerProofDefinitionAliases,
             replacement)) {
      return replacement;
    }
    if (value.atom) return value;
    PreservedSexpr result;
    result.atom = false;
    result.items.reserve(value.items.size());
    if (!value.items.empty()) result.items.push_back(value.items.front());
    for (std::size_t index = 1; index < value.items.size(); ++index) {
      result.items.push_back(self(node, value.items[index], self));
    }
    return result;
  };

  const auto groundId = [](std::size_t instance, const std::string& node) {
    return "ivy_ground_" + std::to_string(instance) + "_" + node;
  };
  const auto sharedGroundId = [](const std::string& node) {
    return "ivy_ground_shared_" + node;
  };
  const auto parseGroundBindings = [&](const auto& bindings) {
    std::map<std::string, PreservedSexpr> result;
    for (const auto& binding : bindings) {
      PreservedSexpr term;
      if (!parser.parse(binding.term.sexpr, term)
          || !result.emplace(binding.variable, std::move(term)).second) {
        result.clear();
        return result;
      }
      result.at(binding.variable) = normalizeProducerTerms(
        result.at(binding.variable), normalizeProducerTerms);
    }
    return result;
  };
  std::vector<std::map<std::string, PreservedSexpr>> environments;
  std::vector<std::vector<std::map<std::string, PreservedSexpr>>>
    parentEnvironments;
  environments.reserve(groundProof.instances.size());
  parentEnvironments.reserve(groundProof.instances.size());
  for (const GroundInstance& instance : groundProof.instances) {
    auto parsed = parseGroundBindings(instance.environment);
    if (parsed.size() != instance.environment.size()) {
      error = "ground choice prooftrans cannot parse an instance environment";
      return false;
    }
    environments.push_back(std::move(parsed));
    if (instance.parentInstances.size()
        != instance.parentEnvironments.size()) {
      error = "ground choice prooftrans received incomplete parent-edge environments";
      return false;
    }
    std::vector<std::map<std::string, PreservedSexpr>> parsedParents;
    parsedParents.reserve(instance.parentEnvironments.size());
    for (const auto& parentEnvironment : instance.parentEnvironments) {
      auto parsedParent = parseGroundBindings(parentEnvironment);
      if (parsedParent.size() != parentEnvironment.size()) {
        error = "ground choice prooftrans cannot parse a parent-edge environment";
        return false;
      }
      parsedParents.push_back(std::move(parsedParent));
    }
    parentEnvironments.push_back(std::move(parsedParents));
  }
  const auto specializeWithEnvironment = [&]
    (PreservedSexpr value,
     const std::map<std::string, PreservedSexpr>& bindings) {
    std::set<std::string> shadowed;
    const auto specializeAll = [&]
      (PreservedSexpr source,
       const auto& self) -> PreservedSexpr {
      if (sexprHead(source, "TMH") && source.items.size() == 2) {
        std::string name;
        if (preservedName(source.items[1], name)
            && shadowed.find(name) == shadowed.end()) {
          auto binding = bindings.find(name);
          if (binding != bindings.end()) return binding->second;
        }
      }
      if (source.atom) return source;
      if (sexprHead(source, "substitute") && source.items.size() == 3
          && sexprHead(source.items[1], "subst")) {
        std::vector<std::string> localBindings;
        for (std::size_t index = 1;
             index < source.items[1].items.size(); ++index) {
          PreservedSexpr& binding = source.items[1].items[index];
          std::string name;
          if (binding.atom || binding.items.size() != 2
              || !preservedName(binding.items[0], name)) {
            continue;
          }
          binding.items[1] = self(std::move(binding.items[1]), self);
          localBindings.push_back(std::move(name));
        }
        std::vector<std::string> newlyShadowed;
        for (const std::string& name : localBindings) {
          if (shadowed.insert(name).second) newlyShadowed.push_back(name);
        }
        source.items[2] = self(std::move(source.items[2]), self);
        for (const std::string& name : newlyShadowed) shadowed.erase(name);
        return source;
      }
      const bool binder =
        (sexprHead(source, "ALLV")
         || sexprHead(source, "LAMV")
         || sexprHead(source, "VLAMV")
         || sexprHead(source, "term_lambda"))
        && source.items.size() == 4;
      if (binder) {
        source.items[2] = self(std::move(source.items[2]), self);
        std::string name;
        if (!preservedName(source.items[1], name)) {
          source.items[3] = self(std::move(source.items[3]), self);
          return source;
        }
        const bool inserted = shadowed.insert(name).second;
        source.items[3] = self(std::move(source.items[3]), self);
        if (inserted) shadowed.erase(name);
        return source;
      }
      for (std::size_t index = 1; index < source.items.size(); ++index) {
        source.items[index] = self(std::move(source.items[index]), self);
      }
      return source;
    };
    return specializeAll(std::move(value), specializeAll);
  };
  const auto specialize = [&](PreservedSexpr value,
                              std::size_t instance) {
    return specializeWithEnvironment(
      std::move(value), environments[instance]);
  };
  struct FiniteWitnessClass {
    std::string type;
    PreservedSexpr witness;
    std::size_t count = 0;
  };
  std::vector<FiniteWitnessClass> finiteWitnessClasses;
  for (const auto& application : finiteProof.applications) {
    const std::string sourceNodeId = mainNodeId(application.skolemStep.value);
    const auto sourceNode = nodeById.find(sourceNodeId);
    if (sourceNode == nodeById.end()
        || application.ownerInstance >= environments.size()
        || !sourceNode->second->hasRootExistsScope
        || sourceNode->second->rootExistsScopeWitnessType == "(SET)") {
      continue;
    }
    const std::size_t macroApplicationCount = static_cast<std::size_t>(
      std::count_if(
        finiteProof.applications.begin(),
        finiteProof.applications.end(),
        [&](const auto& candidate) {
          return candidate.ownerInstance == application.ownerInstance
            && candidate.skolemStep.value == application.skolemStep.value;
        }));
    const bool hasRetainedParameter = std::any_of(
      application.producerChoiceDefinition.parameters.begin(),
      application.producerChoiceDefinition.parameters.end(),
      [&](const auto& parameter) {
        return environments[application.ownerInstance].find(parameter.first)
          == environments[application.ownerInstance].end();
      });
    if (macroApplicationCount != 1 || hasRetainedParameter) continue;

    PreservedSexpr witness;
    if (!parser.parse(application.term.sexpr, witness)) {
      error = "ground choice prooftrans cannot parse a finite witness during replay selection";
      return false;
    }
    witness = betaNormalizeSexpr(specialize(
      normalizeProducerTerms(witness, normalizeProducerTerms),
      application.ownerInstance));
    auto witnessClass = std::find_if(
      finiteWitnessClasses.begin(), finiteWitnessClasses.end(),
      [&](const FiniteWitnessClass& candidate) {
        return candidate.type == application.witnessTypeSexpr
          && alphaEquivalentSexpr(candidate.witness, witness);
      });
    if (witnessClass == finiteWitnessClasses.end()) {
      finiteWitnessClasses.push_back(
        {application.witnessTypeSexpr, std::move(witness), 1});
    } else {
      ++witnessClass->count;
    }
  }
  const bool forceAtomicFiniteReplay = atomicChoicePlan
    || (finiteWitnessClasses.size() > 1
        && std::any_of(
      finiteWitnessClasses.begin(), finiteWitnessClasses.end(),
      [](const FiniteWitnessClass& witnessClass) {
        return witnessClass.count > 1;
      }));
  const auto specializeLeadingBindersWithEnvironment = [&](
      PreservedSexpr value,
      const std::map<std::string, PreservedSexpr>& bindings,
      const std::string& binderHead) {
    std::function<PreservedSexpr(PreservedSexpr)> descend;
    descend = [&](PreservedSexpr current) -> PreservedSexpr {
      if (sexprHead(current, "term_apply")
          && current.items.size() == 3
          && sexprHead(current.items[1], binderHead.c_str())
          && current.items[1].items.size() == 4
          && sexprHead(current.items[2], "term")
          && current.items[2].items.size() == 2) {
        std::string variable;
        PreservedSexpr canonical;
        if (preservedName(current.items[1].items[1], variable)
            && canonicalInhabitantSexpr(
                 current.items[1].items[2],
                 "ivy_inhabitant_" + variable, 0, canonical)
            && current.items[2].items[1] == canonical) {
          auto binding = bindings.find(variable);
          if (binding != bindings.end()) {
            return descend(substituteNamedVariableSexpr(
              current.items[1].items[3], variable, binding->second));
          }
        }
      }
      if (!sexprHead(current, binderHead.c_str())
          || current.items.size() != 4) {
        return specializeWithEnvironment(std::move(current), bindings);
      }
      std::string variable;
      if (!preservedName(current.items[1], variable)) {
        return specializeWithEnvironment(std::move(current), bindings);
      }
      auto binding = bindings.find(variable);
      if (binding != bindings.end()) {
        return descend(substituteNamedVariableSexpr(
          current.items[3], variable, binding->second));
      }
      current.items[3] = descend(std::move(current.items[3]));
      return current;
    };
    return descend(std::move(value));
  };
  const auto specializeLeadingBinders = [&]
    (PreservedSexpr value,
     std::size_t instance,
     const std::string& binderHead) {
    return specializeLeadingBindersWithEnvironment(
      std::move(value), environments[instance], binderHead);
  };
  const auto retainedParameters = [&]
    (const ChoiceNode& node,
     const std::map<std::string, PreservedSexpr>& bindings) {
    std::vector<std::pair<std::string, std::string>> retained;
    for (const auto& parameter : node.parameters) {
      if (bindings.find(parameter.first) == bindings.end()) {
        retained.push_back(parameter);
      }
    }
    return retained;
  };
  const auto formulaBinderSpecializations = [&](const ChoiceNode& node,
                                                std::size_t instance) {
    std::vector<bool> result;
    if (!node.hasResultFormula) return result;
    const auto& bindings = environments[instance];
    PreservedSexpr formula;
    if (!parser.parse(node.resultFormula, formula)) return result;
    while (sexprHead(formula, "ALLV") && formula.items.size() == 4) {
      std::string variable;
      if (!preservedName(formula.items[1], variable)) break;
      result.push_back(
        bindings.find(variable) != bindings.end());
      formula = formula.items[3];
    }
    return result;
  };
  std::set<std::string> groundInstanceUnits;
  for (const GroundInstance& instance : groundProof.instances) {
    groundInstanceUnits.insert(instance.unit.value);
  }
  const auto mainUnit = [&](const std::string& nodeId,
                            std::string& unit) {
    if (nodeId.compare(0, prefix.size(), prefix) != 0) return false;
    unit = nodeId.substr(prefix.size());
    return groundInstanceUnits.find(unit) != groundInstanceUnits.end();
  };
  const auto parentInstance = [&](std::size_t child,
                                  const std::string& unit,
                                  std::size_t& parent) {
    const GroundInstance& instance = groundProof.instances[child];
    std::vector<std::size_t> matches;
    for (std::size_t candidate : instance.parentInstances) {
      if (candidate < groundProof.instances.size()
          && groundProof.instances[candidate].unit.value == unit) {
        matches.push_back(candidate);
      }
    }
    if (matches.size() != 1) return false;
    parent = matches.front();
    return true;
  };
  const auto collectProofParents = [&](const PreservedSexpr& source,
                                       std::set<std::string>& parents,
                                       const auto& self) -> void {
    if (sexprHead(source, "parent") && source.items.size() == 2) {
      std::string parent;
      if (preservedName(source.items[1], parent)) parents.insert(parent);
      return;
    }
    if (source.atom) return;
    for (const auto& item : source.items) self(item, parents, self);
  };
  const auto sharedParentId = [&](const std::string& parent) {
    auto found = nodeById.find(parent);
    if (found == nodeById.end()) found = nodeById.find(mainNodeId(parent));
    return found != nodeById.end()
        && found->second->producerShareAcrossGroundInstances
      ? sharedGroundId(found->first) : parent;
  };
  const auto rewriteSharedParents = [&](const PreservedSexpr& source,
                                        const auto& self) -> PreservedSexpr {
    if (sexprHead(source, "parent") && source.items.size() == 2) {
      std::string parent;
      PreservedSexpr rewritten;
      if (preservedName(source.items[1], parent)
          && parser.parse(
            "(parent " + quotePreservedName(sharedParentId(parent)) + ")",
            rewritten)) {
        return rewritten;
      }
    }
    if (source.atom) return source;
    PreservedSexpr rewritten;
    rewritten.atom = false;
    rewritten.items.reserve(source.items.size());
    if (!source.items.empty()) {
      rewritten.items.push_back(source.items.front());
    }
    for (std::size_t index = 1; index < source.items.size(); ++index) {
      rewritten.items.push_back(self(source.items[index], self));
    }
    return rewritten;
  };
  std::map<std::string, std::size_t> resultNodeIndex;
  for (const ChoiceNode& node : source.nodes) {
    if (!node.producerShareAcrossGroundInstances) continue;
    if (node.hasRootExistsScope) {
      error = "ground choice prooftrans cannot share a scoped local theorem "
        + node.step;
      return false;
    }
    PreservedSexpr proof;
    const bool hasDirectProof =
      node.ivyJustification.rule == IvyRule::None
      && !node.producerProof.empty();
    if (!hasDirectProof
        && node.ivyJustification.rule == IvyRule::None) {
      error = "ground choice prooftrans shared theorem has no Ivy justification "
        + node.step;
      return false;
    }
    if (hasDirectProof && !parser.parse(node.producerProof, proof)) {
      error = "ground choice prooftrans cannot parse shared theorem "
        + node.step;
      return false;
    }
    ChoiceNode shared = node;
    shared.index = result.nodes.size();
    shared.step = sharedGroundId(node.step);
    if (hasDirectProof) {
      shared.producerProof =
        rewriteSharedParents(proof, rewriteSharedParents).render();
    } else {
      shared.producerProof.clear();
    }
    shared.parents.clear();
    for (const std::string& parent : node.parents) {
      const std::string rewritten = sharedParentId(parent);
      if (std::find(shared.parents.begin(), shared.parents.end(), rewritten)
          == shared.parents.end()) {
        shared.parents.push_back(rewritten);
      }
    }
    for (std::string& parent : shared.ivyJustification.parents) {
      parent = sharedParentId(parent);
    }
    shared.producerShareAcrossGroundInstances = false;
    shared.hasProducerGroundOrigin = false;
    shared.producerGroundSourceNode.clear();
    shared.producerGroundSourceInstance = 0;
    resultNodeIndex.emplace(shared.step, shared.index);
    result.nodes.push_back(std::move(shared));
  }
  const auto adaptCnfProjection = [&]
    (const PreservedSexpr& originalSource,
     const PreservedSexpr& contextualSource,
     const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
     const std::vector<std::string>& literals,
     const std::map<std::string, PreservedSexpr>& environment,
     MegalodonKernelSyntax::RenderedKernelCnfProjection& adaptedProjection,
     std::string& failure) {
    failure.clear();
    const auto fail = [&](const std::string& reason,
                          const PreservedSexpr& original,
                          const PreservedSexpr& contextual,
                          const auto& item) {
      if (failure.empty()) {
        failure = reason + " at " + item.kind
          + "; original=" + original.render()
          + "; contextual=" + contextual.render();
      }
      return false;
    };
    std::function<bool(
      const PreservedSexpr&,
      const PreservedSexpr&,
      const MegalodonKernelSyntax::RenderedKernelCnfProjection&,
      MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
      adapt;
    adapt = [&](const PreservedSexpr& original,
                const PreservedSexpr& contextual,
                const auto& item,
                auto& adapted) {
      adapted = item;
      if (!sexprHead(original, "ALLV")
          && sexprHead(contextual, "ALLV")
          && contextual.items.size() == 4) {
        std::string contextualName;
        if (!preservedName(contextual.items[1], contextualName)) {
          return fail(
            "contextual forall has no variable", original, contextual, item);
        }
        auto binding = environment.find(contextualName);
        if (binding == environment.end()) {
          return fail(
            "contextual forall has no producer ground binding",
            original, contextual, item);
        }
        const PreservedSexpr contextualBody = substituteNamedVariableSexpr(
          contextual.items[3], contextualName, binding->second);
        adapted = {};
        adapted.kind = "forall";
        adapted.hasVariable = true;
        adapted.variable = contextualName;
        adapted.hasVariableType = true;
        adapted.variableType = MegalodonKernelSyntax::type(
          contextual.items[2].render());
        adapted.hasWitnessTerm = true;
        adapted.witnessTerm = MegalodonKernelSyntax::term(
          binding->second.render());
        adapted.children.resize(1);
        return adapt(
          original, contextualBody, item, adapted.children[0]);
      }
      if (item.kind == "false") {
        const bool matches = item.children.empty()
          && (namedTermSexpr(original, "vampire_false")
              || namedTermSexpr(original, "f__false"))
          && (namedTermSexpr(contextual, "vampire_false")
              || namedTermSexpr(contextual, "f__false"));
        return matches || fail(
          "false-source mismatch", original, contextual, item);
      }
      if (item.kind == "literal") {
        if (!item.children.empty()
            || item.resultLiteralIndex >= literals.size()) {
          return fail(
            "malformed literal projection", original, contextual, item);
        }
        PreservedSexpr expected;
        if (sexprHead(contextual, "IMP")
            && contextual.items.size() == 3
            && (namedTermSexpr(contextual.items[2], "vampire_false")
                || namedTermSexpr(contextual.items[2], "f__false"))) {
          expected = literalSexpr(false, contextual.items[1]);
        } else {
          expected = literalSexpr(true, contextual);
        }
        PreservedSexpr actualLiteral;
        if (!parser.parse(literals[item.resultLiteralIndex], actualLiteral)
            || !alphaEquivalentSexpr(
                 betaNormalizeSexpr(expected),
                 betaNormalizeSexpr(actualLiteral))) {
          return fail(
            "result literal mismatch: expected " + expected.render()
              + "; actual " + literals[item.resultLiteralIndex],
            original, contextual, item);
        }
        adapted.hasSourceLiteral = true;
        adapted.sourceLiteral = MegalodonKernelSyntax::literal(
          literals[item.resultLiteralIndex]);
        return true;
      }
      if (item.kind == "forall") {
        if (item.children.size() != 1
            || !sexprHead(original, "ALLV")
            || original.items.size() != 4) {
          return fail(
            "forall-source mismatch", original, contextual, item);
        }
        std::string originalName;
        if (!preservedName(original.items[1], originalName)) return false;
        if (sexprHead(contextual, "ALLV")
            && contextual.items.size() == 4
            && original.items[2] == contextual.items[2]) {
          std::string contextualName;
          PreservedSexpr witness;
          if (!preservedName(contextual.items[1], contextualName)
              || !item.hasWitnessTerm
              || !parser.parse(item.witnessTerm.sexpr, witness)) {
            return fail(
              "retained forall projection lacks its Vampire witness",
              original, contextual, item);
          }
          const PreservedSexpr originalBody = substituteNamedVariableSexpr(
            original.items[3], originalName, witness);
          const PreservedSexpr contextualBody = substituteNamedVariableSexpr(
            contextual.items[3], contextualName, witness);
          adapted.children.resize(1);
          return adapt(
            originalBody, contextualBody,
            item.children[0], adapted.children[0]);
        }
        PreservedSexpr witness;
        if (!item.hasWitnessTerm
            || !parser.parse(item.witnessTerm.sexpr, witness)) {
          return fail(
            "forall projection lacks an explicit witness",
            original, contextual, item);
        }
        const PreservedSexpr instantiated = substituteNamedVariableSexpr(
          original.items[3], originalName, witness);
        return adapt(instantiated, contextual, item.children[0], adapted);
      }
      PreservedSexpr originalLeft;
      PreservedSexpr originalRight;
      PreservedSexpr contextualLeft;
      PreservedSexpr contextualRight;
      if (item.kind == "and_left" || item.kind == "and_right") {
        if (item.children.size() != 1
            || !binaryNamedApplicationSexpr(
                 original, "vampire_and", originalLeft, originalRight)
            || !binaryNamedApplicationSexpr(
                 contextual, "vampire_and",
                 contextualLeft, contextualRight)) {
          return fail(
            "conjunction-source mismatch", original, contextual, item);
        }
        const bool left = item.kind == "and_left";
        adapted.children.resize(1);
        return adapt(
          left ? originalLeft : originalRight,
          left ? contextualLeft : contextualRight,
          item.children[0], adapted.children[0]);
      }
      if (item.kind == "or") {
        if (item.children.size() != 2
            || !binaryNamedApplicationSexpr(
                 original, "vampire_or", originalLeft, originalRight)
            || !binaryNamedApplicationSexpr(
                 contextual, "vampire_or",
                 contextualLeft, contextualRight)) {
          return fail(
            "disjunction-source mismatch", original, contextual, item);
        }
        adapted.children.resize(2);
        return adapt(
                 originalLeft, contextualLeft,
                 item.children[0], adapted.children[0])
          && adapt(
               originalRight, contextualRight,
               item.children[1], adapted.children[1]);
      }
      return fail("unknown projection kind", original, contextual, item);
    };
    return adapt(
      originalSource, contextualSource, projection, adaptedProjection);
  };

  struct Key {
    std::string node;
    std::size_t instance = 0;
    bool operator<(const Key& other) const {
      return std::tie(instance, node) < std::tie(other.instance, other.node);
    }
  };
  struct ParentTarget {
    bool generated = false;
    Key key;
    std::string rendered;
  };
  const auto resolveParentForKey = [&]
    (const Key& child,
     const std::string& parent,
     ParentTarget& target) {
    auto generic = nodeById.find(parent);
    if (generic == nodeById.end()) {
      generic = nodeById.find(mainNodeId(parent));
    }
    if (generic == nodeById.end()) {
      target.rendered = parent;
      return true;
    }
    const std::string& sourceParent = generic->first;
    if (generic->second->producerShareAcrossGroundInstances) {
      target.rendered = sharedGroundId(sourceParent);
      return true;
    }
    std::string unit;
    std::size_t instance = child.instance;
    if (mainUnit(sourceParent, unit)) {
      if (unit != groundProof.instances[child.instance].unit.value
          && !parentInstance(child.instance, unit, instance)) {
        error = "ground choice prooftrans cannot identify the exact parent instance for "
          + parent + " from instance " + std::to_string(child.instance);
        return false;
      }
    }
    target.generated = true;
    target.key = {sourceParent, instance};
    target.rendered = groundId(instance, sourceParent);
    return true;
  };
  std::map<Key, unsigned> state;
  std::map<Key, std::size_t> emittedIndex;
  struct PendingUniformScope {
    std::string supportStep;
    std::string witnessType;
    PreservedSexpr witness;
    PreservedSexpr source;
  };
  std::map<std::string, PendingUniformScope> pendingUniformScopes;
  std::function<bool(const Key&)> emit;
  emit = [&](const Key& key) {
    const unsigned currentState = state[key];
    if (currentState == 2) return true;
    if (currentState == 1) {
      error = "ground choice prooftrans found a cyclic support DAG";
      return false;
    }
    auto foundNode = nodeById.find(key.node);
    if (foundNode == nodeById.end()
        || key.instance >= groundProof.instances.size()) {
      error = "ground choice prooftrans references an unknown node or instance";
      return false;
    }
    state[key] = 1;
    if (std::getenv("MEGALODON_CERT_DEBUG")
        && state.size() % 100 == 0) {
      std::cerr << "megalodon ground choice phase: entered nodes="
                << state.size() << "; current=" << key.node
                << "; instance=" << key.instance << std::endl;
    }
    const ChoiceNode& node = *foundNode->second;

    const auto resolveParent = [&](const std::string& parent,
                                   ParentTarget& target) {
      return resolveParentForKey(key, parent, target);
    };

    std::map<std::string, PreservedSexpr> proofEnvironment =
      environments[key.instance];
    std::map<std::string, PreservedSexpr> inheritedBindings;
    std::set<std::string> conflictingInheritedBindings;
    for (const auto& parentEnvironment : parentEnvironments[key.instance]) {
      for (const auto& binding : parentEnvironment) {
        auto inherited = inheritedBindings.find(binding.first);
        if (inherited == inheritedBindings.end()) {
          inheritedBindings.emplace(binding.first, binding.second);
        } else if (!alphaEquivalentSexpr(
                     inherited->second, binding.second)) {
          conflictingInheritedBindings.insert(binding.first);
        }
      }
    }
    for (const auto& binding : inheritedBindings) {
      if (conflictingInheritedBindings.find(binding.first)
            != conflictingInheritedBindings.end()) {
        continue;
      }
      auto local = proofEnvironment.find(binding.first);
      if (local == proofEnvironment.end()) {
        proofEnvironment.emplace(binding.first, binding.second);
      } else if (!alphaEquivalentSexpr(local->second, binding.second)) {
        error = "ground choice prooftrans received a parent-edge binding that conflicts with its child environment at "
          + node.step;
        return false;
      }
    }

    std::string rewriteFailure;
    std::function<bool(const PreservedSexpr&, PreservedSexpr&)> rewrite;
    rewrite = [&](const PreservedSexpr& input, PreservedSexpr& output) {
      std::vector<PreservedSexpr> arguments;
      const PreservedSexpr* base = &input;
      while (sexprHead(*base, "term_apply") && base->items.size() == 3) {
        arguments.push_back(base->items[2]);
        base = &base->items[1];
      }
      if (sexprHead(*base, "parent") && base->items.size() == 2) {
        std::string parent;
        if (!preservedName(base->items[1], parent)) {
          rewriteFailure = "parent has no preserved name";
          return false;
        }
        rewriteFailure = "entered parent " + parent;
        ParentTarget target;
        if (!resolveParent(parent, target)) return false;
        rewriteFailure = "resolved parent " + parent;
        if (target.generated && !emit(target.key)) {
          if (error.empty()) {
            rewriteFailure = "emitting parent " + parent
              + " returned false in state "
              + std::to_string(state[target.key]);
          }
          return false;
        }
        rewriteFailure = "emitted parent " + parent + " with "
          + std::to_string(arguments.size()) + " arguments";
        std::reverse(arguments.begin(), arguments.end());
        std::vector<PreservedSexpr> retainedArguments;
        if (target.generated) {
          const ChoiceNode& parentNode = *nodeById.at(target.key.node);
          const std::vector<bool> formulaBinders =
            formulaBinderSpecializations(parentNode, target.key.instance);
          const std::size_t parameterArguments = parentNode.parameters.size();
          const std::size_t suppliedFormulaArguments = std::min(
            formulaBinders.size(),
            arguments.size() > parameterArguments
              ? arguments.size() - parameterArguments : std::size_t(0));
          const std::size_t consumedArguments =
            parameterArguments + suppliedFormulaArguments;
          rewriteFailure = "parent " + parent + " has "
            + std::to_string(arguments.size()) + " supplied, "
            + std::to_string(parentNode.parameters.size())
            + " parameter, and " + std::to_string(formulaBinders.size())
            + " formula-binder arguments";
          if (arguments.size() < parameterArguments) {
            error = "ground choice prooftrans parent theorem application omits explicit parameters at "
              + node.step + " -> " + parent;
            return false;
          }
          // Parent bindings select erased theorem parameters.  Explicit
          // arguments live in the child proof context, extended only by
          // unambiguous bindings inherited from its selected ground parents.
          for (std::size_t index = 0;
               index < parentNode.parameters.size();
               ++index) {
            PreservedSexpr argument = specializeWithEnvironment(
              arguments[index], proofEnvironment);
            const std::string& parameter = parentNode.parameters[index].first;
            const auto& parentEnvironment = environments[target.key.instance];
            auto binding = parentEnvironment.find(parameter);
            if (binding == parentEnvironment.end()) {
              retainedArguments.push_back(std::move(argument));
            }
          }
          for (std::size_t index = 0;
               index < suppliedFormulaArguments;
               ++index) {
            PreservedSexpr argument = specializeWithEnvironment(
              arguments[parentNode.parameters.size() + index],
              proofEnvironment);
            if (!formulaBinders[index]) {
              retainedArguments.push_back(std::move(argument));
            }
          }
          for (std::size_t index = consumedArguments;
               index < arguments.size();
               ++index) {
            PreservedSexpr argument = specializeWithEnvironment(
              arguments[index], proofEnvironment);
            retainedArguments.push_back(std::move(argument));
          }
        } else {
          for (const PreservedSexpr& argument : arguments) {
            retainedArguments.push_back(specializeWithEnvironment(
              argument, proofEnvironment));
          }
        }
        if (!parser.parse(
              "(parent " + quotePreservedName(target.rendered) + ")",
              output)) {
          rewriteFailure = "cannot render rewritten parent " + target.rendered;
          return false;
        }
        for (const PreservedSexpr& argument : retainedArguments) {
          PreservedSexpr applied;
          if (!parser.parse(
                "(term_apply " + output.render() + " "
                + argument.render() + ")", applied)) {
            rewriteFailure = "cannot render an argument of parent "
              + target.rendered;
            return false;
          }
          output = std::move(applied);
        }
        rewriteFailure.clear();
        return true;
      }
      if (input.atom) {
        output = input;
        return true;
      }
      output = {};
      output.atom = false;
      output.items.reserve(input.items.size());
      if (!input.items.empty()) {
        output.items.push_back(input.items.front());
      }
      for (std::size_t index = 1; index < input.items.size(); ++index) {
        PreservedSexpr rewrittenChild;
        if (!rewrite(input.items[index], rewrittenChild)) {
          if (rewriteFailure.empty()) {
            rewriteFailure = "cannot rewrite proof child "
              + std::to_string(index) + " of " + input.items[0].token
              + ": " + input.items[index].render().substr(0, 800);
          }
          return false;
        }
        output.items.push_back(std::move(rewrittenChild));
      }
      return true;
    };

    PreservedSexpr conclusion;
    PreservedSexpr proof;
    const std::string& conclusionText = node.hasResultClause
      ? node.resultClause : node.resultFormula;
    const bool hasIvyJustification =
      node.ivyJustification.rule != IvyRule::None;
    const bool needsDirectProof = !hasIvyJustification
      || node.producerCnfProjection != nullptr;
    if (node.hasResultClause == node.hasResultFormula
        || !parser.parse(conclusionText, conclusion)
        || (needsDirectProof
            && !parser.parse(node.producerProof, proof))) {
      error = "ground choice prooftrans cannot parse node " + node.step;
      return false;
    }
    if (needsDirectProof) {
      proof = normalizePrivateProofReferences(
        node, proof, normalizePrivateProofReferences);
      proof = normalizeProducerTerms(
        std::move(proof), normalizeProducerTerms);
    }
    conclusion = node.hasResultFormula
      ? specializeLeadingBindersWithEnvironment(
          std::move(conclusion), proofEnvironment, "ALLV")
      : specializeWithEnvironment(
          std::move(conclusion), proofEnvironment);
    const auto specializeProofLeadingBinders = [&]
      (PreservedSexpr value) {
      return specializeLeadingBindersWithEnvironment(
        std::move(value), proofEnvironment, "term_lambda");
    };
    PreservedSexpr rewrittenProof;
    PreservedSexpr rewrittenDirectProof;
    std::vector<PreservedSexpr> rewrittenParentApplications;
    std::map<std::string, PreservedSexpr> inferenceRefinements;
    if (hasIvyJustification && needsDirectProof) {
      PreservedSexpr directProof = specializeProofLeadingBinders(proof);
      if (!rewrite(directProof, rewrittenDirectProof)) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon ground direct-proof rewrite failed at "
                    << node.step << ": " << rewriteFailure << std::endl;
        }
        if (error.empty()) {
          error = "ground choice prooftrans cannot rewrite the producer-expanded compact proof at "
            + node.step;
        }
        return false;
      }
      rewrittenDirectProof = betaNormalizeSexpr(rewrittenDirectProof);
    }
    ParentTarget compactParent;
    if (node.ivyJustification.rule == IvyRule::Copy) {
      if (node.ivyJustification.parents.size() != 1) {
        error = "ground choice prooftrans cannot specialize compact copy node "
          + node.step;
        return false;
      }
      if (!resolveParent(
            node.ivyJustification.parents.front(), compactParent)) {
        return false;
      }
      if (compactParent.generated && !emit(compactParent.key)) {
        return false;
      }
    } else if (node.ivyJustification.rule == IvyRule::Instantiate) {
      if (node.ivyJustification.parents.size() != 1
          || node.ivyJustification.terms.empty()
          || !parser.parse(
               "(parent "
                 + quotePreservedName(node.ivyJustification.parents.front())
                 + ")",
               proof)) {
        error = "ground choice prooftrans cannot parse compact instantiation at "
          + node.step;
        return false;
      }
      for (const std::string& argumentText : node.ivyJustification.terms) {
        PreservedSexpr argument;
        PreservedSexpr applied;
        if (!parser.parse(argumentText, argument)
            || !parser.parse(
                 "(term_apply " + proof.render() + " "
                   + argument.render() + ")",
                 applied)) {
          error = "ground choice prooftrans cannot parse compact instantiation argument at "
            + node.step;
          return false;
        }
        proof = std::move(applied);
      }
      if (!rewrite(proof, rewrittenProof)) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon ground rewrite failed at " << node.step
                    << ": " << rewriteFailure << std::endl;
        }
        if (error.empty()) {
          error = "ground choice prooftrans cannot specialize compact instantiation at "
            + node.step;
        }
        return false;
      }
    } else if (node.ivyJustification.rule == IvyRule::Resolve) {
      if (node.ivyJustification.parents.size() != 2
          || node.ivyJustification.indices.size() != 2
          || node.ivyJustification.parentArguments.size() != 2) {
        error = "ground choice prooftrans received malformed compact resolution at "
          + node.step;
        return false;
      }
      for (std::size_t side = 0; side < 2; ++side) {
        PreservedSexpr application;
        if (!parser.parse(
              "(parent "
                + quotePreservedName(node.ivyJustification.parents[side])
                + ")",
              application)) {
          return false;
        }
        for (const std::string& argumentText
             : node.ivyJustification.parentArguments[side]) {
          PreservedSexpr argument;
          PreservedSexpr applied;
          if (!parser.parse(argumentText, argument)
              || !parser.parse(
                   "(term_apply " + application.render() + " "
                     + argument.render() + ")",
                   applied)) {
            error = "ground choice prooftrans cannot parse compact resolution argument at "
              + node.step;
            return false;
          }
          application = std::move(applied);
        }
        PreservedSexpr rewritten;
        if (!rewrite(application, rewritten)) {
          if (error.empty()) {
            error = "ground choice prooftrans cannot specialize compact resolution at "
              + node.step;
          }
          return false;
        }
        rewrittenParentApplications.push_back(std::move(rewritten));
      }
      std::vector<std::string> concreteParents(2);
      std::vector<std::vector<std::string>> concreteArguments(2);
      const auto decomposeApplication = [&]
        (const PreservedSexpr& application,
         std::string& parent,
         std::vector<std::string>& arguments) {
        const PreservedSexpr* current = &application;
        while (sexprHead(*current, "term_apply")
               && current->items.size() == 3) {
          arguments.push_back(current->items[2].render());
          current = &current->items[1];
        }
        if (!sexprHead(*current, "parent")
            || current->items.size() != 2
            || !preservedName(current->items[1], parent)) {
          return false;
        }
        std::reverse(arguments.begin(), arguments.end());
        return true;
      };
      for (std::size_t side = 0; side < 2; ++side) {
        if (!decomposeApplication(
              rewrittenParentApplications[side],
              concreteParents[side], concreteArguments[side])) {
          error = "ground choice prooftrans cannot expose a compact resolution parent at "
            + node.step;
          return false;
        }
      }
      const auto concreteNode = [&](const std::string& step) -> const ChoiceNode* {
        auto found = resultNodeIndex.find(step);
        return found == resultNodeIndex.end()
          || found->second >= result.nodes.size()
          ? nullptr : &result.nodes[found->second];
      };
      const ChoiceNode* leftNode = concreteNode(concreteParents[0]);
      const ChoiceNode* rightNode = concreteNode(concreteParents[1]);
      if (leftNode == nullptr
          || rightNode == nullptr
          || !refineResolutionArguments(
               *leftNode,
               concreteArguments[0], node.ivyJustification.indices[0],
               *rightNode,
               concreteArguments[1], node.ivyJustification.indices[1],
               node.parameters, &inferenceRefinements)) {
        error = "ground choice prooftrans cannot make the declared compact resolution pivots complementary at "
          + node.step;
        return false;
      }
      for (std::size_t side = 0; side < 2; ++side) {
        PreservedSexpr application;
        if (!parser.parse(
              "(parent " + quotePreservedName(concreteParents[side]) + ")",
              application)) {
          return false;
        }
        for (const std::string& argumentText : concreteArguments[side]) {
          PreservedSexpr applied;
          if (!parser.parse(
                "(term_apply " + application.render() + " "
                  + argumentText + ")",
                applied)) {
            return false;
          }
          application = std::move(applied);
        }
        rewrittenParentApplications[side] = std::move(application);
      }
    } else if (node.ivyJustification.rule == IvyRule::Factor
               || node.ivyJustification.rule == IvyRule::EqualityResolution
               || node.ivyJustification.rule == IvyRule::EqualitySymmetry
               || node.ivyJustification.rule == IvyRule::TruthConflict) {
      const std::size_t expectedIndices =
        node.ivyJustification.rule == IvyRule::Factor ? 2 : 1;
      if (node.ivyJustification.parents.size() != 1
          || node.ivyJustification.indices.size() != expectedIndices
          || !parser.parse(
               "(parent "
                 + quotePreservedName(node.ivyJustification.parents.front())
                 + ")",
               proof)) {
        error = "ground choice prooftrans received malformed compact factor at "
          + node.step;
        return false;
      }
      for (const std::string& argumentText : node.ivyJustification.terms) {
        PreservedSexpr argument;
        PreservedSexpr applied;
        if (!parser.parse(argumentText, argument)
            || !parser.parse(
                 "(term_apply " + proof.render() + " "
                   + argument.render() + ")",
                 applied)) {
          error = "ground choice prooftrans cannot parse compact factor argument at "
            + node.step;
          return false;
        }
        proof = std::move(applied);
      }
      if (!rewrite(proof, rewrittenProof)) {
        if (error.empty()) {
          error = "ground choice prooftrans cannot specialize compact factor at "
            + node.step;
        }
        return false;
      }
    } else if (node.ivyJustification.rule == IvyRule::Paramodulate) {
      if (node.ivyJustification.parents.size() != 2
          || node.ivyJustification.indices.size() != 3
          || node.ivyJustification.parentArguments.size() != 2) {
        error = "ground choice prooftrans received malformed compact paramodulation at "
          + node.step;
        return false;
      }
      for (std::size_t side = 0; side < 2; ++side) {
        PreservedSexpr application;
        if (!parser.parse(
              "(parent "
                + quotePreservedName(node.ivyJustification.parents[side])
                + ")",
              application)) {
          return false;
        }
        for (const std::string& argumentText
             : node.ivyJustification.parentArguments[side]) {
          PreservedSexpr argument;
          PreservedSexpr applied;
          if (!parser.parse(argumentText, argument)
              || !parser.parse(
                   "(term_apply " + application.render() + " "
                     + argument.render() + ")",
                   applied)) {
            error = "ground choice prooftrans cannot parse compact paramodulation argument at "
              + node.step;
            return false;
          }
          application = std::move(applied);
        }
        PreservedSexpr rewritten;
        if (!rewrite(application, rewritten)) {
          if (error.empty()) {
            error = "ground choice prooftrans cannot specialize compact paramodulation at "
              + node.step;
          }
          return false;
        }
        rewrittenParentApplications.push_back(std::move(rewritten));
      }
    } else {
      proof = specializeProofLeadingBinders(std::move(proof));
      if (!rewrite(proof, rewrittenProof)) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon ground rewrite failed at " << node.step
                    << ": " << rewriteFailure << std::endl;
        }
        if (error.empty()) {
          error = "ground choice prooftrans cannot rewrite node " + node.step;
        }
        return false;
      }
      rewrittenProof = betaNormalizeSexpr(rewrittenProof);
    }

    for (const auto& binding : inferenceRefinements) {
      const auto existing = proofEnvironment.find(binding.first);
      if (existing != proofEnvironment.end()
          && !alphaEquivalentSexpr(existing->second, binding.second)) {
        error = "ground choice prooftrans inferred conflicting compact resolution instances at "
          + node.step;
        return false;
      }
      proofEnvironment.emplace(binding.first, binding.second);
    }
    if (!inferenceRefinements.empty()) {
      conclusion = specializeWithEnvironment(
        std::move(conclusion), inferenceRefinements);
      if (hasIvyJustification && needsDirectProof) {
        rewrittenDirectProof = specializeWithEnvironment(
          std::move(rewrittenDirectProof), inferenceRefinements);
        rewrittenDirectProof = betaNormalizeSexpr(rewrittenDirectProof);
      }
    }

    ChoiceNode rendered;
    rendered.index = result.nodes.size();
    rendered.step = groundId(key.instance, node.step);
    rendered.hasProducerGroundOrigin = true;
    rendered.producerGroundSourceNode = node.step;
    rendered.producerGroundSourceInstance = key.instance;
    rendered.parameters = retainedParameters(node, proofEnvironment);
    rendered.hasResultClause = node.hasResultClause;
    rendered.hasResultFormula = node.hasResultFormula;
    if (rendered.hasResultClause) rendered.resultClause = conclusion.render();
    if (rendered.hasResultFormula) rendered.resultFormula = conclusion.render();
    if (node.producerCnfProjection != nullptr) {
      rendered.producerCnfProjection = std::make_shared<
        MegalodonKernelSyntax::RenderedKernelCnfProjection>(
          *node.producerCnfProjection);
      std::function<bool(
        MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
        specializeProjection;
      specializeProjection = [&](auto& item) {
        const auto specializeField = [&](auto& field) {
          PreservedSexpr value;
          if (!parser.parse(field.sexpr, value)) return false;
          value = specialize(std::move(value), key.instance);
          value = normalizeProducerTerms(value, normalizeProducerTerms);
          field.sexpr = value.render();
          return true;
        };
        if (item.hasWitnessTerm && !specializeField(item.witnessTerm)) {
          return false;
        }
        if (item.hasSourceLiteral && !specializeField(item.sourceLiteral)) {
          return false;
        }
        for (auto& child : item.children) {
          if (!specializeProjection(child)) return false;
        }
        return true;
      };
      PreservedSexpr cnfSource;
      if (!specializeProjection(*rendered.producerCnfProjection)
          || !parser.parse(node.producerCnfSourceFormula, cnfSource)) {
        error = "ground choice prooftrans cannot specialize CNF projection at "
          + node.step;
        return false;
      }
      std::function<bool(
        PreservedSexpr&,
        MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
        specializeProjectionSource;
      specializeProjectionSource = [&](PreservedSexpr& formula,
                                        auto& projection) {
        if (!sexprHead(formula, "ALLV") || formula.items.size() != 4) {
          formula = specialize(std::move(formula), key.instance);
          return true;
        }
        std::string variable;
        if (!preservedName(formula.items[1], variable)
            || projection.kind != "forall"
            || !projection.hasVariable
            || projection.variable != variable
            || projection.children.size() != 1) {
          return false;
        }
        const auto binding = environments[key.instance].find(variable);
        if (binding != environments[key.instance].end()) {
          if (!projection.hasWitnessTerm) return false;
          PreservedSexpr witness;
          if (!parser.parse(projection.witnessTerm.sexpr, witness)
              || !alphaEquivalentSexpr(witness, binding->second)) {
            return false;
          }
          formula = substituteNamedVariableSexpr(
            formula.items[3], variable, binding->second);
          projection = std::move(projection.children[0]);
          return specializeProjectionSource(formula, projection);
        }
        if (!specializeProjectionSource(
              formula.items[3], projection.children[0])) {
          return false;
        }
        return true;
      };
      if (!specializeProjectionSource(
            cnfSource, *rendered.producerCnfProjection)) {
        error = "ground choice prooftrans cannot synchronize CNF projection specialization at "
          + node.step;
        return false;
      }
      rendered.producerCnfSourceFormula = cnfSource.render();
    }
    rendered.ivyJustification = node.ivyJustification;
    if (hasIvyJustification) {
      rendered.producerProof = rewrittenDirectProof.render();
      if (node.ivyJustification.rule == IvyRule::Copy) {
        rendered.parents = {compactParent.rendered};
        rendered.ivyJustification.parents = rendered.parents;
      } else if (node.ivyJustification.rule == IvyRule::Instantiate) {
        const PreservedSexpr* current = &rewrittenProof;
        std::vector<std::string> arguments;
        while (sexprHead(*current, "term_apply")
               && current->items.size() == 3) {
          arguments.push_back(current->items[2].render());
          current = &current->items[1];
        }
        std::string parent;
        if (!sexprHead(*current, "parent")
            || current->items.size() != 2
            || !preservedName(current->items[1], parent)) {
          error = "ground choice prooftrans cannot normalize compact instantiation at "
            + node.step;
          return false;
        }
        std::reverse(arguments.begin(), arguments.end());
        rendered.parents = {parent};
        rendered.ivyJustification.parents = rendered.parents;
        rendered.ivyJustification.terms = std::move(arguments);
        if (rendered.ivyJustification.terms.empty()) {
          rendered.ivyJustification.rule = IvyRule::Copy;
        }
      } else if (node.ivyJustification.rule == IvyRule::Resolve) {
        std::set<std::string> parents;
        rendered.ivyJustification.parents.clear();
        rendered.ivyJustification.parentArguments.clear();
        for (const PreservedSexpr& application
             : rewrittenParentApplications) {
          const PreservedSexpr* current = &application;
          std::vector<std::string> arguments;
          while (sexprHead(*current, "term_apply")
                 && current->items.size() == 3) {
            arguments.push_back(current->items[2].render());
            current = &current->items[1];
          }
          std::string parent;
          if (!sexprHead(*current, "parent")
              || current->items.size() != 2
              || !preservedName(current->items[1], parent)) {
            error = "ground choice prooftrans cannot normalize compact resolution at "
              + node.step;
            return false;
          }
          std::reverse(arguments.begin(), arguments.end());
          rendered.ivyJustification.parents.push_back(parent);
          rendered.ivyJustification.parentArguments.push_back(
            std::move(arguments));
          parents.insert(parent);
        }
        rendered.parents.assign(parents.begin(), parents.end());
      } else if (node.ivyJustification.rule == IvyRule::Factor
                 || node.ivyJustification.rule == IvyRule::EqualityResolution
                 || node.ivyJustification.rule == IvyRule::EqualitySymmetry
                 || node.ivyJustification.rule == IvyRule::TruthConflict) {
        const PreservedSexpr* current = &rewrittenProof;
        std::vector<std::string> arguments;
        while (sexprHead(*current, "term_apply")
               && current->items.size() == 3) {
          arguments.push_back(current->items[2].render());
          current = &current->items[1];
        }
        std::string parent;
        if (!sexprHead(*current, "parent")
            || current->items.size() != 2
            || !preservedName(current->items[1], parent)) {
          error = "ground choice prooftrans cannot normalize compact factor at "
            + node.step;
          return false;
        }
        std::reverse(arguments.begin(), arguments.end());
        rendered.parents = {parent};
        rendered.ivyJustification.parents = rendered.parents;
        rendered.ivyJustification.terms = std::move(arguments);
      } else if (node.ivyJustification.rule == IvyRule::Paramodulate) {
        std::set<std::string> parents;
        rendered.ivyJustification.parents.clear();
        rendered.ivyJustification.parentArguments.clear();
        for (const PreservedSexpr& application
             : rewrittenParentApplications) {
          const PreservedSexpr* current = &application;
          std::vector<std::string> arguments;
          while (sexprHead(*current, "term_apply")
                 && current->items.size() == 3) {
            arguments.push_back(current->items[2].render());
            current = &current->items[1];
          }
          std::string parent;
          if (!sexprHead(*current, "parent")
              || current->items.size() != 2
              || !preservedName(current->items[1], parent)) {
            error = "ground choice prooftrans cannot normalize compact paramodulation at "
              + node.step;
            return false;
          }
          std::reverse(arguments.begin(), arguments.end());
          rendered.ivyJustification.parents.push_back(parent);
          rendered.ivyJustification.parentArguments.push_back(
            std::move(arguments));
          parents.insert(parent);
        }
        PreservedSexpr position;
        PreservedSexpr from;
        PreservedSexpr to;
        if (!parser.parse(node.ivyJustification.position, position)
            || !parser.parse(node.ivyJustification.from, from)
            || !parser.parse(node.ivyJustification.to, to)) {
          error = "ground choice prooftrans cannot parse compact paramodulation payload at "
            + node.step;
          return false;
        }
        rendered.ivyJustification.position =
          specialize(std::move(position), key.instance).render();
        rendered.ivyJustification.from =
          specialize(std::move(from), key.instance).render();
        rendered.ivyJustification.to =
          specialize(std::move(to), key.instance).render();
        rendered.parents.assign(parents.begin(), parents.end());
      } else {
        std::set<std::string> parents;
        rendered.ivyJustification.parents.clear();
        for (const std::string& parent : node.ivyJustification.parents) {
          ParentTarget target;
          if (!resolveParent(parent, target)
              || (target.generated && !emit(target.key))) {
            error = "ground choice prooftrans cannot specialize compact parent at "
              + node.step;
            return false;
          }
          rendered.ivyJustification.parents.push_back(target.rendered);
          parents.insert(target.rendered);
        }
        rendered.parents.assign(parents.begin(), parents.end());
      }
    } else {
      rendered.producerProof = rewrittenProof.render();
      std::set<std::string> parents;
      collectProofParents(rewrittenProof, parents, collectProofParents);
      rendered.parents.assign(parents.begin(), parents.end());
    }

    const MegalodonKernelSyntax::RenderedKernelFiniteSkolemApplication*
      rootFiniteApplication = nullptr;
    if (node.hasRootExistsScope
        && node.rootExistsScopeWitnessType != "(SET)") {
      for (const auto& candidate : finiteProof.applications) {
        if (candidate.ownerInstance == key.instance
            && candidate.branchIndex == node.rootExistsScopeBranchIndex
            && candidate.witnessIndex == node.rootExistsScopeWitnessIndex) {
          if (rootFiniteApplication != nullptr) {
            error = "ground choice prooftrans found duplicate finite applications for scoped node "
              + node.step;
            return false;
          }
          rootFiniteApplication = &candidate;
        }
      }
    }
    const std::size_t macroApplicationCount =
      rootFiniteApplication == nullptr ? 0 : static_cast<std::size_t>(
      std::count_if(
        finiteProof.applications.begin(),
        finiteProof.applications.end(),
        [&](const auto& candidate) {
          return candidate.ownerInstance == key.instance
            && candidate.skolemStep.value
                 == rootFiniteApplication->skolemStep.value;
        }));
    const bool requiresAtomicChoiceReplay =
      forceAtomicFiniteReplay
      || rootFiniteApplication == nullptr
      || !rootFiniteApplication->hasProducerProgram
      || macroApplicationCount > 1
      || (rootFiniteApplication != nullptr
          && std::any_of(
        finiteProof.applications.begin(),
        finiteProof.applications.end(),
        [&](const auto& candidate) {
          return candidate.ownerInstance == key.instance
            && candidate.skolemStep.value
                 == rootFiniteApplication->skolemStep.value
            && std::any_of(
              candidate.producerChoiceDefinition.parameters.begin(),
              candidate.producerChoiceDefinition.parameters.end(),
              [&](const auto& parameter) {
                return environments[key.instance].find(parameter.first)
                  == environments[key.instance].end();
              });
        }));
    // A single ground witness is discharged by finite Smolka abstraction.
    // Multi-witness macros are replayed atomically so that one choice lambda
    // cannot be rewritten independently inside another witness definition.
    // The same atomic path handles witnesses below retained forall binders,
    // absent materialized finite applications, and repeated witness classes
    // that cannot be represented by properly nested independent finite scopes.
    if (node.hasRootExistsScope
        && node.rootExistsScopeWitnessType != "(SET)"
        && !requiresAtomicChoiceReplay) {
      const auto* finiteApplication = rootFiniteApplication;
      if (finiteApplication == nullptr
          || !finiteApplication->hasProducerProgram) {
        error = "ground choice prooftrans cannot locate the exact finite application for scoped node "
          + node.step;
        return false;
      }

      const auto parseNormalized = [&](const std::string& text,
                                       PreservedSexpr& value) {
        if (!parser.parse(text, value)) return false;
        value = normalizeProducerTerms(value, normalizeProducerTerms);
        return true;
      };
      PreservedSexpr programSource;
      PreservedSexpr programTarget;
      PreservedSexpr witness;
      PreservedSexpr leafSource;
      PreservedSexpr witnessType;
      if (!parseNormalized(
            finiteApplication->programSourceFormula.sexpr, programSource)
          || !parseNormalized(
            finiteApplication->programTargetFormula.sexpr, programTarget)
          || !parseNormalized(finiteApplication->term.sexpr, witness)
          || !parseNormalized(
            finiteApplication->programStageSourceFormula.sexpr, leafSource)
          || !parser.parse(node.rootExistsScopeWitnessType, witnessType)) {
        error = "ground choice prooftrans cannot parse the exact uniform scope program at "
          + node.step;
        return false;
      }

      struct ScopedPair {
        PreservedSexpr source;
        PreservedSexpr target;
        std::vector<std::size_t> path;
        std::vector<std::pair<std::string, std::string>> retainedAmbient;
      } scopedProgram;
      std::string scopedPairFailure;
      const auto specializeScopedPair = [&]
        (const PreservedSexpr& initialSource,
         const PreservedSexpr& initialTarget,
         ScopedPair& output) {
        output = {};
        std::size_t ambientIndex = 0;
        std::function<bool(
          const PreservedSexpr&,
          const PreservedSexpr&,
          std::size_t,
          PreservedSexpr&,
          PreservedSexpr&)>
          descend;
        descend = [&](const PreservedSexpr& currentSource,
                      const PreservedSexpr& currentTarget,
                      std::size_t pathIndex,
                      PreservedSexpr& resultSource,
                      PreservedSexpr& resultTarget) {
          if (pathIndex == node.rootExistsScopePath.size()) {
            resultSource = specialize(currentSource, key.instance);
            resultTarget = specialize(currentTarget, key.instance);
            return true;
          }
          if (sexprHead(currentSource, "ALLV")
              && currentSource.items.size() == 4
              && sexprHead(currentTarget, "ALLV")
              && currentTarget.items.size() == 4) {
            std::string sourceName;
            std::string targetName;
            if (node.rootExistsScopePath[pathIndex] != 0
                || ambientIndex >= node.rootExistsScopeAmbient.size()
                || !preservedName(currentSource.items[1], sourceName)
                || !preservedName(currentTarget.items[1], targetName)
                || sourceName != targetName
                || sourceName
                   != node.rootExistsScopeAmbient[ambientIndex].first
                || currentSource.items[2] != currentTarget.items[2]
                || currentSource.items[2].render()
                   != node.rootExistsScopeAmbient[ambientIndex].second) {
              scopedPairFailure = "forall frame "
                + std::to_string(pathIndex) + " does not match ambient "
                + std::to_string(ambientIndex);
              return false;
            }
            ++ambientIndex;
            const auto binding = environments[key.instance].find(sourceName);
            if (binding != environments[key.instance].end()) {
              return descend(
                substituteNamedVariableSexpr(
                  currentSource.items[3], sourceName, binding->second),
                substituteNamedVariableSexpr(
                  currentTarget.items[3], targetName, binding->second),
                pathIndex + 1,
                resultSource,
                resultTarget);
            }
            resultSource = currentSource;
            resultTarget = currentTarget;
            output.path.push_back(0);
            output.retainedAmbient.push_back(
              node.rootExistsScopeAmbient[ambientIndex - 1]);
            return descend(
              currentSource.items[3],
              currentTarget.items[3],
              pathIndex + 1,
              resultSource.items[3],
              resultTarget.items[3]);
          }

          PreservedSexpr sourceLeft;
          PreservedSexpr sourceRight;
          PreservedSexpr targetLeft;
          PreservedSexpr targetRight;
          const bool sourceAnd = binaryNamedApplicationSexpr(
            currentSource, "vampire_and", sourceLeft, sourceRight);
          const bool targetAnd = binaryNamedApplicationSexpr(
            currentTarget, "vampire_and", targetLeft, targetRight);
          const bool sourceOr = !sourceAnd && binaryNamedApplicationSexpr(
            currentSource, "vampire_or", sourceLeft, sourceRight);
          const bool targetOr = !targetAnd && binaryNamedApplicationSexpr(
            currentTarget, "vampire_or", targetLeft, targetRight);
          const std::size_t branch = node.rootExistsScopePath[pathIndex];
          if (branch > 1
              || sourceAnd != targetAnd || sourceOr != targetOr
              || (!sourceAnd && !sourceOr)) {
            scopedPairFailure = "junction frame "
              + std::to_string(pathIndex) + " does not match both formulas";
            return false;
          }
          resultSource = specialize(currentSource, key.instance);
          resultTarget = specialize(currentTarget, key.instance);
          output.path.push_back(branch);
          PreservedSexpr& sourceChild = branch == 0
            ? resultSource.items[1].items[2] : resultSource.items[2];
          PreservedSexpr& targetChild = branch == 0
            ? resultTarget.items[1].items[2] : resultTarget.items[2];
          return descend(
            branch == 0 ? sourceLeft : sourceRight,
            branch == 0 ? targetLeft : targetRight,
            pathIndex + 1,
            sourceChild,
            targetChild);
        };
        const bool matched = descend(
          initialSource,
          initialTarget,
          0,
          output.source,
          output.target);
        if (matched
            && ambientIndex != node.rootExistsScopeAmbient.size()) {
          scopedPairFailure = "path consumed "
            + std::to_string(ambientIndex) + " of "
            + std::to_string(node.rootExistsScopeAmbient.size())
            + " ambient binders";
          return false;
        }
        return matched;
      };
      const bool sourcePathMatched = specializeScopedPair(
        programSource, programTarget, scopedProgram);
      const std::string sourcePathFailure = scopedPairFailure;
      if (!sourcePathMatched) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon exact uniform path mismatch at "
                    << node.step
                    << "\n  source path: " << sourcePathMatched
                    << " " << sourcePathFailure
                    << "\n  path length: "
                    << node.rootExistsScopePath.size()
                    << "\n  ambient length: "
                    << node.rootExistsScopeAmbient.size()
                    << std::endl;
        }
        error = "ground choice prooftrans exact uniform path does not match its producer formulas at "
          + node.step;
        return false;
      }
      witness = specialize(std::move(witness), key.instance);
      leafSource = specialize(std::move(leafSource), key.instance);

      PreservedSexpr declaredWitness;
      if (!parser.parse(node.rootExistsScopeWitnessTerm, declaredWitness)) {
        error = "ground choice prooftrans cannot parse declared scoped witness at "
          + node.step;
        return false;
      }
      declaredWitness = specializeLeadingBinders(
        normalizeProducerTerms(
          declaredWitness, normalizeProducerTerms),
        key.instance,
        "LAMV");
      if (witness != declaredWitness
          || !rendered.hasResultFormula) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon uniform scope metadata mismatch at "
                    << node.step
                    << "\n  witness: " << witness.render()
                    << "\n  declared witness: " << declaredWitness.render()
                    << "\n  contextual target: " << scopedProgram.target.render()
                    << "\n  exact Vampire claim: " << rendered.resultFormula
                    << std::endl;
        }
        error = "ground choice prooftrans uniform scope metadata differs from its grounded claim at "
          + node.step;
        return false;
      }

      if (node.parents.size() != 1) {
        error = "ground choice prooftrans uniform scope has no unique pre-Skolem parent at "
          + node.step;
        return false;
      }
      ParentTarget sourceParent;
      if (!resolveParent(node.parents.front(), sourceParent)
          || (sourceParent.generated && !emit(sourceParent.key))) {
        return false;
      }
      std::string sourceStep = sourceParent.rendered;
      PreservedSexpr sourceFormula = programSource;
      PreservedSexpr sourceProof;
      if (sourceParent.generated) {
        const auto sourceIndex = emittedIndex.find(sourceParent.key);
        if (sourceIndex == emittedIndex.end()
            || sourceIndex->second >= result.nodes.size()
            || !result.nodes[sourceIndex->second].hasResultFormula
            || !parser.parse(
                 result.nodes[sourceIndex->second].resultFormula,
                 sourceFormula)) {
          error = "ground choice prooftrans cannot locate the emitted pre-Skolem parent at "
            + node.step;
          return false;
        }
        sourceStep = result.nodes[sourceIndex->second].step;
      }
      if (!parser.parse(
            "(parent " + quotePreservedName(sourceStep) + ")",
            sourceProof)) {
        return false;
      }
      if (sourceFormula != scopedProgram.source) {
        MegalodonKernelSyntax::RenderedKernelFoolProgram sourceProgram;
        std::size_t nextIndex = 0;
        IvyClauseProofBuilder builder;
        std::string mappedProof;
        if (!buildFoolProgramNode(
              sourceFormula,
              scopedProgram.source,
              true,
              {},
              nextIndex,
              sourceProgram.root,
              &environments[key.instance])
            || !builder.foolFormulaProof(
                 sourceProgram, sourceProof.render(), mappedProof)
            || !parser.parse(mappedProof, sourceProof)) {
          error = "ground choice prooftrans cannot instantiate its exact external pre-Skolem parent at "
            + node.step;
          return false;
        }
        sourceFormula = scopedProgram.source;
      }
      if (sourceFormula != scopedProgram.source) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon uniform source mismatch at " << node.step
                    << "\n  program source: " << scopedProgram.source.render()
                    << "\n  parent source: "
                    << sourceFormula.render() << std::endl;
        }
        error = "ground choice prooftrans pre-Skolem parent differs from its exact uniform program at "
          + node.step;
        return false;
      }

      UniformSkolemScopeExpansion uniform;
      const std::string uniformId = std::to_string(key.instance)
        + "_" + std::to_string(finiteApplication->index);
      if (!expandUniformSkolemScope(
            uniformId,
            witnessType,
            witness,
            leafSource,
            scopedProgram.path,
            scopedProgram.source,
            scopedProgram.target,
            sourceProof,
            uniform,
            error)) {
        return false;
      }
      ChoiceNode support;
      support.index = result.nodes.size();
      support.step = groundId(key.instance, node.step)
        + "_uniform_scope_support";
      support.parents = {sourceStep};
      support.hasResultFormula = true;
      support.resultFormula = uniform.theorem.render();
      support.producerProof = uniform.proof.render();
      const std::string supportStep = support.step;
      resultNodeIndex.emplace(support.step, support.index);
      result.nodes.push_back(std::move(support));
      rendered.hasRootExistsScope = false;
      if (!pendingUniformScopes.emplace(
            rendered.step,
            PendingUniformScope{
              supportStep,
              node.rootExistsScopeWitnessType,
              witness,
              scopedProgram.target,
            }).second) {
        error = "ground choice prooftrans repeats a pending finite scope at "
          + rendered.step;
        return false;
      }
    }

    auto pending = pendingUniformScopes.end();
    for (const std::string& parent : rendered.parents) {
      auto candidate = pendingUniformScopes.find(parent);
      if (candidate == pendingUniformScopes.end()) continue;
      if (pending != pendingUniformScopes.end()) {
        error = "ground choice prooftrans consumer has multiple pending finite scopes at "
          + rendered.step;
        return false;
      }
      pending = candidate;
    }
    if (pending != pendingUniformScopes.end()) {
      if (!rendered.hasResultClause
          || rendered.producerCnfProjection == nullptr) {
        if (std::getenv("MEGALODON_CERT_DEBUG")) {
          std::cerr << "megalodon finite-scope formula consumer at "
                    << rendered.step
                    << "\n  pending parent: " << pending->first
                    << "\n  pending source: "
                    << pending->second.source.render()
                    << "\n  result formula: " << rendered.resultFormula
                    << "\n  producer proof: " << rendered.producerProof
                    << std::endl;
        }
        error = "ground choice prooftrans finite scope is not consumed by an exact CNF projection at "
          + rendered.step;
        return false;
      }
      PreservedSexpr clause;
      if (!parser.parse(rendered.resultClause, clause)
          || !sexprHead(clause, "clause")) {
        error = "ground choice prooftrans cannot parse finite-scope CNF result at "
          + rendered.step;
        return false;
      }
      std::vector<std::string> literals;
      std::vector<PreservedSexpr> literalFormulas;
      PreservedSexpr targetFormula;
      for (std::size_t index = 1; index < clause.items.size(); ++index) {
        const PreservedSexpr& literal = clause.items[index];
        if ((!sexprHead(literal, "pos") && !sexprHead(literal, "neg"))
            || literal.items.size() != 2) {
          error = "ground choice prooftrans has malformed finite-scope CNF literal at "
            + rendered.step;
          return false;
        }
        literals.push_back(literal.render());
        PreservedSexpr formula = literal.items[1];
        if (sexprHead(literal, "neg")) {
          PreservedSexpr falseFormula;
          if (!parser.parse("(TMH \"vampire_false\")", falseFormula)) {
            return false;
          }
          PreservedSexpr implication;
          if (!parser.parse(
                "(IMP " + formula.render() + " "
                  + falseFormula.render() + ")",
                implication)) {
            return false;
          }
          formula = std::move(implication);
        }
        literalFormulas.push_back(std::move(formula));
      }
      if (!literalFormulas.empty()) {
        targetFormula = literalFormulas.back();
        for (std::size_t index = literalFormulas.size() - 1;
             index > 0;
             --index) {
          PreservedSexpr disjunction;
          if (!parser.parse(
                "(AP (AP (TMH \"vampire_or\") "
                  + literalFormulas[index - 1].render() + ") "
                  + targetFormula.render() + ")",
                disjunction)) {
            return false;
          }
          targetFormula = std::move(disjunction);
        }
      }
      if (literals.empty()
          && !parser.parse("(TMH \"vampire_false\")", targetFormula)) {
        return false;
      }

      const std::string bridgeName = "ivy_ground_scope_bridge_"
        + std::to_string(key.instance);
      PreservedSexpr projectionSource;
      if (!parser.parse(
            rendered.producerCnfSourceFormula, projectionSource)) {
        error = "ground choice prooftrans cannot parse the exact CNF source at "
          + rendered.step;
        return false;
      }
      MegalodonKernelSyntax::RenderedKernelCnfProjection adaptedProjection;
      std::string projectionAdaptationFailure;
      const auto adaptationFailure = [&](const std::string& reason,
                                         const PreservedSexpr& original,
                                         const PreservedSexpr& contextual,
                                         const auto& projection) {
        if (projectionAdaptationFailure.empty()) {
          projectionAdaptationFailure = reason + " at " + projection.kind
            + "; original=" + original.render()
            + "; contextual=" + contextual.render();
        }
        return false;
      };
      std::function<bool(
        const PreservedSexpr&,
        const PreservedSexpr&,
        const MegalodonKernelSyntax::RenderedKernelCnfProjection&,
        MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
        adaptProjection;
      adaptProjection = [&](const PreservedSexpr& original,
                            const PreservedSexpr& contextual,
                            const auto& projection,
                            auto& adapted) {
        adapted = projection;
        if (!sexprHead(original, "ALLV")
            && sexprHead(contextual, "ALLV")
            && contextual.items.size() == 4) {
          std::string contextualName;
          if (!preservedName(contextual.items[1], contextualName)) {
            return adaptationFailure(
              "contextual forall has no variable",
              original, contextual, projection);
          }
          const auto binding = environments[key.instance].find(contextualName);
          if (binding == environments[key.instance].end()) {
            return adaptationFailure(
              "contextual forall has no producer ground binding",
              original, contextual, projection);
          }
          const PreservedSexpr contextualBody = substituteNamedVariableSexpr(
            contextual.items[3], contextualName, binding->second);
          adapted = {};
          adapted.kind = "forall";
          adapted.hasVariable = true;
          adapted.variable = contextualName;
          adapted.hasVariableType = true;
          adapted.variableType = MegalodonKernelSyntax::type(
            contextual.items[2].render());
          adapted.hasWitnessTerm = true;
          adapted.witnessTerm = MegalodonKernelSyntax::term(
            binding->second.render());
          adapted.children.resize(1);
          return adaptProjection(
            original,
            contextualBody,
            projection,
            adapted.children[0]);
        }
        if (projection.kind == "false") {
          const bool matches = projection.children.empty()
            && (namedTermSexpr(original, "vampire_false")
                || namedTermSexpr(original, "f__false"))
            && (namedTermSexpr(contextual, "vampire_false")
                || namedTermSexpr(contextual, "f__false"));
          return matches || adaptationFailure(
            "false-source mismatch", original, contextual, projection);
        }
        if (projection.kind == "literal") {
          if (projection.children.size() != 0
              || projection.resultLiteralIndex >= literals.size()) {
            return adaptationFailure(
              "malformed literal projection", original, contextual, projection);
          }
          PreservedSexpr expected;
          if (sexprHead(contextual, "IMP")
              && contextual.items.size() == 3
              && (namedTermSexpr(
                    contextual.items[2], "vampire_false")
                  || namedTermSexpr(contextual.items[2], "f__false"))) {
            expected = literalSexpr(false, contextual.items[1]);
          } else {
            expected = literalSexpr(true, contextual);
          }
          PreservedSexpr actualLiteral;
          if (!parser.parse(
                literals[projection.resultLiteralIndex], actualLiteral)
              || !alphaEquivalentSexpr(
                   betaNormalizeSexpr(expected),
                   betaNormalizeSexpr(actualLiteral))) {
            return adaptationFailure(
              "result literal mismatch: expected " + expected.render()
                + "; actual " + literals[projection.resultLiteralIndex],
              original, contextual, projection);
          }
          adapted.hasSourceLiteral = true;
          adapted.sourceLiteral =
            MegalodonKernelSyntax::literal(
              literals[projection.resultLiteralIndex]);
          return true;
        }
        if (projection.kind == "forall") {
          if (projection.children.size() != 1
              || !sexprHead(original, "ALLV")
              || original.items.size() != 4) {
            return adaptationFailure(
              "forall-source mismatch", original, contextual, projection);
          }
          std::string originalName;
          if (!preservedName(original.items[1], originalName)) return false;
          if (sexprHead(contextual, "ALLV")
              && contextual.items.size() == 4
              && original.items[2] == contextual.items[2]) {
            std::string contextualName;
            if (!preservedName(contextual.items[1], contextualName)) {
              return false;
            }
            PreservedSexpr witness;
            if (!projection.hasWitnessTerm
                || !parser.parse(projection.witnessTerm.sexpr, witness)) {
              return adaptationFailure(
                "retained forall projection lacks its Vampire witness",
                original, contextual, projection);
            }
            const PreservedSexpr originalBody =
              substituteNamedVariableSexpr(
                original.items[3], originalName, witness);
            const PreservedSexpr contextualBody =
              substituteNamedVariableSexpr(
                contextual.items[3], contextualName, witness);
            adapted.children.resize(1);
            return adaptProjection(
              originalBody,
              contextualBody,
              projection.children[0],
              adapted.children[0]);
          }
          PreservedSexpr witness;
          if (!projection.hasWitnessTerm
              || !parser.parse(projection.witnessTerm.sexpr, witness)) {
            return adaptationFailure(
              "forall projection lacks an explicit witness",
              original, contextual, projection);
          }
          const PreservedSexpr instantiated = substituteNamedVariableSexpr(
            original.items[3], originalName, witness);
          return adaptProjection(
            instantiated,
            contextual,
            projection.children[0],
            adapted);
        }
        PreservedSexpr originalLeft;
        PreservedSexpr originalRight;
        PreservedSexpr contextualLeft;
        PreservedSexpr contextualRight;
        if (projection.kind == "and_left"
            || projection.kind == "and_right") {
          if (projection.children.size() != 1
              || !binaryNamedApplicationSexpr(
                   original, "vampire_and",
                   originalLeft, originalRight)
              || !binaryNamedApplicationSexpr(
                   contextual, "vampire_and",
                   contextualLeft, contextualRight)) {
            return adaptationFailure(
              "conjunction-source mismatch", original, contextual, projection);
          }
          const bool left = projection.kind == "and_left";
          adapted.children.resize(1);
          return adaptProjection(
            left ? originalLeft : originalRight,
            left ? contextualLeft : contextualRight,
            projection.children[0],
            adapted.children[0]);
        }
        if (projection.kind == "or") {
          if (projection.children.size() != 2
              || !binaryNamedApplicationSexpr(
                   original, "vampire_or", originalLeft, originalRight)
              || !binaryNamedApplicationSexpr(
                   contextual, "vampire_or",
                   contextualLeft, contextualRight)) {
            return adaptationFailure(
              "disjunction-source mismatch", original, contextual, projection);
          }
          adapted.children.resize(2);
          return adaptProjection(
                   originalLeft,
                   contextualLeft,
                   projection.children[0],
                   adapted.children[0])
            && adaptProjection(
                 originalRight,
                 contextualRight,
                 projection.children[1],
                 adapted.children[1]);
        }
        return adaptationFailure(
          "unknown projection kind", original, contextual, projection);
      };
      if (!adaptProjection(
            projectionSource,
            pending->second.source,
            *rendered.producerCnfProjection,
            adaptedProjection)) {
        error = "ground choice prooftrans cannot adapt the exact CNF projection to its finite source at "
          + rendered.step + ": " + projectionAdaptationFailure;
        return false;
      }
      std::function<bool(
        MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
        normalizeAdaptedProjection;
      normalizeAdaptedProjection = [&](auto& item) {
        const auto normalizeField = [&](auto& field) {
          PreservedSexpr value;
          if (!parser.parse(field.sexpr, value)) return false;
          field.sexpr = betaNormalizeSexpr(value).render();
          return true;
        };
        if (item.hasWitnessTerm && !normalizeField(item.witnessTerm)) {
          return false;
        }
        if (item.hasSourceLiteral && !normalizeField(item.sourceLiteral)) {
          return false;
        }
        for (auto& child : item.children) {
          if (!normalizeAdaptedProjection(child)) return false;
        }
        return true;
      };
      std::vector<std::string> bridgeLiterals;
      bridgeLiterals.reserve(literals.size());
      for (const std::string& literal : literals) {
        PreservedSexpr parsedLiteral;
        if (!parser.parse(literal, parsedLiteral)) return false;
        bridgeLiterals.push_back(betaNormalizeSexpr(parsedLiteral).render());
      }
      PreservedSexpr bridgeSource = betaNormalizeSexpr(pending->second.source);
      PreservedSexpr bridgeTarget = betaNormalizeSexpr(targetFormula);
      PreservedSexpr bridgeWitness = betaNormalizeSexpr(pending->second.witness);
      if (!normalizeAdaptedProjection(adaptedProjection)) {
        error = "ground choice prooftrans cannot normalize its exact finite CNF projection at "
          + rendered.step;
        return false;
      }
      const std::string witnessBinder = "ivy_scope_w_"
        + std::to_string(key.instance) + "_"
        + std::to_string(rendered.index);
      PreservedSexpr witnessVariable;
      if (!parser.parse(
            "(TMH " + quotePreservedName(witnessBinder) + ")",
            witnessVariable)) {
        return false;
      }
      std::size_t witnessReplacements = 0;
      PreservedSexpr abstractBridgeSource = replaceExactSexpr(
        bridgeSource, bridgeWitness, witnessVariable, witnessReplacements);
      PreservedSexpr abstractBridgeTarget = replaceExactSexpr(
        bridgeTarget, bridgeWitness, witnessVariable, witnessReplacements);
      std::vector<std::string> abstractBridgeLiterals;
      abstractBridgeLiterals.reserve(bridgeLiterals.size());
      for (const std::string& literalText : bridgeLiterals) {
        PreservedSexpr literal;
        if (!parser.parse(literalText, literal)) return false;
        abstractBridgeLiterals.push_back(
          replaceExactSexpr(
            literal, bridgeWitness, witnessVariable, witnessReplacements)
            .render());
      }
      auto abstractProjection = adaptedProjection;
      std::function<bool(
        MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
        abstractProjectionTerms;
      abstractProjectionTerms = [&](auto& item) {
        const auto abstractField = [&](auto& field) {
          PreservedSexpr value;
          if (!parser.parse(field.sexpr, value)) return false;
          field.sexpr = replaceExactSexpr(
            value, bridgeWitness, witnessVariable, witnessReplacements).render();
          return true;
        };
        if (item.hasWitnessTerm && !abstractField(item.witnessTerm)) return false;
        if (item.hasSourceLiteral && !abstractField(item.sourceLiteral)) return false;
        for (auto& child : item.children) {
          if (!abstractProjectionTerms(child)) return false;
        }
        return true;
      };
      if (!abstractProjectionTerms(abstractProjection)
          || witnessReplacements == 0) {
        error = "ground choice prooftrans cannot abstract its exact finite witness at "
          + rendered.step;
        return false;
      }
      IvyClauseProofBuilder builder;
      std::string bridgeBody;
      if (!builder.cnfFormulaClauseProof(
            "(hyp " + quotePreservedName(bridgeName) + ")",
            abstractBridgeSource.render(),
            abstractProjection,
            abstractBridgeLiterals,
            bridgeBody)) {
        error = "ground choice prooftrans cannot replay the exact CNF projection from its finite scope at "
          + rendered.step;
        return false;
      }
      std::string closedConcreteTarget = bridgeTarget.render();
      std::string closedAbstractTarget = abstractBridgeTarget.render();
      std::string closedBridgeBody = bridgeBody;
      std::string closedConcreteProof = rendered.producerProof;
      for (auto parameter = rendered.parameters.rbegin();
           parameter != rendered.parameters.rend(); ++parameter) {
        closedConcreteTarget = "(ALLV "
          + quotePreservedName(parameter->first) + " " + parameter->second
          + " " + closedConcreteTarget + ")";
        closedAbstractTarget = "(ALLV "
          + quotePreservedName(parameter->first) + " " + parameter->second
          + " " + closedAbstractTarget + ")";
        closedBridgeBody = "(term_lambda "
          + quotePreservedName(parameter->first) + " " + parameter->second
          + " " + closedBridgeBody + ")";
        closedConcreteProof = "(term_lambda "
          + quotePreservedName(parameter->first) + " " + parameter->second
          + " " + closedConcreteProof + ")";
      }
      const std::string bridgeProof = "(proof_lambda "
        + quotePreservedName(bridgeName) + " (formula "
        + abstractBridgeSource.render() + ") " + closedBridgeBody + ")";
      PreservedSexpr parsedBridge;
      if (!parser.parse(bridgeProof, parsedBridge)) return false;

      ChoiceNode boundary;
      boundary.index = result.nodes.size();
      boundary.step = rendered.step + "_finite_scope_boundary";
      boundary.parents = rendered.parents;
      boundary.parents.push_back(pending->second.supportStep);
      std::sort(boundary.parents.begin(), boundary.parents.end());
      boundary.parents.erase(
        std::unique(boundary.parents.begin(), boundary.parents.end()),
        boundary.parents.end());
      boundary.hasResultFormula = true;
      boundary.resultFormula = closedConcreteTarget;
      boundary.producerProof = closedConcreteProof;
      boundary.hasRootExistsScope = true;
      boundary.rootExistsScopeAbstract = true;
      boundary.rootExistsScopeParent = pending->second.supportStep;
      boundary.rootExistsScopeWitnessType = pending->second.witnessType;
      boundary.rootExistsScopeWitnessBinder = witnessBinder;
      boundary.rootExistsScopeWitnessTerm = bridgeWitness.render();
      boundary.rootExistsScopeSourceFormula = abstractBridgeSource.render();
      boundary.rootExistsScopeTargetFormula = closedAbstractTarget;
      boundary.rootExistsScopeBridgeProof = parsedBridge.render();
      boundary.rootExistsScopeSourceStep = pending->first;
      resultNodeIndex.emplace(boundary.step, boundary.index);
      result.nodes.push_back(std::move(boundary));

      rendered.parents = {rendered.step + "_finite_scope_boundary"};
      rendered.producerProof = "(parent "
        + quotePreservedName(rendered.parents.front()) + ")";
      for (const auto& parameter : rendered.parameters) {
        rendered.producerProof = "(term_apply " + rendered.producerProof
          + " (term (TMH " + quotePreservedName(parameter.first) + ")))";
      }
      rendered.ivyJustification = {};
      rendered.producerCnfProjection.reset();
      rendered.producerCnfSourceFormula.clear();
      rendered.rootExistsScopeBoundaryCopy = true;
      rendered.hasProducerGroundOrigin = false;
      rendered.producerGroundSourceNode.clear();
      rendered.producerGroundSourceInstance = 0;
      pendingUniformScopes.erase(pending);
    }
    rendered.index = result.nodes.size();
    emittedIndex.emplace(key, rendered.index);
    resultNodeIndex.emplace(rendered.step, rendered.index);
    result.nodes.push_back(std::move(rendered));
    state[key] = 2;
    return true;
  };

  const Key root = {source.finalStep, 0};
  const bool certificateDebug =
    std::getenv("MEGALODON_CERT_DEBUG") != nullptr
    || std::getenv("MEGALODON_CERT_PROFILE") != nullptr;
  const auto certificateProfileStart = std::chrono::steady_clock::now();
  const auto certificateProfileMilliseconds = [&]() {
    return std::chrono::duration_cast<std::chrono::milliseconds>(
      std::chrono::steady_clock::now() - certificateProfileStart).count();
  };
  if (certificateDebug) {
    std::cerr << "megalodon ground choice phase: emit reachable DAG"
              << std::endl;
  }
  if (!emit(root)) return false;
  if (certificateDebug) {
    std::cerr << "megalodon ground choice phase: reachable DAG complete; nodes="
              << result.nodes.size() << std::endl;
  }

  std::map<std::pair<std::string, std::string>, bool>
    nodeExactTermContainment;
  std::map<std::string, std::vector<std::string>>
    requiredNamedTermsByNeedle;
  const auto nodeContainsExactTerm = [&]
    (const ChoiceNode& node, const PreservedSexpr& needle) {
    const PreservedSexpr& normalizedNeedle = needle;
    const std::string needleKey = normalizedNeedle.render();
    const auto cacheKey = std::make_pair(
      node.step, needleKey);
    auto cached = nodeExactTermContainment.find(cacheKey);
    if (cached != nodeExactTermContainment.end()) return cached->second;
    auto required = requiredNamedTermsByNeedle.find(needleKey);
    if (required == requiredNamedTermsByNeedle.end()) {
      std::set<std::string> names;
      const auto collectNames = [&]
        (const PreservedSexpr& value, const auto& self) -> void {
        if (sexprHead(value, "TMH") && value.items.size() == 2) {
          std::string name;
          if (preservedName(value.items[1], name)) {
            names.insert(quotePreservedName(name));
          }
          return;
        }
        if (value.atom) return;
        for (std::size_t index = 1; index < value.items.size(); ++index) {
          self(value.items[index], self);
        }
      };
      collectNames(normalizedNeedle, collectNames);
      required = requiredNamedTermsByNeedle.emplace(
        needleKey,
        std::vector<std::string>(names.begin(), names.end())).first;
    }
    const auto contains = [&](const std::string& text) {
      for (const std::string& requiredName : required->second) {
        if (text.find(requiredName) == std::string::npos) return false;
      }
      PreservedSexpr value;
      if (text.empty() || !parser.parse(text, value)) return false;
      return containsAlphaEquivalent(value, normalizedNeedle);
    };
    bool resultContains = false;
    if (contains(node.resultClause) || contains(node.resultFormula)
        || contains(node.producerCnfSourceFormula)
        || contains(node.ivyJustification.position)
        || contains(node.ivyJustification.from)
        || contains(node.ivyJustification.to)) {
      resultContains = true;
    }
    for (const std::string& term : node.ivyJustification.terms) {
      if (!resultContains && contains(term)) resultContains = true;
    }
    for (const auto& arguments : node.ivyJustification.parentArguments) {
      for (const std::string& term : arguments) {
        if (!resultContains && contains(term)) resultContains = true;
      }
    }
    std::function<bool(
      const MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
      projectionContains = [&](const auto& projection) {
        if ((projection.hasWitnessTerm
             && contains(projection.witnessTerm.sexpr))
            || (projection.hasSourceLiteral
                && contains(projection.sourceLiteral.sexpr))) {
          return true;
        }
        return std::any_of(
          projection.children.begin(), projection.children.end(),
          projectionContains);
      };
    if (!resultContains && node.producerCnfProjection != nullptr) {
      resultContains = projectionContains(*node.producerCnfProjection);
    }
    nodeExactTermContainment.emplace(cacheKey, resultContains);
    return resultContains;
  };

  // Ground support lemmas can be parent-free even though their proposition
  // contains a local choice witness.  Place every such lemma inside the
  // producer-declared existential scope.  This is a stable topological pass:
  // ordinary proof dependencies remain edges, and a cycle means the proposed
  // scope is not a valid lexical discharge boundary.
  if (std::any_of(
        result.nodes.begin(), result.nodes.end(),
        [](const ChoiceNode& node) { return node.hasRootExistsScope; })) {
    const std::size_t count = result.nodes.size();
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: order scoped DAG; nodes="
                << count << std::endl;
    }
    std::map<std::string, std::size_t> indexByName;
    for (std::size_t index = 0; index < count; ++index) {
      if (!indexByName.emplace(result.nodes[index].step, index).second) {
        error = "ground choice prooftrans cannot order duplicate node names";
        return false;
      }
    }
    std::vector<std::set<std::size_t>> successors(count);
    std::vector<std::set<std::size_t>> predecessors(count);
    std::vector<std::size_t> indegree(count, 0);
    const auto addEdge = [&](std::size_t parent, std::size_t child) {
      if (parent != child && successors[parent].insert(child).second) {
        predecessors[child].insert(parent);
        ++indegree[child];
      }
    };
    for (std::size_t child = 0; child < count; ++child) {
      for (const std::string& parentName : result.nodes[child].parents) {
        auto parent = indexByName.find(parentName);
        if (parent != indexByName.end()) addEdge(parent->second, child);
      }
    }
    for (std::size_t scope = 0; scope < count; ++scope) {
      const ChoiceNode& boundary = result.nodes[scope];
      if (!boundary.hasRootExistsScope
          || boundary.rootExistsScopeWitnessTerm.empty()) {
        continue;
      }
      PreservedSexpr witness;
      if (!parser.parse(boundary.rootExistsScopeWitnessTerm, witness)) {
        error = "ground choice prooftrans cannot parse its scope witness for ordering";
        return false;
      }
      witness = betaNormalizeSexpr(witness);
      std::set<std::size_t> boundaryAncestors;
      std::function<void(std::size_t)> markBoundaryAncestors =
        [&](std::size_t node) {
          for (std::size_t parent : predecessors[node]) {
            if (boundaryAncestors.insert(parent).second) {
              markBoundaryAncestors(parent);
            }
          }
        };
      markBoundaryAncestors(scope);
      for (std::size_t node = 0; node < count; ++node) {
        if (node != scope
            && boundaryAncestors.find(node) == boundaryAncestors.end()
            && nodeContainsExactTerm(result.nodes[node], witness)) {
          addEdge(scope, node);
        }
      }
    }
    std::set<std::size_t> ready;
    for (std::size_t index = 0; index < count; ++index) {
      if (indegree[index] == 0) ready.insert(index);
    }
    std::vector<ChoiceNode> orderedNodes;
    orderedNodes.reserve(count);
    while (!ready.empty()) {
      const std::size_t next = *ready.begin();
      ready.erase(ready.begin());
      orderedNodes.push_back(std::move(result.nodes[next]));
      for (std::size_t child : successors[next]) {
        if (--indegree[child] == 0) ready.insert(child);
      }
    }
    if (orderedNodes.size() != count) {
      if (std::getenv("MEGALODON_CERT_DEBUG")) {
        std::cerr << "megalodon ground scope cycle:" << std::endl;
        for (std::size_t node = 0; node < count; ++node) {
          if (indegree[node] == 0) continue;
          std::cerr << "  " << result.nodes[node].step << " <-";
          for (std::size_t parent : predecessors[node]) {
            if (indegree[parent] != 0) {
              std::cerr << " " << result.nodes[parent].step;
            }
          }
          std::cerr << std::endl;
        }
      }
      error = "ground choice prooftrans scope ordering is cyclic";
      return false;
    }
    for (std::size_t index = 0; index < count; ++index) {
      orderedNodes[index].index = index;
    }
    result.nodes = std::move(orderedNodes);
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scoped DAG order complete"
                << std::endl;
    }
  }
  std::vector<std::size_t> abstractScopeBoundaries;
  for (std::size_t index = 0; index < result.nodes.size(); ++index) {
    if (result.nodes[index].hasRootExistsScope
        && result.nodes[index].rootExistsScopeAbstract) {
      abstractScopeBoundaries.push_back(index);
    }
  }
  // Replay the witness-dependent DAG once with every finite witness abstracted,
  // then wrap that continuation in explicit Church-existential eliminations.
  // This keeps multi-scope prooftrans linear in the expanded Vampire proof.
  if (!abstractScopeBoundaries.empty()) {
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: abstract finite scopes; count="
                << abstractScopeBoundaries.size() << std::endl;
    }
    const std::size_t finalIndex = result.nodes.size() - 1;
    if (result.nodes[finalIndex].step != groundId(0, source.finalStep)
        || !result.nodes[finalIndex].hasResultClause
        || result.nodes[finalIndex].resultClause != "(clause)") {
      error = "ground choice prooftrans complete finite scope has no final contradiction";
      return false;
    }

    std::map<std::string, std::size_t> indexByName;
    for (std::size_t index = 0; index < result.nodes.size(); ++index) {
      indexByName.emplace(result.nodes[index].step, index);
    }
    std::set<std::size_t> ancestors;
    std::function<void(std::size_t)> markAncestors = [&](std::size_t index) {
      if (!ancestors.insert(index).second) return;
      for (const std::string& parentName : result.nodes[index].parents) {
        auto parent = indexByName.find(parentName);
        if (parent != indexByName.end()) markAncestors(parent->second);
      }
    };
    markAncestors(finalIndex);
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: dependency slice complete; nodes="
                << ancestors.size() << std::endl;
    }
    struct AbstractScopeContext {
      std::size_t boundaryIndex = 0;
      std::size_t sourceIndex = 0;
      PreservedSexpr concreteWitness;
      PreservedSexpr witnessVariable;
      PreservedSexpr boundaryBridge;
      std::string sourceHypothesis;
    };
    std::vector<AbstractScopeContext> abstractScopes;
    std::map<std::size_t, std::size_t> abstractScopeByBoundary;
    std::map<std::size_t, std::size_t> abstractScopeBySource;
    abstractScopes.reserve(abstractScopeBoundaries.size());
    for (std::size_t boundaryIndex : abstractScopeBoundaries) {
      const ChoiceNode& boundary = result.nodes[boundaryIndex];
      AbstractScopeContext context;
      context.boundaryIndex = boundaryIndex;
      const auto sourcePosition = indexByName.find(
        boundary.rootExistsScopeSourceStep);
      if (sourcePosition == indexByName.end()
          || !result.nodes[sourcePosition->second].hasResultFormula
          || !parser.parse(
            boundary.rootExistsScopeWitnessTerm, context.concreteWitness)
          || !parser.parse(
            "(TMH "
              + quotePreservedName(boundary.rootExistsScopeWitnessBinder)
              + ")",
            context.witnessVariable)
          || !parser.parse(
            boundary.rootExistsScopeBridgeProof, context.boundaryBridge)
          || !sexprHead(context.boundaryBridge, "proof_lambda")
          || context.boundaryBridge.items.size() != 4
          || !preservedName(
            context.boundaryBridge.items[1], context.sourceHypothesis)) {
        error = "ground choice prooftrans cannot read an abstract finite boundary";
        return false;
      }
      context.sourceIndex = sourcePosition->second;
      context.concreteWitness = betaNormalizeSexpr(context.concreteWitness);
      abstractScopeByBoundary.emplace(
        boundaryIndex, abstractScopes.size());
      if (!abstractScopeBySource.emplace(
            context.sourceIndex, abstractScopes.size()).second) {
        error = "ground choice prooftrans finite scopes share a source step";
        return false;
      }
      abstractScopes.push_back(std::move(context));
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scope contexts complete"
                << std::endl;
    }
    std::vector<std::vector<std::size_t>> scopeGroups;
    std::vector<std::size_t> scopeGroupByScope;
    scopeGroupByScope.reserve(abstractScopes.size());
    for (std::size_t scope = 0; scope < abstractScopes.size(); ++scope) {
      const ChoiceNode& boundary =
        result.nodes[abstractScopes[scope].boundaryIndex];
      std::size_t group = scopeGroups.size();
      for (std::size_t candidate = 0;
           candidate < scopeGroups.size(); ++candidate) {
        const std::size_t representative = scopeGroups[candidate].front();
        const ChoiceNode& representativeBoundary =
          result.nodes[abstractScopes[representative].boundaryIndex];
        if (boundary.rootExistsScopeWitnessType
              == representativeBoundary.rootExistsScopeWitnessType
            && alphaEquivalentSexpr(
                 abstractScopes[scope].concreteWitness,
                 abstractScopes[representative].concreteWitness)) {
          group = candidate;
          break;
        }
      }
      if (group == scopeGroups.size()) scopeGroups.emplace_back();
      scopeGroups[group].push_back(scope);
      scopeGroupByScope.push_back(group);
    }
    const auto canonicalizeScopeVariables = [&]
      (PreservedSexpr value) {
      for (const auto& group : scopeGroups) {
        const PreservedSexpr& representative =
          abstractScopes[group.front()].witnessVariable;
        for (std::size_t item = 1; item < group.size(); ++item) {
          std::size_t replacements = 0;
          value = replaceExactSexpr(
            value,
            abstractScopes[group[item]].witnessVariable,
            representative,
            replacements);
        }
      }
      return value;
    };
    // Unfold only aliases whose bodies actually cross a finite witness scope;
    // unrelated shared definitions remain compact certificate references.
    std::map<std::string, PreservedSexpr> sharedDefinitionBodies;
    for (const auto& definition : source.definitions) {
      if (definition.symbol.compare(
            0, 24, "vampire_ivy_shared_term_") != 0) {
        continue;
      }
      PreservedSexpr body;
      if (!parser.parse(definition.body, body)
          || !sharedDefinitionBodies.emplace(
                definition.symbol, std::move(body)).second) {
        error = "ground choice prooftrans cannot read a shared term definition during finite-scope abstraction";
        return false;
      }
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: shared scope terms indexed; count="
                << sharedDefinitionBodies.size() << std::endl;
    }
    struct WitnessRewrite {
      PreservedSexpr normalized;
      PreservedSexpr rewritten;
      std::size_t nodeCount = 0;
    };
    const std::function<std::size_t(const PreservedSexpr&)> sexprNodeCount =
      [&](const PreservedSexpr& value) {
        if (value.atom) return std::size_t(1);
        std::size_t count = 1;
        for (std::size_t item = 1; item < value.items.size(); ++item) {
          count += sexprNodeCount(value.items[item]);
        }
        return count;
      };
    std::vector<std::size_t> concreteWitnessNodeCounts;
    std::vector<std::set<std::string>> concreteWitnessFreeNames;
    concreteWitnessNodeCounts.reserve(abstractScopes.size());
    concreteWitnessFreeNames.reserve(abstractScopes.size());
    const auto freeNamedTerms = [&](const PreservedSexpr& value) {
      std::set<std::string> names;
      std::vector<std::string> binders;
      std::function<void(const PreservedSexpr&)> collect;
      collect = [&](const PreservedSexpr& current) {
        const bool binder = sexprHead(current, "ALLV")
          || sexprHead(current, "LAMV") || sexprHead(current, "VLAMV");
        if (binder && current.items.size() == 4) {
          collect(current.items[2]);
          std::string name;
          if (!preservedName(current.items[1], name)) return;
          binders.push_back(name);
          collect(current.items[3]);
          binders.pop_back();
          return;
        }
        if (sexprHead(current, "TMH") && current.items.size() == 2) {
          std::string name;
          if (preservedName(current.items[1], name)
              && std::find(binders.begin(), binders.end(), name)
                   == binders.end()) {
            names.insert(std::move(name));
          }
          return;
        }
        if (current.atom) return;
        for (std::size_t item = 1; item < current.items.size(); ++item) {
          collect(current.items[item]);
        }
      };
      collect(value);
      return names;
    };
    for (const auto& scope : abstractScopes) {
      concreteWitnessNodeCounts.push_back(
        sexprNodeCount(scope.concreteWitness));
      concreteWitnessFreeNames.push_back(
        freeNamedTerms(scope.concreteWitness));
    }
    const auto mayContainConcreteWitness = [&]
      (const PreservedSexpr& value, std::size_t scopeCount) {
        const std::size_t limit = std::min(
          scopeCount, concreteWitnessFreeNames.size());
        std::vector<std::set<std::string>> missing(
          concreteWitnessFreeNames.begin(),
          concreteWitnessFreeNames.begin() + limit);
        if (std::any_of(
              missing.begin(), missing.end(),
              [](const auto& names) { return names.empty(); })) {
          return true;
        }
        std::function<bool(const PreservedSexpr&)> collect;
        collect = [&](const PreservedSexpr& current) {
          if (sexprHead(current, "TMH") && current.items.size() == 2) {
            std::string name;
            if (preservedName(current.items[1], name)) {
              for (auto& names : missing) names.erase(name);
              if (std::any_of(
                    missing.begin(), missing.end(),
                    [](const auto& names) { return names.empty(); })) {
                return true;
              }
            }
            return false;
          }
          if (current.atom) return false;
          for (std::size_t item = 1; item < current.items.size(); ++item) {
            if (collect(current.items[item])) return true;
          }
          return false;
        };
        return collect(value);
      };
    std::set<std::string> expandingSharedAliases;
    std::function<WitnessRewrite(
      const PreservedSexpr&, std::size_t, std::size_t&)>
      rewriteWitnesses = [&]
        (const PreservedSexpr& value,
         std::size_t scopeCount,
         std::size_t& replacements) -> WitnessRewrite {
        const std::size_t replacementsAtEntry = replacements;
        const std::size_t limit = std::min(
          scopeCount, abstractScopes.size());
        std::string sharedAlias;
        if (sexprHead(value, "TMH") && value.items.size() == 2
            && preservedName(value.items[1], sharedAlias)) {
          auto definition = sharedDefinitionBodies.find(sharedAlias);
          if (definition != sharedDefinitionBodies.end()
              && expandingSharedAliases.insert(sharedAlias).second) {
            WitnessRewrite expanded = rewriteWitnesses(
              definition->second, scopeCount, replacements);
            expandingSharedAliases.erase(sharedAlias);
            if (replacements != replacementsAtEntry) {
              return expanded;
            }
          }
        }
        WitnessRewrite result;
        result.normalized.atom = value.atom;
        result.rewritten.atom = value.atom;
        result.nodeCount = 1;
        if (value.atom) {
          result.normalized.token = value.token;
          result.rewritten.token = value.token;
        } else {
          result.normalized.items.reserve(value.items.size());
          result.rewritten.items.reserve(value.items.size());
          if (!value.items.empty()) {
            result.normalized.items.push_back(value.items.front());
            result.rewritten.items.push_back(value.items.front());
          }
          for (std::size_t item = 1; item < value.items.size(); ++item) {
            WitnessRewrite child = rewriteWitnesses(
              value.items[item], scopeCount, replacements);
            result.normalized.items.push_back(
              std::move(child.normalized));
            result.rewritten.items.push_back(
              std::move(child.rewritten));
            result.nodeCount += child.nodeCount;
          }
          if (sexprHead(result.normalized, "AP")
              && result.normalized.items.size() == 3
              && (sexprHead(result.normalized.items[1], "LAMV")
                  || sexprHead(result.normalized.items[1], "VLAMV"))
              && result.normalized.items[1].items.size() == 4) {
            std::string variable;
            if (preservedName(
                  result.normalized.items[1].items[1], variable)) {
              PreservedSexpr reduced = betaNormalizeSexpr(
                substituteNamedVariableSexpr(
                  result.normalized.items[1].items[3], variable,
                  result.normalized.items[2]));
              replacements = replacementsAtEntry;
              return rewriteWitnesses(
                reduced, scopeCount, replacements);
            }
          }
        }
        for (std::size_t scope = 0; scope < limit; ++scope) {
          if (result.nodeCount == concreteWitnessNodeCounts[scope]
              && alphaEquivalentSexpr(
                result.normalized,
                abstractScopes[scope].concreteWitness)) {
            ++replacements;
            result.rewritten =
              abstractScopes[scope].witnessVariable;
            break;
          }
        }
        return result;
      };
    const auto abstractWitnessPrefixBeta = [&]
      (PreservedSexpr value, std::size_t scopeCount,
       std::size_t* replacementCount = nullptr) {
      std::size_t replacements = 0;
      if (!mayContainConcreteWitness(value, scopeCount)) {
        if (replacementCount != nullptr) *replacementCount = 0;
        return value;
      }
      WitnessRewrite rewritten = rewriteWitnesses(
        value, scopeCount, replacements);
      if (replacementCount != nullptr) {
        *replacementCount = replacements;
      }
      return std::move(rewritten.rewritten);
    };
    const auto abstractWitnessPrefix = [&]
      (PreservedSexpr value, std::size_t scopeCount,
       std::size_t* replacementCount = nullptr) {
      return abstractWitnessPrefixBeta(
        std::move(value), scopeCount, replacementCount);
    };
    const auto abstractAllWitnesses = [&]
      (PreservedSexpr value, std::size_t* replacementCount = nullptr) {
      return abstractWitnessPrefix(
        std::move(value), abstractScopes.size(), replacementCount);
    };
    struct GroupScopeReplay {
      PreservedSexpr source;
      PreservedSexpr supportProof;
      std::string hypothesis;
      std::vector<std::size_t> members;
    };
    std::map<std::size_t, GroupScopeReplay> groupedScopeReplay;
    std::size_t scopeProofFresh = 0;
    const auto freshScopeName = [&](const std::string& stem) {
      return stem + std::to_string(scopeProofFresh++);
    };
    const auto conjunctionFormula = [&]
      (const PreservedSexpr& left,
       const PreservedSexpr& right,
       PreservedSexpr& conjunction) {
      return parser.parse(
        "(AP (AP (TMH \"vampire_and\") " + left.render()
          + ") " + right.render() + ")",
        conjunction);
    };
    const auto conjunctionProof = [&]
      (const PreservedSexpr& left,
       const PreservedSexpr& right,
       const PreservedSexpr& leftProof,
       const PreservedSexpr& rightProof,
       PreservedSexpr& proof) {
      const std::string resultName = freshScopeName("ivy_scope_and_q_");
      const std::string handlerName = freshScopeName("ivy_scope_and_h_");
      return parser.parse(
        "(term_lambda " + quotePreservedName(resultName) + " (PROP)"
          " (proof_lambda " + quotePreservedName(handlerName)
          + " (formula (IMP " + left.render() + " (IMP "
          + right.render() + " (TMH "
          + quotePreservedName(resultName) + "))))"
          " (proof_apply (proof_apply (hyp "
          + quotePreservedName(handlerName) + ") " + leftProof.render()
          + ") " + rightProof.render() + ")))",
        proof);
    };
    for (std::size_t groupIndex = 0;
         groupIndex < scopeGroups.size(); ++groupIndex) {
      const auto& members = scopeGroups[groupIndex];
      if (members.size() == 1) continue;
      if (members.front() != 0) {
        error = "ground choice prooftrans cannot yet group a repeated finite witness below an earlier distinct witness";
        return false;
      }
      GroupScopeReplay replay;
      replay.members = members;
      replay.hypothesis = "ivy_scope_group_"
        + std::to_string(abstractScopes[members.front()].boundaryIndex);
      std::vector<PreservedSexpr> sources;
      std::vector<PreservedSexpr> concreteSources;
      std::vector<PreservedSexpr> sourceProofs;
      for (std::size_t scope : members) {
        const AbstractScopeContext& context = abstractScopes[scope];
        const ChoiceNode& boundary = result.nodes[context.boundaryIndex];
        const ChoiceNode& sourceNode = result.nodes[context.sourceIndex];
        PreservedSexpr source;
        PreservedSexpr concreteSource;
        PreservedSexpr declaredConcreteSource;
        PreservedSexpr sourceProof;
        if (!parser.parse(boundary.rootExistsScopeSourceFormula, source)
            || !parser.parse(sourceNode.resultFormula, declaredConcreteSource)
            || !parser.parse(
                 "(parent " + quotePreservedName(sourceNode.step) + ")",
                 sourceProof)) {
          error = "ground choice prooftrans cannot assemble a grouped finite source";
          return false;
        }
        source = canonicalizeScopeVariables(std::move(source));
        source = abstractAllWitnesses(std::move(source));
        concreteSource = source;
        for (const auto& concreteGroup : scopeGroups) {
          const std::size_t representative = concreteGroup.front();
          std::size_t replacements = 0;
          concreteSource = replaceExactSexpr(
            concreteSource,
            abstractScopes[representative].witnessVariable,
            abstractScopes[representative].concreteWitness,
            replacements);
        }
        if (!alphaEquivalentSexpr(
              betaNormalizeSexpr(concreteSource),
              betaNormalizeSexpr(declaredConcreteSource))) {
          error = "ground choice prooftrans grouped finite source is not the exact Vampire source claim at "
            + sourceNode.step;
          return false;
        }
        sources.push_back(std::move(source));
        concreteSources.push_back(std::move(concreteSource));
        sourceProofs.push_back(std::move(sourceProof));
      }
      PreservedSexpr combinedSource = sources.back();
      PreservedSexpr combinedConcrete = concreteSources.back();
      PreservedSexpr combinedProof = sourceProofs.back();
      for (std::size_t remaining = sources.size() - 1;
           remaining > 0; --remaining) {
        const std::size_t item = remaining - 1;
        PreservedSexpr nextSource;
        PreservedSexpr nextConcrete;
        PreservedSexpr nextProof;
        if (!conjunctionFormula(
              sources[item], combinedSource, nextSource)
            || !conjunctionFormula(
              concreteSources[item], combinedConcrete, nextConcrete)
            || !conjunctionProof(
              concreteSources[item], combinedConcrete,
              sourceProofs[item], combinedProof, nextProof)) {
          error = "ground choice prooftrans cannot build its grouped finite conjunction";
          return false;
        }
        combinedSource = std::move(nextSource);
        combinedConcrete = std::move(nextConcrete);
        combinedProof = std::move(nextProof);
      }
      const std::size_t representative = members.front();
      const ChoiceNode& representativeBoundary =
        result.nodes[abstractScopes[representative].boundaryIndex];
      const std::string resultName = freshScopeName("ivy_scope_exists_q_");
      const std::string handlerName = freshScopeName("ivy_scope_exists_h_");
      PreservedSexpr supportProof;
      if (!parser.parse(
            "(term_lambda " + quotePreservedName(resultName) + " (PROP)"
              " (proof_lambda " + quotePreservedName(handlerName)
              + " (formula (ALLV "
              + quotePreservedName(
                  representativeBoundary.rootExistsScopeWitnessBinder)
              + " " + representativeBoundary.rootExistsScopeWitnessType
              + " (IMP " + combinedSource.render() + " (TMH "
              + quotePreservedName(resultName) + "))))"
              " (proof_apply (term_apply (hyp "
              + quotePreservedName(handlerName) + ") (term "
              + abstractScopes[representative].concreteWitness.render()
              + ")) " + combinedProof.render() + ")))",
            supportProof)) {
        error = "ground choice prooftrans cannot build its grouped finite existential";
        return false;
      }
      replay.source = std::move(combinedSource);
      replay.supportProof = std::move(supportProof);
      groupedScopeReplay.emplace(groupIndex, std::move(replay));
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: grouped scopes complete"
                << std::endl;
    }
    const auto conjunctionProjection = [&]
      (const GroupScopeReplay& replay,
       std::size_t memberPosition,
       PreservedSexpr& proof) {
      if (memberPosition >= replay.members.size()
          || !parser.parse(
               "(hyp " + quotePreservedName(replay.hypothesis) + ")",
               proof)) {
        return false;
      }
      PreservedSexpr current = replay.source;
      for (std::size_t position = 0;
           position + 1 < replay.members.size(); ++position) {
        PreservedSexpr left;
        PreservedSexpr right;
        if (!binaryNamedApplicationSexpr(
              current, "vampire_and", left, right)) {
          return false;
        }
        const bool selectLeft = memberPosition == position;
        const PreservedSexpr& selected = selectLeft ? left : right;
        const std::string leftName = freshScopeName("ivy_scope_proj_l_");
        const std::string rightName = freshScopeName("ivy_scope_proj_r_");
        PreservedSexpr projected;
        if (!parser.parse(
              "(proof_apply (term_apply " + proof.render()
                + " (formula " + selected.render() + "))"
                " (proof_lambda " + quotePreservedName(leftName)
                + " (formula " + left.render() + ")"
                " (proof_lambda " + quotePreservedName(rightName)
                + " (formula " + right.render() + ") (hyp "
                + quotePreservedName(selectLeft ? leftName : rightName)
                + "))))",
              projected)) {
          return false;
        }
        proof = std::move(projected);
        if (selectLeft) return true;
        current = std::move(right);
      }
      return memberPosition + 1 == replay.members.size();
    };
    const auto abstractNodeValue = [&]
      (PreservedSexpr value, const ChoiceNode& node) {
      (void)node;
      return abstractScopes.size() > 1
        ? abstractWitnessPrefixBeta(
            std::move(value), abstractScopes.size())
        : abstractAllWitnesses(std::move(value));
    };
    std::set<std::size_t> descendants(
      abstractScopeBoundaries.begin(), abstractScopeBoundaries.end());
    const std::size_t firstBoundary = abstractScopeBoundaries.front();
    for (std::size_t index = firstBoundary;
         index < result.nodes.size(); ++index) {
      const bool containsWitness = std::any_of(
        abstractScopes.begin(), abstractScopes.end(),
        [&](const AbstractScopeContext& context) {
          return nodeContainsExactTerm(
            result.nodes[index], context.concreteWitness);
        });
      if (containsWitness
          || std::any_of(
            result.nodes[index].parents.begin(),
            result.nodes[index].parents.end(),
            [&](const std::string& parentName) {
              auto parent = indexByName.find(parentName);
              return parent != indexByName.end()
                && descendants.find(parent->second) != descendants.end();
            })) {
        descendants.insert(index);
      }
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scope descendants complete; nodes="
                << descendants.size() << std::endl;
    }
    std::vector<std::size_t> scopedNodes;
    for (std::size_t index = firstBoundary;
         index < result.nodes.size(); ++index) {
      if (ancestors.find(index) != ancestors.end()
          && descendants.find(index) != descendants.end()) {
        scopedNodes.push_back(index);
      }
    }
    if (scopedNodes.empty() || scopedNodes.back() != finalIndex
        || std::any_of(
          abstractScopeBoundaries.begin(), abstractScopeBoundaries.end(),
          [&](std::size_t boundary) {
            return std::find(
              scopedNodes.begin(), scopedNodes.end(), boundary)
              == scopedNodes.end();
          })) {
      error = "ground choice prooftrans finite boundaries do not reach the contradiction";
      return false;
    }
    if (std::getenv("MEGALODON_CERT_DEBUG")) {
      std::cerr << "megalodon abstract scope claims:" << std::endl;
      for (std::size_t ordinal = 0;
           ordinal < scopedNodes.size(); ++ordinal) {
        std::cerr << "  " << ordinal << " "
                  << result.nodes[scopedNodes[ordinal]].step << std::endl;
      }
    }

    std::map<std::string, std::string> localHypotheses;
    std::size_t scopedProofBinderFresh = 0;
    for (std::size_t index : scopedNodes) {
      localHypotheses.emplace(
        result.nodes[index].step,
        "ivy_scope_claim_" + std::to_string(index));
    }
    std::map<std::size_t, PreservedSexpr> abstractProofs;
    std::set<std::size_t> compactScopedNodes;
    std::map<std::size_t, std::string> abstractPropositions;
    std::map<std::size_t, std::vector<std::string>> abstractClauses;
    using GroundEnvironment = std::map<std::string, PreservedSexpr>;
    std::map<std::size_t, GroundEnvironment> abstractEnvironments;
    const auto abstractEnvironment = [&](std::size_t instance)
      -> const GroundEnvironment* {
      if (instance >= environments.size()) return nullptr;
      auto found = abstractEnvironments.find(instance);
      if (found != abstractEnvironments.end()) return &found->second;
      GroundEnvironment environment = environments[instance];
      for (auto& binding : environment) {
        binding.second = abstractAllWitnesses(std::move(binding.second));
      }
      return &abstractEnvironments.emplace(
        instance, std::move(environment)).first->second;
    };
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: lazy abstract environments ready"
                << std::endl;
    }

    const auto abstractSourceConclusion = [&]
      (const ChoiceNode& renderedNode,
       PreservedSexpr& conclusion) {
      if (!renderedNode.hasProducerGroundOrigin
          || renderedNode.producerGroundSourceInstance
             >= environments.size()) {
        return false;
      }
      auto sourceNode = nodeById.find(renderedNode.producerGroundSourceNode);
      if (sourceNode == nodeById.end()) return false;
      const ChoiceNode& original = *sourceNode->second;
      if (original.hasResultClause != renderedNode.hasResultClause
          || original.hasResultFormula != renderedNode.hasResultFormula) {
        return false;
      }
      const std::string& text = original.hasResultClause
        ? original.resultClause : original.resultFormula;
      if (!parser.parse(text, conclusion)) return false;
      const GroundEnvironment* environment = abstractEnvironment(
        renderedNode.producerGroundSourceInstance);
      if (environment == nullptr) return false;
      conclusion = original.hasResultFormula
        ? specializeLeadingBindersWithEnvironment(
            std::move(conclusion), *environment, "ALLV")
        : specializeWithEnvironment(std::move(conclusion), *environment);
      conclusion = abstractNodeValue(
        std::move(conclusion), renderedNode);
      return true;
    };

    std::size_t abstractProofOrdinal = 0;
    for (std::size_t index : scopedNodes) {
      ChoiceNode& node = result.nodes[index];
      auto scopeAtSource = abstractScopeBySource.find(index);
      if (scopeAtSource != abstractScopeBySource.end()) {
        PreservedSexpr source;
        const ChoiceNode& boundary = result.nodes[
          abstractScopes[scopeAtSource->second].boundaryIndex];
        if (!node.hasResultFormula
            || !parser.parse(boundary.rootExistsScopeSourceFormula, source)) {
          error = "ground choice prooftrans cannot read its exact finite-scope source claim at "
            + node.step;
          return false;
        }
        source = canonicalizeScopeVariables(std::move(source));
        source = abstractAllWitnesses(std::move(source));
        abstractPropositions.emplace(
          index, "(formula " + source.render() + ")");
        continue;
      }
      if (node.rootExistsScopeBoundaryCopy) {
        if (node.parents.size() != 1) {
          error = "ground choice prooftrans finite-scope boundary copy has multiple parents at "
            + node.step;
          return false;
        }
        const auto parent = indexByName.find(node.parents.front());
        if (parent == indexByName.end()
            || abstractScopeByBoundary.find(parent->second)
                 == abstractScopeByBoundary.end()) {
          error = "ground choice prooftrans finite-scope boundary copy lost its boundary at "
            + node.step;
          return false;
        }
      }
      auto scopeAtBoundary = abstractScopeByBoundary.find(index);
      if (scopeAtBoundary != abstractScopeByBoundary.end()) {
        PreservedSexpr target;
        if (!parser.parse(node.rootExistsScopeTargetFormula, target)) {
          error = "ground choice prooftrans cannot read its exact finite-scope target at "
            + node.step;
          return false;
        }
        target = canonicalizeScopeVariables(std::move(target));
        target = abstractAllWitnesses(std::move(target));
        abstractPropositions.emplace(
          index, "(formula " + target.render() + ")");
        continue;
      }
      PreservedSexpr proposition;
      const std::string& propositionText = node.hasResultFormula
        ? node.resultFormula : node.resultClause;
      if (!parser.parse(propositionText, proposition)) return false;
      PreservedSexpr replacedProposition =
        abstractNodeValue(proposition, node);
      PreservedSexpr replayedProposition;
      if (node.hasProducerGroundOrigin) {
        if (!abstractSourceConclusion(node, replayedProposition)
            || !alphaEquivalentSexpr(
                 betaNormalizeSexpr(replayedProposition),
                 betaNormalizeSexpr(replacedProposition))) {
          if (std::getenv("MEGALODON_CERT_DEBUG")) {
            std::cerr << "megalodon abstract conclusion mismatch at "
                      << node.step << "\n  replayed: "
                      << replayedProposition.render()
                      << "\n  replaced: "
                      << replacedProposition.render() << std::endl;
          }
          error = "ground choice prooftrans abstract source conclusion disagrees at "
            + node.step;
          return false;
        }
        proposition = abstractScopes.size() > 1
          ? std::move(replacedProposition)
          : std::move(replayedProposition);
      } else {
        proposition = std::move(replacedProposition);
      }
      if (node.hasResultFormula) {
        abstractPropositions.emplace(
          index, "(formula " + proposition.render() + ")");
      } else if (node.hasResultClause && sexprHead(proposition, "clause")) {
        std::vector<std::string> literals;
        for (std::size_t item = 1; item < proposition.items.size(); ++item) {
          literals.push_back(proposition.items[item].render());
        }
        abstractClauses.emplace(index, std::move(literals));
        abstractPropositions.emplace(
          index, "(clause " + proposition.render() + ")");
      } else {
        return false;
      }
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: abstract propositions complete"
                << "; environments=" << abstractEnvironments.size()
                << std::endl;
    }

    const auto abstractSourceProof = [&]
      (const ChoiceNode& renderedNode,
       PreservedSexpr& proof) {
      if (!renderedNode.hasProducerGroundOrigin
          || renderedNode.producerGroundSourceInstance
             >= environments.size()) {
        return false;
      }
      const Key key = {
        renderedNode.producerGroundSourceNode,
        renderedNode.producerGroundSourceInstance};
      auto sourceNode = nodeById.find(key.node);
      if (sourceNode == nodeById.end()
          || !parser.parse(sourceNode->second->producerProof, proof)) {
        return false;
      }
      proof = normalizePrivateProofReferences(
        *sourceNode->second, proof, normalizePrivateProofReferences);
      proof = normalizeProducerTerms(
        std::move(proof), normalizeProducerTerms);
      const GroundEnvironment* sourceEnvironment =
        abstractEnvironment(key.instance);
      if (sourceEnvironment == nullptr) return false;
      proof = specializeLeadingBindersWithEnvironment(
        std::move(proof), *sourceEnvironment, "term_lambda");
      proof = abstractNodeValue(std::move(proof), renderedNode);

      std::function<bool(const PreservedSexpr&, PreservedSexpr&)> rewrite;
      rewrite = [&](const PreservedSexpr& input, PreservedSexpr& output) {
        std::vector<PreservedSexpr> arguments;
        const PreservedSexpr* base = &input;
        while (sexprHead(*base, "term_apply") && base->items.size() == 3) {
          arguments.push_back(base->items[2]);
          base = &base->items[1];
        }
        if (sexprHead(*base, "parent") && base->items.size() == 2) {
          std::string parent;
          if (!preservedName(base->items[1], parent)) return false;
          ParentTarget target;
          if (!resolveParentForKey(key, parent, target)) return false;
          std::reverse(arguments.begin(), arguments.end());
          std::vector<PreservedSexpr> retainedArguments;
          if (target.generated) {
            auto parentNode = nodeById.find(target.key.node);
            if (parentNode == nodeById.end()) return false;
            const ChoiceNode& originalParent = *parentNode->second;
            const std::vector<bool> formulaBinders =
              formulaBinderSpecializations(
                originalParent, target.key.instance);
            const std::size_t parameterArguments =
              originalParent.parameters.size();
            if (arguments.size() < parameterArguments) return false;
            const std::size_t suppliedFormulaArguments = std::min(
              formulaBinders.size(),
              arguments.size() - parameterArguments);
            const std::size_t consumedArguments =
              parameterArguments + suppliedFormulaArguments;
            const GroundEnvironment* parentEnvironment =
              abstractEnvironment(target.key.instance);
            if (parentEnvironment == nullptr) return false;
            for (std::size_t item = 0;
                 item < originalParent.parameters.size(); ++item) {
              PreservedSexpr argument = specializeWithEnvironment(
                arguments[item], *sourceEnvironment);
              if (parentEnvironment->find(
                    originalParent.parameters[item].first)
                  == parentEnvironment->end()) {
                retainedArguments.push_back(std::move(argument));
              }
            }
            for (std::size_t item = 0;
                 item < suppliedFormulaArguments; ++item) {
              PreservedSexpr argument = specializeWithEnvironment(
                arguments[originalParent.parameters.size() + item],
                *sourceEnvironment);
              if (!formulaBinders[item]) {
                retainedArguments.push_back(std::move(argument));
              }
            }
            for (std::size_t item = consumedArguments;
                 item < arguments.size(); ++item) {
              retainedArguments.push_back(specializeWithEnvironment(
                arguments[item], *sourceEnvironment));
            }
          } else {
            for (const PreservedSexpr& argument : arguments) {
              retainedArguments.push_back(specializeWithEnvironment(
                argument, *sourceEnvironment));
            }
          }
          if (!parser.parse(
                "(parent " + quotePreservedName(target.rendered) + ")",
                output)) {
            return false;
          }
          for (const PreservedSexpr& argument : retainedArguments) {
            PreservedSexpr applied;
            if (!parser.parse(
                  "(term_apply " + output.render() + " "
                    + argument.render() + ")",
                  applied)) {
              return false;
            }
            output = std::move(applied);
          }
          return true;
        }
        output = input;
        if (output.atom) return true;
        for (std::size_t item = 1; item < output.items.size(); ++item) {
          if (!rewrite(output.items[item], output.items[item])) return false;
        }
        return true;
      };

      PreservedSexpr rewritten;
      if (!rewrite(proof, rewritten)) return false;
      proof = std::move(rewritten);
      return true;
    };

    std::map<std::size_t, std::vector<std::string>> compactAbstractClauses =
      abstractClauses;
    const auto compactClause = [&](const std::string& step)
      -> const std::vector<std::string>* {
      const auto position = indexByName.find(step);
      if (position == indexByName.end()) return nullptr;
      auto cached = compactAbstractClauses.find(position->second);
      if (cached != compactAbstractClauses.end()) return &cached->second;
      const ChoiceNode& parent = result.nodes[position->second];
      PreservedSexpr clause;
      if (!parent.hasResultClause
          || !parser.parse(parent.resultClause, clause)) {
        return nullptr;
      }
      clause = canonicalizeScopeVariables(
        abstractNodeValue(std::move(clause), parent));
      if (!sexprHead(clause, "clause")) return nullptr;
      std::vector<std::string> literals;
      literals.reserve(clause.items.size() - 1);
      for (std::size_t item = 1; item < clause.items.size(); ++item) {
        literals.push_back(clause.items[item].render());
      }
      return &compactAbstractClauses.emplace(
        position->second, std::move(literals)).first->second;
    };
    const auto abstractIvyTerm = [&](const ChoiceNode& node,
                                     const std::string& text,
                                     std::string& rendered) {
      PreservedSexpr term;
      if (!parser.parse(text, term)) return false;
      term = canonicalizeScopeVariables(
        abstractNodeValue(std::move(term), node));
      rendered = term.render();
      return true;
    };
    const auto abstractIvyTerms = [&](const ChoiceNode& node,
                                      const std::vector<std::string>& source,
                                      std::vector<std::string>& rendered) {
      rendered.clear();
      rendered.reserve(source.size());
      for (const std::string& text : source) {
        std::string term;
        if (!abstractIvyTerm(node, text, term)) return false;
        rendered.push_back(std::move(term));
      }
      return true;
    };
    const auto compactIvyProof = [&](std::size_t index,
                                     const ChoiceNode& node,
                                     PreservedSexpr& proof) {
      const IvyRule rule = node.ivyJustification.rule;
      if (rule == IvyRule::None) return false;
      const auto& parents = node.ivyJustification.parents;
      const auto& indices = node.ivyJustification.indices;
      const auto target = compactAbstractClauses.find(index);
      IvyClauseProofBuilder builder;
      std::string built;
      std::vector<std::string> arguments;
      if (!abstractIvyTerms(node, node.ivyJustification.terms, arguments)) {
        return false;
      }
      if (rule == IvyRule::Copy) {
        if (parents.size() != 1) return false;
        built = builder.parent(parents.front());
      } else if (rule == IvyRule::Instantiate) {
        if (parents.size() != 1
            || !builder.instantiation(parents.front(), arguments, built)) {
          return false;
        }
      } else if (rule == IvyRule::Factor) {
        if (parents.size() != 1 || indices.size() != 2
            || target == compactAbstractClauses.end()) {
          return false;
        }
        const auto source = compactClause(parents.front());
        if (source == nullptr
            || !builder.projection(
                 parents.front(), arguments, *source,
                 target->second, built)) {
          return false;
        }
      } else if (rule == IvyRule::EqualityResolution
                 || rule == IvyRule::EqualitySymmetry
                 || rule == IvyRule::TruthConflict) {
        if (parents.size() != 1 || indices.size() != 1
            || target == compactAbstractClauses.end()) {
          return false;
        }
        const auto source = compactClause(parents.front());
        if (source == nullptr) return false;
        const bool replayed = rule == IvyRule::EqualityResolution
          ? builder.equalityResolution(
              parents.front(), arguments, *source, indices.front(),
              target->second, built)
          : rule == IvyRule::EqualitySymmetry
            ? builder.equalitySymmetry(
                parents.front(), arguments, *source, indices.front(),
                target->second, built)
            : builder.truthConflict(
                parents.front(), arguments, *source, indices.front(),
                target->second, built);
        if (!replayed) return false;
      } else if (rule == IvyRule::Resolve) {
        if (parents.size() != 2 || indices.size() != 2
            || node.ivyJustification.parentArguments.size() != 2
            || target == compactAbstractClauses.end()) {
          return false;
        }
        const auto left = compactClause(parents[0]);
        const auto right = compactClause(parents[1]);
        std::vector<std::string> leftArguments;
        std::vector<std::string> rightArguments;
        if (left == nullptr || right == nullptr
            || !abstractIvyTerms(
                 node, node.ivyJustification.parentArguments[0],
                 leftArguments)
            || !abstractIvyTerms(
                 node, node.ivyJustification.parentArguments[1],
                 rightArguments)
            || !builder.resolution(
                 parents[0], leftArguments, *left, indices[0],
                 parents[1], rightArguments, *right, indices[1],
                 target->second, built)) {
          return false;
        }
      } else if (rule == IvyRule::Paramodulate) {
        if (parents.size() != 2 || indices.size() != 3
            || node.ivyJustification.parentArguments.size() != 2
            || target == compactAbstractClauses.end()
            || indices[2] >= target->second.size()) {
          return false;
        }
        const auto equalityClause = compactClause(parents[0]);
        const auto targetClause = compactClause(parents[1]);
        std::vector<std::string> equalityArguments;
        std::vector<std::string> targetArguments;
        std::string from;
        std::string to;
        PreservedSexpr position;
        std::vector<unsigned> path;
        if (equalityClause == nullptr || targetClause == nullptr
            || !abstractIvyTerms(
                 node, node.ivyJustification.parentArguments[0],
                 equalityArguments)
            || !abstractIvyTerms(
                 node, node.ivyJustification.parentArguments[1],
                 targetArguments)
            || !abstractIvyTerm(node, node.ivyJustification.from, from)
            || !abstractIvyTerm(node, node.ivyJustification.to, to)
            || !parser.parse(node.ivyJustification.position, position)
            || !sexprHead(position, "position")) {
          return false;
        }
        for (std::size_t item = 1; item < position.items.size(); ++item) {
          if (!position.items[item].atom) return false;
          std::size_t consumed = 0;
          unsigned long value = 0;
          try {
            value = std::stoul(position.items[item].token, &consumed);
          } catch (...) {
            return false;
          }
          if (consumed != position.items[item].token.size()) return false;
          path.push_back(static_cast<unsigned>(value));
        }
        const auto replay = [&](bool symmetry) {
          return builder.paramodulation(
            parents[0], equalityArguments, *equalityClause, indices[0],
            parents[1], targetArguments, *targetClause, indices[1], path,
            from, to, target->second[indices[2]], target->second, symmetry,
            "", built);
        };
        if (!replay(false) && !replay(true)) return false;
      } else {
        return false;
      }
      return parser.parse(built, proof);
    };

    for (std::size_t index : scopedNodes) {
      ChoiceNode& node = result.nodes[index];
      if (certificateDebug
          && (abstractProofOrdinal % 25 == 0
              || abstractProofOrdinal >= 270)) {
        std::cerr << "megalodon ground choice phase: abstract proof "
                  << abstractProofOrdinal << "/" << scopedNodes.size()
                  << "; step=" << node.step
                  << "; ms=" << certificateProfileMilliseconds()
                  << std::endl;
      }
      PreservedSexpr proof;
      auto scopeAtBoundary = abstractScopeByBoundary.find(index);
      auto scopeAtSource = abstractScopeBySource.find(index);
      if (scopeAtSource != abstractScopeBySource.end()) {
        const AbstractScopeContext& sourceScope =
          abstractScopes[scopeAtSource->second];
        PreservedSexpr declaredClaim;
        PreservedSexpr declaredSource;
        const ChoiceNode& boundary =
          result.nodes[sourceScope.boundaryIndex];
        if (!parser.parse(
              abstractPropositions.at(index), declaredClaim)
            || !sexprHead(declaredClaim, "formula")
            || declaredClaim.items.size() != 2
            || !parser.parse(
              boundary.rootExistsScopeSourceFormula, declaredSource)) {
          error = "ground choice prooftrans cannot parse its finite-scope source claim at "
            + node.step;
          return false;
        }
        declaredSource = canonicalizeScopeVariables(
          std::move(declaredSource));
        declaredSource = abstractAllWitnesses(std::move(declaredSource));
        if (!alphaEquivalentSexpr(
              betaNormalizeSexpr(declaredClaim.items[1]),
              betaNormalizeSexpr(declaredSource))) {
          error = "ground choice prooftrans finite-scope source claim disagrees with its exact bound hypothesis at "
            + node.step;
          return false;
        }
        const std::size_t groupIndex =
          scopeGroupByScope[scopeAtSource->second];
        auto grouped = groupedScopeReplay.find(groupIndex);
        if (grouped != groupedScopeReplay.end()) {
          const auto member = std::find(
            grouped->second.members.begin(),
            grouped->second.members.end(),
            scopeAtSource->second);
          if (member == grouped->second.members.end()
              || !conjunctionProjection(
                   grouped->second,
                   static_cast<std::size_t>(
                     member - grouped->second.members.begin()),
                   proof)) {
            error = "ground choice prooftrans cannot project a grouped finite source at "
              + node.step;
            return false;
          }
        } else if (!parser.parse(
                     "(hyp "
                       + quotePreservedName(sourceScope.sourceHypothesis)
                       + ")",
                     proof)) {
          return false;
        }
      } else if (node.rootExistsScopeBoundaryCopy) {
        if (node.parents.size() != 1
            || node.producerProof.empty()
            || !parser.parse(node.producerProof, proof)) {
          error = "ground choice prooftrans cannot replay its finite-scope boundary copy at "
            + node.step;
          return false;
        }
        proof = abstractAllWitnesses(std::move(proof));
      } else if (scopeAtBoundary != abstractScopeByBoundary.end()) {
        const AbstractScopeContext& boundaryScope =
          abstractScopes[scopeAtBoundary->second];
        PreservedSexpr sourceClaimProof;
        const std::size_t groupIndex =
          scopeGroupByScope[scopeAtBoundary->second];
        auto grouped = groupedScopeReplay.find(groupIndex);
        if (grouped != groupedScopeReplay.end()) {
          const auto member = std::find(
            grouped->second.members.begin(),
            grouped->second.members.end(),
            scopeAtBoundary->second);
          if (member == grouped->second.members.end()
              || !conjunctionProjection(
                   grouped->second,
                   static_cast<std::size_t>(
                     member - grouped->second.members.begin()),
                   sourceClaimProof)) {
            error = "ground choice prooftrans cannot project a grouped boundary source";
            return false;
          }
          proof = preservedList(
            preservedAtom("proof_apply"),
            boundaryScope.boundaryBridge,
            std::move(sourceClaimProof));
        } else {
          const auto sourceClaim = localHypotheses.find(
            result.nodes[boundaryScope.sourceIndex].step);
          if (sourceClaim != localHypotheses.end()) {
            if (!parser.parse(
                  "(hyp " + quotePreservedName(sourceClaim->second) + ")",
                  sourceClaimProof)) {
              return false;
            }
            proof = preservedList(
              preservedAtom("proof_apply"),
              boundaryScope.boundaryBridge,
              std::move(sourceClaimProof));
          } else {
            proof = boundaryScope.boundaryBridge.items[3];
          }
        }
        proof = canonicalizeScopeVariables(std::move(proof));
        proof = abstractAllWitnesses(std::move(proof));
      } else if (node.producerCnfProjection != nullptr
                 && node.hasResultClause) {
        PreservedSexpr projectionSource;
        if (!parser.parse(node.producerCnfSourceFormula, projectionSource)) {
          error = "ground choice prooftrans cannot parse scoped CNF source at "
            + node.step;
          return false;
        }
        PreservedSexpr concreteClause;
        std::vector<std::string> concreteLiterals;
        if (!parser.parse(node.resultClause, concreteClause)
            || !sexprHead(concreteClause, "clause")) {
          return false;
        }
        for (std::size_t item = 1;
             item < concreteClause.items.size(); ++item) {
          concreteLiterals.push_back(concreteClause.items[item].render());
        }
        const std::size_t environmentIndex = node.hasProducerGroundOrigin
          ? node.producerGroundSourceInstance : 0;
        std::string adaptationFailure;
        bool replayed = false;
        if (environmentIndex < environments.size()) {
          for (const AbstractScopeContext& context : abstractScopes) {
            const ChoiceNode& scopeBoundary =
              result.nodes[context.boundaryIndex];
            PreservedSexpr declaredScopeSource;
            if (!parser.parse(
                  scopeBoundary.rootExistsScopeSourceFormula,
                  declaredScopeSource)) {
              return false;
            }
            std::size_t scopeReplacements = 0;
            PreservedSexpr concreteScopeSource = replaceAlphaEquivalent(
              declaredScopeSource,
              context.witnessVariable,
              context.concreteWitness,
              scopeReplacements);
            if (scopeReplacements == 0) continue;
            auto projection =
              MegalodonKernelSyntax::RenderedKernelCnfProjection{};
            if (!adaptCnfProjection(
                  projectionSource, concreteScopeSource,
                  *node.producerCnfProjection, concreteLiterals,
                  environments[environmentIndex], projection,
                  adaptationFailure)) {
              continue;
            }
            std::function<bool(
              MegalodonKernelSyntax::RenderedKernelCnfProjection&)>
              abstractProjection;
            abstractProjection = [&](auto& item) {
              const auto abstractField = [&](auto& field) {
                PreservedSexpr value;
                if (!parser.parse(field.sexpr, value)) return false;
                value = abstractNodeValue(std::move(value), node);
                field.sexpr = canonicalizeScopeVariables(
                  std::move(value)).render();
                return true;
              };
              if (item.hasWitnessTerm && !abstractField(item.witnessTerm)) {
                return false;
              }
              if (item.hasSourceLiteral && !abstractField(item.sourceLiteral)) {
                return false;
              }
              for (auto& child : item.children) {
                if (!abstractProjection(child)) return false;
              }
              return true;
            };
            PreservedSexpr abstractScopeSource =
              canonicalizeScopeVariables(std::move(concreteScopeSource));
            abstractScopeSource = abstractNodeValue(
              std::move(abstractScopeSource), node);
            std::string rebuilt;
            IvyClauseProofBuilder builder;
            PreservedSexpr sourceProof;
            const std::size_t scopeIndex = static_cast<std::size_t>(
              &context - abstractScopes.data());
            const std::size_t groupIndex = scopeGroupByScope[scopeIndex];
            auto grouped = groupedScopeReplay.find(groupIndex);
            if (grouped != groupedScopeReplay.end()) {
              const auto member = std::find(
                grouped->second.members.begin(),
                grouped->second.members.end(),
                scopeIndex);
              if (member == grouped->second.members.end()
                  || !conjunctionProjection(
                       grouped->second,
                       static_cast<std::size_t>(
                         member - grouped->second.members.begin()),
                       sourceProof)) {
                return false;
              }
            } else {
              const auto sourceClaim = localHypotheses.find(
                result.nodes[context.sourceIndex].step);
              const std::string sourceHypothesis =
                sourceClaim == localHypotheses.end()
                  ? context.sourceHypothesis : sourceClaim->second;
              if (!parser.parse(
                    "(hyp " + quotePreservedName(sourceHypothesis) + ")",
                    sourceProof)) {
                return false;
              }
            }
            replayed = abstractProjection(projection)
              && builder.cnfFormulaClauseProof(
                   sourceProof.render(),
                   abstractScopeSource.render(), projection,
                   abstractClauses.at(index), rebuilt)
              && parser.parse(rebuilt, proof);
            if (replayed) break;
          }
        }
        if (!replayed && abstractScopes.size() > 1
            && !node.producerProof.empty()
            && parser.parse(node.producerProof, proof)) {
          proof = abstractNodeValue(std::move(proof), node);
          replayed = true;
        }
        if (!replayed && node.hasProducerGroundOrigin) {
          replayed = abstractSourceProof(node, proof);
        }
        if (!replayed) {
          if (std::getenv("MEGALODON_CERT_DEBUG")) {
            std::cerr << "megalodon scoped CNF replay failed at "
                      << node.step << ": " << adaptationFailure
                      << "\n  projection source: "
                      << projectionSource.render() << std::endl;
          }
          error = "ground choice prooftrans cannot replay exact CNF projection from its abstract scope at "
            + node.step;
          return false;
        }
      } else if (node.ivyJustification.rule != IvyRule::None) {
        if (!compactIvyProof(index, node, proof)) {
          error = "ground choice prooftrans cannot replay compact Ivy inference under its abstract witness at "
            + node.step;
          return false;
        }
        compactScopedNodes.insert(index);
      } else if (abstractScopes.size() > 1
                 && !node.hasResultFormula
                 && !node.producerProof.empty()
                 && parser.parse(node.producerProof, proof)) {
        proof = abstractNodeValue(std::move(proof), node);
      } else if (node.hasProducerGroundOrigin) {
        if (!abstractSourceProof(node, proof)) {
          error = "ground choice prooftrans cannot replay the Vampire source proof under its abstract witness at "
            + node.step;
          return false;
        }
      } else if (!node.producerProof.empty()
                 && parser.parse(node.producerProof, proof)) {
        proof = abstractAllWitnesses(std::move(proof));
      } else {
        error = "ground choice prooftrans scoped continuation lacks an explicit proof at "
          + node.step;
        return false;
      }
      // Every proof path above passes through the exact witness abstraction.
      // Re-running that normalization here is quadratic in the final scoped
      // SAT proof and cannot discover a case the transformation did not visit.
      if (compactScopedNodes.find(index) == compactScopedNodes.end()) {
        abstractProofs.emplace(index, std::move(proof));
      }
      ++abstractProofOrdinal;
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: abstract proofs complete"
                << "; environments=" << abstractEnvironments.size()
                << std::endl;
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scoped parameters retained"
                << std::endl;
    }
    struct ClosedScopeFrame {
      MegalodonKernelSyntax::RenderedKernelIvyContextFrame context;
      std::string supportStep;
    };
    std::vector<ClosedScopeFrame> closedScopes;
    std::vector<ChoiceNode> supportNodes;
    for (std::size_t groupIndex = 0;
         groupIndex < scopeGroups.size(); ++groupIndex) {
      const auto& members = scopeGroups[groupIndex];
      const std::size_t representative = members.front();
      const AbstractScopeContext& scope = abstractScopes[representative];
      const ChoiceNode& boundary = result.nodes[scope.boundaryIndex];
      ClosedScopeFrame closed;
      closed.context.binder = boundary.rootExistsScopeWitnessBinder;
      closed.context.witnessType = boundary.rootExistsScopeWitnessType;
      auto grouped = groupedScopeReplay.find(groupIndex);
      if (grouped != groupedScopeReplay.end()) {
        closed.context.hypothesis = grouped->second.hypothesis;
        closed.context.sourceFormula = grouped->second.source.render();
        closed.supportStep = "ivy_scope_support_"
          + std::to_string(scope.boundaryIndex);
        const std::string proposition =
          "(ALLV \"ivy_scope_result\" (PROP) (IMP (ALLV "
          + quotePreservedName(closed.context.binder) + " "
          + closed.context.witnessType + " (IMP "
          + closed.context.sourceFormula
          + " (TMH \"ivy_scope_result\")))"
            " (TMH \"ivy_scope_result\")))";
        ChoiceNode support;
        support.step = closed.supportStep;
        support.hasResultFormula = true;
        support.resultFormula = proposition;
        support.producerProof = grouped->second.supportProof.render();
        for (std::size_t member : members) {
          support.parents.push_back(
            result.nodes[abstractScopes[member].sourceIndex].step);
        }
        std::sort(support.parents.begin(), support.parents.end());
        support.parents.erase(
          std::unique(support.parents.begin(), support.parents.end()),
          support.parents.end());
        supportNodes.push_back(std::move(support));
      } else {
        PreservedSexpr sourceFormula;
        if (!parser.parse(
              boundary.rootExistsScopeSourceFormula, sourceFormula)) {
          return false;
        }
        sourceFormula = canonicalizeScopeVariables(std::move(sourceFormula));
        sourceFormula = abstractAllWitnesses(std::move(sourceFormula));
        closed.context.hypothesis = scope.sourceHypothesis;
        closed.context.sourceFormula = sourceFormula.render();
        closed.supportStep = boundary.rootExistsScopeParent;
      }
      closedScopes.push_back(std::move(closed));
    }
    if (closedScopes.empty()) {
      error = "ground choice prooftrans produced no explicit scope context";
      return false;
    }

    std::map<std::string, std::string> stepByLocalHypothesis;
    for (const auto& entry : localHypotheses) {
      stepByLocalHypothesis.emplace(entry.second, entry.first);
    }
    const auto restoreParentReferences = [&]
      (PreservedSexpr value, const auto& self) -> PreservedSexpr {
      if (sexprHead(value, "hyp") && value.items.size() == 2) {
        std::string hypothesis;
        if (preservedName(value.items[1], hypothesis)) {
          auto parent = stepByLocalHypothesis.find(hypothesis);
          if (parent != stepByLocalHypothesis.end()) {
            return preservedList(
              preservedAtom("parent"),
              preservedAtom(quotePreservedName(parent->second)));
          }
        }
        return value;
      }
      if (value.atom) return value;
      for (std::size_t item = 1; item < value.items.size(); ++item) {
        value.items[item] = self(std::move(value.items[item]), self);
      }
      return value;
    };
    for (std::size_t index : scopedNodes) {
      ChoiceNode& node = result.nodes[index];
      PreservedSexpr proposition;
      if (!parser.parse(abstractPropositions.at(index), proposition)) {
        error = "ground choice prooftrans cannot serialize an abstract scoped result";
        return false;
      }
      if (sexprHead(proposition, "formula")
          && proposition.items.size() == 2) {
        node.hasResultFormula = true;
        node.hasResultClause = false;
        node.resultFormula = proposition.items[1].render();
        node.resultClause.clear();
      } else if (sexprHead(proposition, "clause")
                 && proposition.items.size() == 2
                 && sexprHead(proposition.items[1], "clause")) {
        node.hasResultFormula = false;
        node.hasResultClause = true;
        node.resultClause = proposition.items[1].render();
        node.resultFormula.clear();
      } else {
        error = "ground choice prooftrans abstract scoped result has no kernel shape";
        return false;
      }
      node.ivyContext.clear();
      for (const ClosedScopeFrame& scope : closedScopes) {
        node.ivyContext.push_back(scope.context);
      }
      node.hasRootExistsScope = false;
      node.rootExistsScopeAbstract = false;
      node.rootExistsScopeComplete = false;
      node.rootExistsScopeParent.clear();
      node.rootExistsScopeBridgeParents.clear();
      node.rootExistsScopeWitnessType.clear();
      node.rootExistsScopeWitnessBinder.clear();
      node.rootExistsScopeWitnessTerm.clear();
      node.rootExistsScopeSourceFormula.clear();
      node.rootExistsScopeTargetFormula.clear();
      node.rootExistsScopeBridgeProof.clear();
      node.rootExistsScopeSourceStep.clear();
      node.rootExistsScopeBoundaryCopy = false;
      node.producerCnfProjection.reset();
      node.producerCnfSourceFormula.clear();
      node.hasProducerGroundOrigin = false;
      node.producerGroundSourceNode.clear();
      node.producerGroundSourceInstance = 0;

      if (compactScopedNodes.find(index) != compactScopedNodes.end()) {
        bool termsOk = true;
        for (std::string& term : node.ivyJustification.terms) {
          std::string abstracted;
          termsOk = termsOk && abstractIvyTerm(node, term, abstracted);
          term = std::move(abstracted);
        }
        for (auto& arguments : node.ivyJustification.parentArguments) {
          for (std::string& term : arguments) {
            std::string abstracted;
            termsOk = termsOk && abstractIvyTerm(node, term, abstracted);
            term = std::move(abstracted);
          }
        }
        if (!node.ivyJustification.from.empty()) {
          std::string abstracted;
          termsOk = termsOk && abstractIvyTerm(
            node, node.ivyJustification.from, abstracted);
          node.ivyJustification.from = std::move(abstracted);
        }
        if (!node.ivyJustification.to.empty()) {
          std::string abstracted;
          termsOk = termsOk && abstractIvyTerm(
            node, node.ivyJustification.to, abstracted);
          node.ivyJustification.to = std::move(abstracted);
        }
        if (!termsOk) {
          error = "ground choice prooftrans cannot abstract compact Ivy payload at "
            + node.step;
          return false;
        }
        node.parents = node.ivyJustification.parents;
        std::sort(node.parents.begin(), node.parents.end());
        node.parents.erase(
          std::unique(node.parents.begin(), node.parents.end()),
          node.parents.end());
        node.producerProof.clear();
      } else {
        PreservedSexpr proof = restoreParentReferences(
          abstractProofs.at(index), restoreParentReferences);
        proof = freshenProofProgramBinders(
          std::move(proof), scopedProofBinderFresh);
        std::set<std::string> parents;
        collectProofParents(proof, parents, collectProofParents);
        node.parents.assign(parents.begin(), parents.end());
        node.producerProof = proof.render();
      }
    }

    const std::string publicFinalStep = groundId(0, source.finalStep);
    ChoiceNode& localFinal = result.nodes[finalIndex];
    const std::string localFinalStep = publicFinalStep + "_scope_body";
    localFinal.step = localFinalStep;
    PreservedSexpr localProof = preservedList(
      preservedAtom("parent"),
      preservedAtom(quotePreservedName(localFinalStep)));
    const auto eliminateScope = [&]
      (std::size_t index, PreservedSexpr proof, const auto& self)
        -> PreservedSexpr {
      if (index == closedScopes.size()) return proof;
      const ClosedScopeFrame& scope = closedScopes[index];
      PreservedSexpr witnessType;
      PreservedSexpr sourceFormula;
      if (!parser.parse(scope.context.witnessType, witnessType)
          || !parser.parse(scope.context.sourceFormula, sourceFormula)) {
        return PreservedSexpr{};
      }
      PreservedSexpr witness = preservedList(
        preservedAtom("term"),
        quotedTmh(quotePreservedName(scope.context.binder)));
      PreservedSexpr hypothesis = preservedList(
        preservedAtom("hyp"),
        preservedAtom(quotePreservedName(scope.context.hypothesis)));
      PreservedSexpr applied = preservedList(
        preservedAtom("proof_apply"),
        preservedList(
          preservedAtom("term_apply"), std::move(proof), std::move(witness)),
        std::move(hypothesis));
      PreservedSexpr continuation = preservedList(
        preservedAtom("term_lambda"),
        preservedAtom(quotePreservedName(scope.context.binder)),
        std::move(witnessType),
        preservedList(
          preservedAtom("proof_lambda"),
          preservedAtom(quotePreservedName(scope.context.hypothesis)),
          preservedList(preservedAtom("formula"), std::move(sourceFormula)),
          self(index + 1, std::move(applied), self)));
      return preservedList(
        preservedAtom("proof_apply"),
        preservedList(
          preservedAtom("term_apply"),
          preservedList(
            preservedAtom("parent"),
            preservedAtom(quotePreservedName(scope.supportStep))),
          preservedList(
            preservedAtom("formula"),
            quotedTmh(quotePreservedName("vampire_false")))),
        std::move(continuation));
    };
    PreservedSexpr dischargedProof = eliminateScope(
      0, std::move(localProof), eliminateScope);
    if (dischargedProof.items.empty()) {
      error = "ground choice prooftrans cannot encode explicit scope discharge";
      return false;
    }
    for (ChoiceNode& support : supportNodes) {
      result.nodes.push_back(std::move(support));
    }
    ChoiceNode final;
    final.step = publicFinalStep;
    final.hasResultClause = true;
    final.resultClause = "(clause)";
    final.producerProof = dischargedProof.render();
    final.parents.push_back(localFinalStep);
    for (const ClosedScopeFrame& scope : closedScopes) {
      final.parents.push_back(scope.supportStep);
    }
    std::sort(final.parents.begin(), final.parents.end());
    final.parents.erase(
      std::unique(final.parents.begin(), final.parents.end()),
      final.parents.end());
    result.nodes.push_back(std::move(final));
    for (std::size_t index = 0; index < result.nodes.size(); ++index) {
      result.nodes[index].index = index;
    }
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: explicit scoped Ivy DAG complete; nodes="
                << result.nodes.size() << "; ms="
                << certificateProfileMilliseconds() << std::endl;
    }
    abstractProofs.clear();
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scoped proof cache released; ms="
                << certificateProfileMilliseconds() << std::endl;
    }
    compactAbstractClauses.clear();
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: compact clause cache released; ms="
                << certificateProfileMilliseconds() << std::endl;
    }
    abstractEnvironments.clear();
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: abstract environments released; ms="
                << certificateProfileMilliseconds() << std::endl;
    }
    abstractPropositions.clear();
    abstractClauses.clear();
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scoped proposition caches released; ms="
                << certificateProfileMilliseconds() << std::endl;
    }
    groupedScopeReplay.clear();
    abstractScopes.clear();
    sharedDefinitionBodies.clear();
    if (certificateDebug) {
      std::cerr << "megalodon ground choice phase: scope syntax caches released; ms="
                << certificateProfileMilliseconds() << std::endl;
    }
  }
  environments.clear();
  if (certificateDebug) {
    std::cerr << "megalodon ground choice phase: ground environments released; ms="
              << certificateProfileMilliseconds() << std::endl;
  }
  producerSubstitutions.clear();
  if (certificateDebug) {
    std::cerr << "megalodon ground choice phase: producer substitutions released; ms="
              << certificateProfileMilliseconds() << std::endl;
  }
  finiteWitnessClasses.clear();
  pendingUniformScopes.clear();
  if (certificateDebug) {
    std::cerr << "megalodon ground choice phase: finite witness caches released; ms="
              << certificateProfileMilliseconds() << std::endl;
  }
  result.finalStep = groundId(0, source.finalStep);
  result.eliminatedSymbols = source.eliminatedSymbols;
  result.definitions = source.definitions;
  const bool hasExplicitIvyContext = std::any_of(
    result.nodes.begin(), result.nodes.end(),
    [](const ChoiceNode& node) { return !node.ivyContext.empty(); });
  // Scoped nodes retain compact Ivy results directly.  Re-sharing their large
  // contextual propositions would parse the whole DAG a second time and does
  // not reduce any inference payload.
  if (!hasExplicitIvyContext
      && !shareRepeatedChoicePropositions(result, error)) return false;
  const bool hasRootExistsScope = std::any_of(
    result.nodes.begin(), result.nodes.end(),
    [](const ChoiceNode& node) { return node.hasRootExistsScope; });
  result.version = hasExplicitIvyContext
    ? "ivy_ground_scoped_choice_dag_v1"
    : (result.definitions.empty()
       ? (hasRootExistsScope
          ? "ivy_ground_choice_dag_v2" : "ivy_ground_choice_dag_v1")
       : "ivy_ground_choice_dag_v3");
  return true;
}

bool expandEnnfFormulaProof(
  const std::string& stepId,
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const MegalodonKernelSyntax::RenderedKernelEnnfTrace& trace,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (!builder.ennfFormula(
        stepId, parentId, parentArguments, trace, result, error)) {
    if (error.empty()) {
      error = "ENNF trace does not lower to an explicit producer Ivy proof";
    }
    return false;
  }
  return true;
}

bool buildFoolFormulaProgram(
  const std::string& sourceFormula,
  const std::string& targetFormula,
  MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
  std::string& error,
  bool allowJunctionReassociation)
{
  PreservedSexprParser parser;
  PreservedSexpr source;
  PreservedSexpr target;
  std::size_t nextIndex = 0;
  if (!parser.parse(sourceFormula, source)
      || !parser.parse(targetFormula, target)
      || !buildFoolProgramNode(
           source, target, true, {}, nextIndex, program.root, nullptr,
           allowJunctionReassociation)) {
    error = "FOOL formulas do not produce a typed recorder program";
    return false;
  }
  return true;
}

bool alphaEquivalentTermSexpr(
  const std::string& leftText,
  const std::string& rightText)
{
  PreservedSexprParser parser;
  PreservedSexpr left;
  PreservedSexpr right;
  return parser.parse(leftText, left)
    && parser.parse(rightText, right)
    && alphaEquivalentSexpr(left, right);
}

bool expandAvatarSatResolutionProof(
  const std::string& leftParentId,
  const std::vector<std::string>& leftLiterals,
  std::size_t leftPivot,
  const std::string& rightParentId,
  const std::vector<std::string>& rightLiterals,
  std::size_t rightPivot,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  return expandClauseResolutionProof(
    leftParentId, {}, leftLiterals, leftPivot,
    rightParentId, {}, rightLiterals, rightPivot,
    resultLiterals, result, error);
}

bool expandClauseResolutionProof(
  const std::string& leftParentId,
  const std::vector<std::string>& leftParentArguments,
  const std::vector<std::string>& leftLiterals,
  std::size_t leftPivot,
  const std::string& rightParentId,
  const std::vector<std::string>& rightParentArguments,
  const std::vector<std::string>& rightLiterals,
  std::size_t rightPivot,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (leftParentId.empty() || rightParentId.empty()
      || !builder.resolution(
           leftParentId, leftParentArguments, leftLiterals, leftPivot,
           rightParentId, rightParentArguments, rightLiterals, rightPivot,
           resultLiterals, result)) {
    error = "AVATAR SAT resolution is not the declared producer pivot step";
    return false;
  }
  return true;
}

bool expandClauseEqualityResolutionProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (parentId.empty()
      || !builder.equalityResolution(
           parentId,
           parentArguments,
           sourceLiterals,
           selectedLiteral,
           resultLiterals,
           result)) {
    error = "equality resolution is not a reflexive producer disequality step";
    return false;
  }
  return true;
}

bool expandClauseEqualitySymmetryProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (parentId.empty()
      || !builder.equalitySymmetry(
           parentId,
           parentArguments,
           sourceLiterals,
           selectedLiteral,
           resultLiterals,
           result)) {
    error = "equality symmetry is not the declared producer equality swap";
    return false;
  }
  return true;
}

bool expandClauseTruthConflictProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (parentId.empty()
      || !builder.truthConflict(
           parentId,
           parentArguments,
           sourceLiterals,
           selectedLiteral,
           resultLiterals,
           result)) {
    error = "truth conflict is not a declared producer true/false equality";
    return false;
  }
  return true;
}

bool planClauseBoolSimplification(
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  ClauseBoolSimplificationPlan& plan,
  std::string& error)
{
  PreservedSexprParser parser;
  std::vector<PreservedSexpr> source;
  std::vector<PreservedSexpr> target;
  for (const std::string& literal : sourceLiterals) {
    PreservedSexpr parsed;
    if (!parser.parse(literal, parsed)) {
      error = "Boolean simplification source clause is unreadable";
      return false;
    }
    source.push_back(std::move(parsed));
  }
  for (const std::string& literal : resultLiterals) {
    PreservedSexpr parsed;
    if (!parser.parse(literal, parsed)) {
      error = "Boolean simplification result clause is unreadable";
      return false;
    }
    target.push_back(std::move(parsed));
  }
  if (source.size() != target.size()) {
    error = "Boolean simplification changes clause length";
    return false;
  }

  const auto isTrue = [](const PreservedSexpr& value) {
    return namedTermSexpr(value, "vampire_true")
      || namedTermSexpr(value, "f__true");
  };
  const auto isFalse = [](const PreservedSexpr& value) {
    return namedTermSexpr(value, "vampire_false")
      || namedTermSexpr(value, "f__false");
  };
  const auto isNot = [](const PreservedSexpr& value,
                        PreservedSexpr& argument) {
    if (!sexprHead(value, "AP") || value.items.size() != 3
        || !namedTermSexpr(value.items[1], "vNOT")) {
      return false;
    }
    argument = value.items[2];
    return true;
  };
  std::function<bool(
    const PreservedSexpr&,
    const PreservedSexpr&,
    std::vector<unsigned>&,
    PreservedSexpr&,
    PreservedSexpr&)> findRewrite;
  findRewrite = [&](const PreservedSexpr& fromTerm,
                    const PreservedSexpr& toTerm,
                    std::vector<unsigned>& position,
                    PreservedSexpr& from,
                    PreservedSexpr& to) {
    if (fromTerm == toTerm) return false;
    PreservedSexpr negated;
    if (isNot(fromTerm, negated)
        && ((isTrue(negated) && isFalse(toTerm))
            || (isFalse(negated) && isTrue(toTerm)))) {
      from = fromTerm;
      to = toTerm;
      return true;
    }
    bool found = false;
    std::vector<unsigned> foundPosition;
    PreservedSexpr foundFrom;
    PreservedSexpr foundTo;
    for (unsigned child = 0; child < 2; ++child) {
      const PreservedSexpr* fromChild = sexprTermChild(fromTerm, child);
      const PreservedSexpr* toChild = sexprTermChild(toTerm, child);
      if ((fromChild == nullptr) != (toChild == nullptr)) return false;
      if (fromChild == nullptr || *fromChild == *toChild) continue;
      std::vector<unsigned> childPosition;
      PreservedSexpr childFrom;
      PreservedSexpr childTo;
      if (found || !findRewrite(
            *fromChild, *toChild,
            childPosition, childFrom, childTo)) {
        return false;
      }
      found = true;
      foundPosition.push_back(child);
      foundPosition.insert(
        foundPosition.end(), childPosition.begin(), childPosition.end());
      foundFrom = std::move(childFrom);
      foundTo = std::move(childTo);
    }
    if (!found) return false;
    position = std::move(foundPosition);
    from = std::move(foundFrom);
    to = std::move(foundTo);
    return true;
  };
  const auto sameClauseMultiset = [](std::vector<std::string> left,
                                     std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };

  std::vector<ClauseBoolSimplificationPlan> candidates;
  for (std::size_t sourceIndex = 0;
       sourceIndex < source.size();
       ++sourceIndex) {
    const PreservedSexpr& sourceLiteral = source[sourceIndex];
    if ((!sexprHead(sourceLiteral, "pos")
         && !sexprHead(sourceLiteral, "neg"))
        || sourceLiteral.items.size() != 2) {
      continue;
    }
    for (const PreservedSexpr& targetLiteral : target) {
      if (targetLiteral.items.size() != 2
          || targetLiteral.items[0] != sourceLiteral.items[0]) {
        continue;
      }
      const auto addCandidate = [&](const PreservedSexpr& rewrittenAtom,
                                    bool symmetry) {
        std::vector<unsigned> position;
        PreservedSexpr from;
        PreservedSexpr to;
        if (!findRewrite(
              sourceLiteral.items[1], rewrittenAtom,
              position, from, to)) {
          return;
        }
        std::vector<std::string> rewritten = sourceLiterals;
        rewritten[sourceIndex] =
          literalSexpr(
            sexprHead(sourceLiteral, "pos"), rewrittenAtom).render();
        const std::vector<std::string>& expected = symmetry
          ? rewritten : resultLiterals;
        if (!sameClauseMultiset(rewritten, expected)) return;
        if (symmetry) {
          std::vector<std::string> symmetric = rewritten;
          symmetric[sourceIndex] = targetLiteral.render();
          if (!sameClauseMultiset(symmetric, resultLiterals)) return;
        }
        ClauseBoolSimplificationPlan candidate;
        candidate.selectedLiteral = sourceIndex;
        candidate.position = std::move(position);
        candidate.from = from.render();
        candidate.to = to.render();
        candidate.rewrittenLiterals = std::move(rewritten);
        candidate.requiresEqualitySymmetry = symmetry;
        candidates.push_back(std::move(candidate));
      };

      addCandidate(targetLiteral.items[1], false);
      PreservedSexpr targetType;
      PreservedSexpr targetLeft;
      PreservedSexpr targetRight;
      if (typedEqualitySexpr(
            targetLiteral.items[1],
            targetType, targetLeft, targetRight)) {
        addCandidate(
          equalityAtomSexpr(targetType, targetRight, targetLeft),
          true);
      }
    }
  }
  if (candidates.size() != 1) {
    error = candidates.empty()
      ? "Boolean simplification has no exact logical rewrite plan"
      : "Boolean simplification has multiple exact logical rewrite plans";
    return false;
  }
  plan = std::move(candidates.front());
  return true;
}

bool expandClauseBoolSimplificationProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArguments,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  const std::vector<unsigned>& position,
  const std::string& from,
  const std::string& to,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (!builder.boolSimplification(
        parentId,
        parentArguments,
        sourceLiterals,
        selectedLiteral,
        position,
        from,
        to,
        resultLiterals,
        result)) {
    error = "Boolean simplification is not a supported producer rewrite";
    return false;
  }
  return true;
}

bool expandClauseInstantiationProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArgumentTerms,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (!builder.instantiation(parentId, parentArgumentTerms, result)) {
    error = "cannot build explicit producer parent instantiation";
    return false;
  }
  return true;
}

bool expandClauseSubstitutionProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArgumentTerms,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  std::string instantiated;
  if (!builder.instantiation(
        parentId, parentArgumentTerms, instantiated)
      || !builder.projectionFromProof(
        instantiated, sourceLiterals, resultLiterals, result)) {
    error = "cannot build explicit producer substitution and clause projection";
    return false;
  }
  return true;
}

bool expandClauseEqualityFactoringProof(
  const std::string& parentId,
  const std::vector<std::string>& parentArgumentTerms,
  const std::vector<std::string>& sourceLiterals,
  std::size_t selectedLiteral,
  std::size_t otherLiteral,
  const std::string& selectedSharedTerm,
  const std::string& otherOtherTerm,
  const std::vector<std::string>& resultLiterals,
  std::string& result,
  std::string& error)
{
  IvyClauseProofBuilder builder;
  if (parentId.empty()
      || !builder.equalityFactoring(
           parentId,
           parentArgumentTerms,
           sourceLiterals,
           selectedLiteral,
           otherLiteral,
           selectedSharedTerm,
           otherOtherTerm,
           resultLiterals,
           result)) {
    error = "equality factoring is not the declared producer factoring step";
    return false;
  }
  return true;
}

bool expandClauseParamodulationProof(
  const std::string& equalityParentId,
  const std::vector<std::string>& equalityParentArguments,
  const std::vector<std::string>& equalityLiterals,
  std::size_t equalityLiteral,
  const std::string& targetParentId,
  const std::vector<std::string>& targetParentArguments,
  const std::vector<std::string>& targetLiterals,
  std::size_t targetLiteral,
  const std::vector<unsigned>& position,
  const std::string& from,
  const std::string& to,
  const std::string& rewrittenLiteral,
  const std::vector<std::string>& resultLiterals,
  bool rewriteSymmetry,
  std::string& result,
  std::string& error,
  const std::string& scopedLambdaBodyType,
  bool* usedScopedLambda,
  std::string* scopedParentParameter)
{
  IvyClauseProofBuilder builder;
  if (equalityParentId.empty() || targetParentId.empty()
      || !builder.paramodulation(
           equalityParentId,
           equalityParentArguments,
           equalityLiterals,
           equalityLiteral,
           targetParentId,
           targetParentArguments,
           targetLiterals,
           targetLiteral,
           position,
           from,
           to,
           rewrittenLiteral,
           resultLiterals,
           rewriteSymmetry,
           scopedLambdaBodyType,
           result,
           false,
           nullptr,
           usedScopedLambda,
           scopedParentParameter)) {
    error = "paramodulation is not the declared producer rewrite step";
    return false;
  }
  return true;
}

bool expandScopedLambdaChoiceParamodulationProof(
  const std::string& equalityParentId,
  const std::vector<std::string>& equalityParentArguments,
  const std::vector<std::string>& equalityLiterals,
  std::size_t equalityLiteral,
  const std::string& targetParentId,
  const std::vector<std::string>& targetParentArguments,
  const std::vector<std::string>& targetLiterals,
  std::size_t targetLiteral,
  const std::vector<unsigned>& position,
  const std::string& from,
  const std::string& to,
  const std::string& rewrittenLiteral,
  const std::vector<std::string>& originalResultLiterals,
  bool rewriteSymmetry,
  const std::string& scopedLambdaBodyType,
  MegalodonKernelSyntax::ProducerScopedLambdaChoice& result,
  std::string& error)
{
  result = {};
  IvyClauseProofBuilder builder;
  std::string proof;
  if (equalityParentId.empty() || targetParentId.empty()
      || !builder.paramodulation(
           equalityParentId,
           equalityParentArguments,
           equalityLiterals,
           equalityLiteral,
           targetParentId,
           targetParentArguments,
           targetLiterals,
           targetLiteral,
           position,
           from,
           to,
           rewrittenLiteral,
           originalResultLiterals,
           rewriteSymmetry,
           scopedLambdaBodyType,
           proof,
           true,
           &result)
      || result.parameter.empty() || result.parameterType.empty()
      || result.witnessTerm.empty() || result.resultClause.empty()
      || result.resultLiterals.empty() || result.producerProof.empty()) {
    result = {};
    error = "scoped lambda choice lowering is not the declared producer rewrite step";
    return false;
  }
  return true;
}

bool expandAvatarContradictionProof(
  const AvatarContradictionProofRequest& request,
  std::string& result,
  std::string& error)
{
  auto quote = [](const std::string& value) {
    std::string rendered = "\"";
    for (char ch : value) {
      switch (ch) {
        case '\\': rendered += "\\\\"; break;
        case '"': rendered += "\\\""; break;
        case '\n': rendered += "\\n"; break;
        case '\r': rendered += "\\r"; break;
        case '\t': rendered += "\\t"; break;
        default: rendered += ch; break;
      }
    }
    return rendered + '"';
  };
  auto literalFormula = [](const std::string& literal, std::string& formula) {
    if (literal.size() < 7 || literal.back() != ')') {
      return false;
    }
    const bool positive = literal.compare(0, 5, "(pos ") == 0;
    const bool negative = literal.compare(0, 5, "(neg ") == 0;
    if (!positive && !negative) {
      return false;
    }
    const std::string atom = literal.substr(5, literal.size() - 6);
    formula = positive
      ? atom
      : "(IMP " + atom + " (TMH \"vampire_false\"))";
    return true;
  };
  auto formulaOr = [](const std::string& left, const std::string& right) {
    return "(AP (AP (TMH \"vampire_or\") " + left + ") " + right + ")";
  };
  if (request.parentId.empty() || request.sourceLiterals.empty()) {
    error = "AVATAR contradiction direct proof has an empty parent or source";
    return false;
  }

  std::vector<std::string> literalFormulas(request.sourceLiterals.size());
  for (std::size_t index = 0; index < request.sourceLiterals.size(); ++index) {
    if (!literalFormula(request.sourceLiterals[index], literalFormulas[index])) {
      error = "AVATAR contradiction direct proof has a malformed source literal";
      return false;
    }
  }
  std::string foldedTargetFormula;
  for (std::size_t offset = 0; offset < literalFormulas.size(); ++offset) {
    const std::size_t index = literalFormulas.size() - offset - 1;
    foldedTargetFormula = foldedTargetFormula.empty()
      ? literalFormulas[index]
      : formulaOr(foldedTargetFormula, literalFormulas[index]);
  }
  std::vector<std::string> normalizedResult(
    request.sourceLiterals.rbegin(), request.sourceLiterals.rend());
  const bool legacyFold =
    request.resultLiterals.size() == 1
    && request.resultLiterals.front() == "(pos " + foldedTargetFormula + ")";
  if (!legacyFold && request.resultLiterals != normalizedResult) {
    error = "AVATAR contradiction direct proof result is not the producer split-clause normalization";
    return false;
  }
  if (!legacyFold) {
    std::string sourceProof = "(parent " + quote(request.parentId) + ")";
    for (const std::string& argument : request.parentArguments) {
      sourceProof = "(term_apply " + sourceProof
        + " (term (TMH " + quote(argument) + ")))";
    }
    IvyClauseProofBuilder builder;
    if (!builder.projectionFromProof(
          sourceProof,
          request.sourceLiterals,
          request.resultLiterals,
          result)) {
      error = "AVATAR contradiction direct proof could not normalize its split clause";
      return false;
    }
    return true;
  }
  std::string targetFormula = foldedTargetFormula;

  auto formula = [](const std::string& value) {
    return "(formula " + value + ")";
  };
  auto literal = [](const std::string& value) {
    return "(literal " + value + ")";
  };
  auto clause = [](const std::vector<std::string>& literals) {
    std::string value = "(clause (clause";
    for (const std::string& literal : literals) {
      value += " " + literal;
    }
    return value + "))";
  };
  auto hypothesis = [&](const std::string& name) {
    return "(hyp " + quote(name) + ")";
  };
  auto termApply = [](const std::string& proof, const std::string& term) {
    return "(term_apply " + proof + " " + term + ")";
  };
  auto proofApply = [](const std::string& left, const std::string& right) {
    return "(proof_apply " + left + " " + right + ")";
  };
  auto proofLambda = [&](const std::string& name,
                         const std::string& proposition,
                         const std::string& body) {
    return "(proof_lambda " + quote(name) + " " + proposition
      + " " + body + ")";
  };
  auto termLambda = [&](const std::string& name,
                        const std::string& type,
                        const std::string& body) {
    return "(term_lambda " + quote(name) + " " + type
      + " " + body + ")";
  };
  auto formulaImp = [](const std::string& left, const std::string& right) {
    return "(IMP " + left + " " + right + ")";
  };

  std::size_t fresh = 0;
  auto freshName = [&](const char* prefix) {
    return std::string("ivy_") + prefix + std::to_string(fresh++);
  };
  auto orIntroduction = [&](const std::string& left,
                            const std::string& right,
                            const std::string& proof,
                            bool injectLeft) {
    const std::string resultName = freshName("q");
    const std::string leftName = freshName("left");
    const std::string rightName = freshName("right");
    const std::string resultVariable = "(TMH " + quote(resultName) + ")";
    return termLambda(
      resultName,
      "(PROP)",
      proofLambda(
        leftName,
        formula(formulaImp(left, resultVariable)),
        proofLambda(
          rightName,
          formula(formulaImp(right, resultVariable)),
          proofApply(hypothesis(injectLeft ? leftName : rightName), proof))));
  };

  std::vector<std::size_t> literalOrder;
  literalOrder.reserve(literalFormulas.size());
  for (std::size_t offset = 0; offset < literalFormulas.size(); ++offset) {
    literalOrder.push_back(literalFormulas.size() - offset - 1);
  }
  std::function<std::string(
    const std::vector<std::size_t>&, std::size_t, const std::string&)>
    inject;
  inject = [&](const std::vector<std::size_t>& order,
               std::size_t sourceIndex,
               const std::string& proof) -> std::string {
    if (order.size() == 1) {
      return order.front() == sourceIndex ? proof : std::string();
    }
    std::vector<std::size_t> prefix(order.begin(), order.end() - 1);
    const std::size_t last = order.back();
    std::string left = literalFormulas[prefix.front()];
    for (std::size_t index = 1; index < prefix.size(); ++index) {
      left = formulaOr(left, literalFormulas[prefix[index]]);
    }
    if (last == sourceIndex) {
      return orIntroduction(left, literalFormulas[last], proof, false);
    }
    const std::string inner = inject(prefix, sourceIndex, proof);
    return inner.empty()
      ? std::string()
      : orIntroduction(left, literalFormulas[last], inner, true);
  };

  std::function<std::string(std::size_t, const std::string&)> consume;
  consume = [&](std::size_t sourceIndex,
                const std::string& sourceProof) -> std::string {
    if (sourceIndex + 1 == request.sourceLiterals.size()) {
      return inject(literalOrder, sourceIndex, sourceProof);
    }
    const std::string leftName = freshName("source");
    const std::string restName = freshName("rest");
    const std::vector<std::string> rest(
      request.sourceLiterals.begin() + sourceIndex + 1,
      request.sourceLiterals.end());
    const std::string leftBranch = proofLambda(
      leftName,
      literal(request.sourceLiterals[sourceIndex]),
      inject(literalOrder, sourceIndex, hypothesis(leftName)));
    const std::string rightBranch = proofLambda(
      restName,
      clause(rest),
      consume(sourceIndex + 1, hypothesis(restName)));
    return proofApply(
      proofApply(
        termApply(sourceProof, formula(targetFormula)),
        leftBranch),
      rightBranch);
  };

  std::string parentProof = "(parent " + quote(request.parentId) + ")";
  for (const std::string& argument : request.parentArguments) {
    parentProof = termApply(
      parentProof,
      "(term (TMH " + quote(argument) + "))");
  }
  result = consume(0, parentProof);
  if (result.empty()) {
    error = "AVATAR contradiction direct proof could not inject a source literal";
    return false;
  }
  return true;
}

bool expandAvatarComponentProof(
  const AvatarComponentProofRequest& request,
  std::string& result,
  std::string& error,
  MegalodonKernelSyntax::ProducerScopedLambdaChoice* scopedChoice)
{
  auto quote = [](const std::string& value) {
    std::string rendered = "\"";
    for (char ch : value) {
      if (ch == '\\' || ch == '"') rendered += '\\';
      rendered += ch;
    }
    return rendered + '"';
  };
  auto literalFormula = [](const std::string& literal, std::string& formula) {
    if (literal.size() < 7 || literal.back() != ')') return false;
    const bool positive = literal.compare(0, 5, "(pos ") == 0;
    const bool negative = literal.compare(0, 5, "(neg ") == 0;
    if (!positive && !negative) return false;
    const std::string atom = literal.substr(5, literal.size() - 6);
    formula = positive ? atom : "(IMP " + atom + " (TMH \"vampire_false\"))";
    return true;
  };
  auto complement = [](const std::string& literal) {
    if (literal.compare(0, 5, "(pos ") == 0) return "(neg " + literal.substr(5);
    if (literal.compare(0, 5, "(neg ") == 0) return "(pos " + literal.substr(5);
    return std::string();
  };
  auto sameMultiset = [](std::vector<std::string> left,
                         std::vector<std::string> right) {
    std::sort(left.begin(), left.end());
    std::sort(right.begin(), right.end());
    return left == right;
  };
  auto formulaOr = [](const std::string& left, const std::string& right) {
    return "(AP (AP (TMH \"vampire_or\") " + left + ") " + right + ")";
  };
  auto formulaImp = [](const std::string& left, const std::string& right) {
    return "(IMP " + left + " " + right + ")";
  };
  auto formula = [](const std::string& value) { return "(formula " + value + ")"; };
  auto clauseTerm = [](const std::vector<std::string>& literals) {
    std::string value = "(clause (clause";
    for (const std::string& literal : literals) value += " " + literal;
    return value + "))";
  };
  auto clauseValue = [](const std::vector<std::string>& literals) {
    std::string value = "(clause";
    for (const std::string& literal : literals) value += " " + literal;
    return value + ")";
  };
  auto hypothesis = [&](const std::string& name) { return "(hyp " + quote(name) + ")"; };
  auto definition = [&](const std::string& name) { return "(definition " + quote(name) + ")"; };
  auto known = [&](const std::string& name) { return "(known " + quote(name) + ")"; };
  auto termApply = [](const std::string& proof, const std::string& term) {
    return "(term_apply " + proof + " " + term + ")";
  };
  auto proofApply = [](const std::string& left, const std::string& right) {
    return "(proof_apply " + left + " " + right + ")";
  };
  auto proofLambda = [&](const std::string& name, const std::string& prop,
                         const std::string& body) {
    return "(proof_lambda " + quote(name) + " " + prop + " " + body + ")";
  };
  auto termLambda = [&](const std::string& name, const std::string& type,
                        const std::string& body) {
    return "(term_lambda " + quote(name) + " " + type + " " + body + ")";
  };
  auto clauseFormula = [&](const std::vector<std::string>& literals,
                           std::string& value) {
    if (literals.empty()) return false;
    std::vector<std::string> formulas;
    for (const std::string& literal : literals) {
      std::string item;
      if (!literalFormula(literal, item)) return false;
      formulas.push_back(std::move(item));
    }
    value = formulas.back();
    for (std::size_t offset = formulas.size() - 1; offset > 0; --offset) {
      value = formulaOr(formulas[offset - 1], value);
    }
    return true;
  };

  std::size_t fresh = 0;
  auto freshName = [&](const char* prefix) {
    return std::string("ivy_component_") + prefix + std::to_string(fresh++);
  };
  std::function<std::string(
    const std::vector<std::string>&, std::size_t, const std::string&)> inject;
  inject = [&](const std::vector<std::string>& target, std::size_t index,
               const std::string& proof) -> std::string {
    if (target.size() == 1) return index == 0 ? proof : std::string();
    const std::string qName = freshName("q");
    const std::string leftName = freshName("left");
    const std::string rightName = freshName("right");
    std::vector<std::string> rest(target.begin() + 1, target.end());
    std::string leftFormula;
    std::string rightFormula;
    if (!literalFormula(target.front(), leftFormula)
        || !clauseFormula(rest, rightFormula)) return std::string();
    const std::string q = "(TMH " + quote(qName) + ")";
    const std::string selected = index == 0
      ? proofApply(hypothesis(leftName), proof)
      : proofApply(hypothesis(rightName), inject(rest, index - 1, proof));
    return termLambda(
      qName, "(PROP)",
      proofLambda(
        leftName, formula(formulaImp(leftFormula, q)),
        proofLambda(rightName, formula(formulaImp(rightFormula, q)), selected)));
  };
  auto injectLiteral = [&](const std::string& literal, const std::string& proof) {
    auto position = std::find(
      request.resultLiterals.begin(), request.resultLiterals.end(), literal);
    return position == request.resultLiterals.end()
      ? std::string()
      : inject(
          request.resultLiterals,
          static_cast<std::size_t>(position - request.resultLiterals.begin()),
          proof);
  };
  std::function<std::string(
    const std::vector<std::string>&, std::size_t, const std::string&)> project;
  project = [&](const std::vector<std::string>& source, std::size_t index,
                const std::string& proof) -> std::string {
    const std::string injected = injectLiteral(source[index], hypothesis("ivy_component_source" + std::to_string(index)));
    if (injected.empty()) return std::string();
    if (index + 1 == source.size()) return injectLiteral(source[index], proof);
    const std::string headName = "ivy_component_source" + std::to_string(index);
    const std::string restName = "ivy_component_rest" + std::to_string(index);
    std::vector<std::string> rest(source.begin() + index + 1, source.end());
    std::string headFormula;
    if (!literalFormula(source[index], headFormula)) return std::string();
    return proofApply(
      proofApply(
        termApply(proof, clauseTerm(request.resultLiterals)),
        proofLambda(headName, formula(headFormula), injected)),
      proofLambda(restName, clauseTerm(rest), project(source, index + 1, hypothesis(restName))));
  };
  auto excludedMiddle = [&](const std::string& prop, const std::string& target,
                            const std::string& trueName, const std::string& trueProof,
                            const std::string& falseName, const std::string& falseProof) {
    const std::string qName = freshName("xm_q");
    const std::string leftName = freshName("xm_left");
    const std::string rightName = freshName("xm_right");
    const std::string notQName = freshName("xm_not_q");
    const std::string propName = freshName("xm_prop");
    const std::string q = "(TMH " + quote(qName) + ")";
    const std::string falseFormula = "(TMH \"vampire_false\")";
    const std::string leftResult =
      proofApply(hypothesis(leftName), hypothesis(propName));
    const std::string notProp = proofLambda(
      propName, formula(prop),
      proofApply(hypothesis(notQName), leftResult));
    const std::string rightResult = proofApply(hypothesis(rightName), notProp);
    const std::string contradiction =
      proofApply(hypothesis(notQName), rightResult);
    const std::string dneg = proofApply(
      termApply(
        known("e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0"),
        formula(q)),
      proofLambda(notQName, formula(formulaImp(q, falseFormula)), contradiction));
    const std::string xm = termLambda(
      qName, "(PROP)",
      proofLambda(
        leftName, formula(formulaImp(prop, q)),
        proofLambda(
          rightName, formula(formulaImp(formulaImp(prop, falseFormula), q)),
          dneg)));
    return proofApply(
      proofApply(
        termApply(xm, formula(target)),
        proofLambda(trueName, formula(prop), trueProof)),
      proofLambda(falseName, formula(formulaImp(prop, falseFormula)), falseProof));
  };

  std::string targetFormula;
  if (!clauseFormula(request.resultLiterals, targetFormula)) {
    error = "AVATAR component direct proof has an empty or malformed result";
    return false;
  }
  for (const AvatarComponentDefinition& item : request.definitions) {
    const std::string splitName = "split_" + std::to_string(item.splitVariable);
    const std::string splitAtom = "(TMH " + quote(splitName) + ")";
    const std::string negativeSplit = "(neg " + splitAtom + ")";
    const std::string positiveSplit = "(pos " + splitAtom + ")";
    std::vector<std::string> negativeExpected = item.componentLiterals;
    negativeExpected.push_back(negativeSplit);
    const bool negativeDirection = sameMultiset(request.resultLiterals, negativeExpected);
    const bool positiveDirection =
      item.componentLiterals.size() == 1
      && sameMultiset(
           request.resultLiterals,
           {complement(item.componentLiterals.front()), positiveSplit});
    if (!negativeDirection && !positiveDirection) continue;

    std::string componentFormula;
    if (!clauseFormula(item.componentLiterals, componentFormula)) continue;
    for (auto variable = item.componentVariables.rbegin();
         variable != item.componentVariables.rend(); ++variable) {
      componentFormula = "(ALLV " + quote(variable->first) + " "
        + variable->second.sexpr + " " + componentFormula + ")";
    }
    const std::string left = formulaImp(splitAtom, componentFormula);
    const std::string right = formulaImp(componentFormula, splitAtom);
    auto selectDefinition = [&](bool selectLeft) {
      const std::string leftName = freshName("definition_left");
      const std::string rightName = freshName("definition_right");
      const std::string selectedProp = selectLeft ? left : right;
      return proofApply(
        termApply(definition(item.id), formula(selectedProp)),
        proofLambda(
          leftName, formula(left),
          proofLambda(
            rightName, formula(right),
            hypothesis(selectLeft ? leftName : rightName))));
    };

    if (negativeDirection) {
      const std::string splitProofName = freshName("split");
      const std::string notSplitName = freshName("not_split");
      std::string componentProof = proofApply(
        selectDefinition(true), hypothesis(splitProofName));
      for (const auto& variable : item.componentVariables) {
        auto resultVariable = std::find_if(
          request.resultVariables.begin(), request.resultVariables.end(),
          [&](const auto& candidate) { return candidate.first == variable.first; });
        if (resultVariable == request.resultVariables.end()) {
          error = "AVATAR component direct proof cannot map a component variable";
          return false;
        }
        componentProof = termApply(
          componentProof, "(term (TMH " + quote(resultVariable->first) + "))");
      }
      const std::string trueProof = project(item.componentLiterals, 0, componentProof);
      const std::string falseProof = injectLiteral(negativeSplit, hypothesis(notSplitName));
      if (trueProof.empty() || falseProof.empty()) continue;
      result = excludedMiddle(
        splitAtom, targetFormula,
        splitProofName, trueProof,
        notSplitName, falseProof);
    } else {
      if (!item.componentVariables.empty()) {
        if (scopedChoice == nullptr || item.componentVariables.size() != 1) {
          error = "positive AVATAR component direct proof requires one explicit counterexample witness";
          return false;
        }
        const auto& variable = item.componentVariables.front();
        auto resultVariable = std::find_if(
          request.resultVariables.begin(), request.resultVariables.end(),
          [&](const auto& candidate) {
            return candidate.first == variable.first
              && candidate.second.sexpr == variable.second.sexpr;
          });
        if (resultVariable == request.resultVariables.end()) {
          error = "positive AVATAR component counterexample has no result-variable binding";
          return false;
        }
        const std::string& type = variable.second.sexpr;
        std::string epsilon;
        std::string notForall;
        std::string choice;
        if (type == "(SET)") {
          epsilon = "Eps_i";
          notForall = "vampire_not_forall_exists_set";
          choice = "vampire_exists_set_choice";
        } else if (type == "(PROP)") {
          epsilon = "Eps_prop";
          notForall = "vampire_not_forall_exists_prop";
          choice = "vampire_exists_prop_choice";
        } else if (type == "(AR (SET) (PROP))") {
          epsilon = "Eps_set_prop";
          notForall = "vampire_not_forall_exists_set_prop";
          choice = "vampire_exists_set_prop_choice";
        } else if (type == "(AR (SET) (SET))") {
          epsilon = "Eps_set_set";
          notForall = "vampire_not_forall_exists_set_set";
          choice = "vampire_exists_set_set_choice";
        } else if (type == "(AR (SET) (AR (SET) (PROP)))") {
          epsilon = "Eps_set_set_prop";
          notForall = "vampire_not_forall_exists_set_set_prop";
          choice = "vampire_exists_set_set_prop_choice";
        } else {
          error = "positive AVATAR component counterexample has no typed choice operator";
          return false;
        }

        const std::string componentLiteral = item.componentLiterals.front();
        std::string openBody;
        if (!literalFormula(componentLiteral, openBody)) {
          error = "positive AVATAR component counterexample has a malformed body";
          return false;
        }
        const std::string positivePredicate =
          "(LAMV " + quote(variable.first) + " " + type + " "
          + openBody + ")";
        const std::string negativePredicate =
          "(LAMV " + quote(variable.first) + " " + type + " (IMP "
          + openBody + " (TMH \"vampire_false\")))";
        const std::string witness =
          "(AP (TMH " + quote(epsilon) + ") " + negativePredicate + ")";

        PreservedSexprParser parser;
        PreservedSexpr witnessTerm;
        if (!parser.parse(witness, witnessTerm)) {
          error = "positive AVATAR component counterexample witness does not parse";
          return false;
        }
        std::vector<std::string> effectiveResult;
        for (const std::string& literalText : request.resultLiterals) {
          PreservedSexpr literal;
          if (!parser.parse(literalText, literal)) {
            error = "positive AVATAR component result literal does not parse";
            return false;
          }
          effectiveResult.push_back(
            substituteNamedVariableSexpr(
              literal, variable.first, witnessTerm).render());
        }
        std::string effectiveTargetFormula;
        if (!clauseFormula(effectiveResult, effectiveTargetFormula)) {
          error = "positive AVATAR component counterexample result is malformed";
          return false;
        }
        PreservedSexpr complemented;
        if (!parser.parse(complement(componentLiteral), complemented)) {
          error = "positive AVATAR component complement does not parse";
          return false;
        }
        const std::string witnessComplement =
          substituteNamedVariableSexpr(
            complemented, variable.first, witnessTerm).render();

        const std::string notSplitName = freshName("not_split");
        const std::string closedComponentName = freshName("closed_component");
        const std::string pointwiseName = freshName("pointwise");
        const std::string notClosedComponent = proofLambda(
          closedComponentName,
          formula(componentFormula),
          proofApply(
            hypothesis(notSplitName),
            proofApply(
              selectDefinition(false),
              hypothesis(closedComponentName))));
        const std::string pointwise = termLambda(
          variable.first,
          type,
          proofLambda(
            pointwiseName,
            formula(formulaImp(openBody, "(TMH \"vampire_false\")")),
            hypothesis(pointwiseName)));
        const std::string existsNegative = proofApply(
          proofApply(
            termApply(
              termApply(known(notForall), formula(positivePredicate)),
              formula(negativePredicate)),
            pointwise),
          notClosedComponent);
        const std::string witnessNegative = proofApply(
          termApply(known(choice), formula(negativePredicate)),
          existsNegative);
        const std::string splitName = freshName("split");
        const auto splitPosition = std::find(
          effectiveResult.begin(), effectiveResult.end(), positiveSplit);
        const auto complementPosition = std::find(
          effectiveResult.begin(), effectiveResult.end(), witnessComplement);
        if (splitPosition == effectiveResult.end()
            || complementPosition == effectiveResult.end()) {
          error = "positive AVATAR component counterexample does not occur in its result";
          return false;
        }
        const std::string trueProof = inject(
          effectiveResult,
          static_cast<std::size_t>(
            splitPosition - effectiveResult.begin()),
          hypothesis(splitName));
        const std::string falseProof = inject(
          effectiveResult,
          static_cast<std::size_t>(
            complementPosition - effectiveResult.begin()),
          witnessNegative);
        if (trueProof.empty() || falseProof.empty()) {
          error = "positive AVATAR component counterexample does not inject into its result";
          return false;
        }
        result = excludedMiddle(
          splitAtom,
          effectiveTargetFormula,
          splitName,
          trueProof,
          notSplitName,
          falseProof);
        scopedChoice->parameter = variable.first;
        scopedChoice->parameterType = type;
        scopedChoice->witnessTerm = witness;
        scopedChoice->resultLiterals = effectiveResult;
        scopedChoice->resultClause = clauseValue(effectiveResult);
        scopedChoice->producerProof = result;
        return !result.empty();
      }
      const std::string componentLiteral = item.componentLiterals.front();
      const std::string atom = componentLiteral.substr(5, componentLiteral.size() - 6);
      const bool componentPositive = componentLiteral.compare(0, 5, "(pos ") == 0;
      const std::string atomName = freshName("atom");
      const std::string notAtomName = freshName("not_atom");
      const std::string splitFromComponent = selectDefinition(false);
      const std::string trueProof = componentPositive
        ? injectLiteral(
            positiveSplit,
            proofApply(splitFromComponent, hypothesis(atomName)))
        : injectLiteral("(pos " + atom + ")", hypothesis(atomName));
      const std::string falseProof = componentPositive
        ? injectLiteral("(neg " + atom + ")", hypothesis(notAtomName))
        : injectLiteral(
            positiveSplit,
            proofApply(splitFromComponent, hypothesis(notAtomName)));
      if (trueProof.empty() || falseProof.empty()) continue;
      result = excludedMiddle(
        atom, targetFormula,
        atomName, trueProof,
        notAtomName, falseProof);
    }
    return true;
  }
  error = "AVATAR component direct proof has no matching producer definition";
  return false;
}

bool expandAvatarDefinitionProof(
  const MegalodonKernelSyntax::RenderedKernelAvatarDefinition& request,
  std::string& resultFormula,
  std::string& result,
  std::string& error)
{
  auto quote = [](const std::string& value) {
    std::string rendered = "\"";
    for (char ch : value) {
      switch (ch) {
        case '\\': rendered += "\\\\"; break;
        case '"': rendered += "\\\""; break;
        case '\n': rendered += "\\n"; break;
        case '\r': rendered += "\\r"; break;
        case '\t': rendered += "\\t"; break;
        default: rendered += ch; break;
      }
    }
    return rendered + '"';
  };
  auto literalFormula = [](const std::string& literal, std::string& formula) {
    if (literal.size() < 7 || literal.back() != ')') {
      return false;
    }
    const bool positive = literal.compare(0, 5, "(pos ") == 0;
    const bool negative = literal.compare(0, 5, "(neg ") == 0;
    if (!positive && !negative) {
      return false;
    }
    const std::string atom = literal.substr(5, literal.size() - 6);
    formula = positive
      ? atom
      : "(IMP " + atom + " (TMH \"vampire_false\"))";
    return true;
  };
  auto formulaOr = [](const std::string& left, const std::string& right) {
    return "(AP (AP (TMH \"vampire_or\") " + left + ") " + right + ")";
  };
  auto formulaImp = [](const std::string& left, const std::string& right) {
    return "(IMP " + left + " " + right + ")";
  };
  auto formula = [](const std::string& value) {
    return "(formula " + value + ")";
  };
  auto hypothesis = [&](const std::string& name) {
    return "(hyp " + quote(name) + ")";
  };
  auto known = [&](const std::string& name) {
    return "(known " + quote(name) + ")";
  };
  auto termApply = [](const std::string& proof, const std::string& term) {
    return "(term_apply " + proof + " " + term + ")";
  };
  auto proofApply = [](const std::string& left, const std::string& right) {
    return "(proof_apply " + left + " " + right + ")";
  };
  auto proofLambda = [&](const std::string& name,
                         const std::string& proposition,
                         const std::string& body) {
    return "(proof_lambda " + quote(name) + " " + proposition
      + " " + body + ")";
  };
  auto termLambda = [&](const std::string& name,
                        const std::string& type,
                        const std::string& body) {
    return "(term_lambda " + quote(name) + " " + type
      + " " + body + ")";
  };

  if (!request.componentSplit.positive) {
    error = "AVATAR definition direct proof requires a positive split definition";
    return false;
  }
  if (request.componentLiterals.empty()) {
    error = "AVATAR definition direct proof has an empty component";
    return false;
  }
  std::vector<std::string> literalFormulas;
  literalFormulas.reserve(request.componentLiterals.size());
  for (const std::string& literal : request.componentLiterals) {
    std::string rendered;
    if (!literalFormula(literal, rendered)) {
      error = "AVATAR definition direct proof has a malformed component literal";
      return false;
    }
    literalFormulas.push_back(std::move(rendered));
  }
  std::string component = literalFormulas.back();
  for (std::size_t offset = literalFormulas.size() - 1; offset > 0; --offset) {
    component = formulaOr(literalFormulas[offset - 1], component);
  }
  for (auto variable = request.componentVariables.rbegin();
       variable != request.componentVariables.rend(); ++variable) {
    component = "(ALLV " + quote(variable->first) + " "
      + variable->second.sexpr + " " + component + ")";
  }

  const std::string split =
    "(TMH " + quote("split_" + std::to_string(request.componentSplit.variable)) + ")";
  const std::string left = formulaImp(split, component);
  const std::string right = formulaImp(component, split);
  resultFormula =
    "(AP (AP (TMH \"vampire_and\") " + left + ") " + right + ")";
  const std::string qName = "ivy_definition_q";
  const std::string introName = "ivy_definition_intro";
  const std::string splitName = "ivy_definition_split";
  const std::string componentName = "ivy_definition_component";
  const std::string notSplitName = "ivy_definition_not_split";
  const std::string q = "(TMH " + quote(qName) + ")";

  std::string splitToComponent = hypothesis(splitName);
  for (const auto& variable : request.componentVariables) {
    splitToComponent = termApply(
      splitToComponent,
      "(term (TMH " + quote(variable.first) + "))");
  }
  for (auto variable = request.componentVariables.rbegin();
       variable != request.componentVariables.rend(); ++variable) {
    splitToComponent = termLambda(
      variable->first, variable->second.sexpr, splitToComponent);
  }
  splitToComponent = proofLambda(
    splitName, formula(split), splitToComponent);

  const std::string dnegHash =
    "e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0";
  const std::string componentToSplit = proofLambda(
    componentName,
    formula(component),
    proofApply(
      termApply(known(dnegHash), formula(split)),
      proofLambda(
        notSplitName,
        formula(formulaImp(split, "(TMH \"vampire_false\")")),
        proofApply(hypothesis(notSplitName), hypothesis(componentName)))));

  result = termLambda(
    qName,
    "(PROP)",
    proofLambda(
      introName,
      formula(formulaImp(left, formulaImp(right, q))),
      proofApply(
        proofApply(hypothesis(introName), splitToComponent),
        componentToSplit)));
  return true;
}

bool expandAvatarSplitProof(
  const std::string& stepId,
  const MegalodonKernelSyntax::RenderedKernelAvatarSplitStep& request,
  std::string& result,
  std::vector<MegalodonKernelSyntax::ProducerProofClaim>& supportClaims,
  std::vector<MegalodonKernelSyntax::ProducerTermDefinition>& termDefinitions,
  std::string& error)
{
  using MegalodonKernelSyntax::RenderedKernelAvatarComponentParent;
  using MegalodonKernelSyntax::RenderedKernelAvatarCounterexampleProgram;
  using MegalodonKernelSyntax::RenderedKernelAvatarLiteralClass;
  using MegalodonKernelSyntax::RenderedKernelAvatarSplitCase;
  using MegalodonKernelSyntax::RenderedKernelAvatarSplitSourceAction;
  using MegalodonKernelSyntax::RenderedKernelAvatarSplitSourceNode;
  using MegalodonKernelSyntax::RenderedKernelTypedVariable;

  auto quote = [](const std::string& value) {
    std::string rendered = "\"";
    for (char ch : value) {
      switch (ch) {
        case '\\': rendered += "\\\\"; break;
        case '"': rendered += "\\\""; break;
        case '\n': rendered += "\\n"; break;
        case '\r': rendered += "\\r"; break;
        case '\t': rendered += "\\t"; break;
        default: rendered += ch; break;
      }
    }
    return rendered + '"';
  };
  auto literalFormula = [](const std::string& literal, std::string& formula) {
    if (literal.size() < 7 || literal.back() != ')') {
      return false;
    }
    const bool positive = literal.compare(0, 5, "(pos ") == 0;
    const bool negative = literal.compare(0, 5, "(neg ") == 0;
    if (!positive && !negative) {
      return false;
    }
    const std::string atom = literal.substr(5, literal.size() - 6);
    formula = positive
      ? atom
      : "(IMP " + atom + " (TMH \"vampire_false\"))";
    return true;
  };
  auto formulaOr = [](const std::string& left, const std::string& right) {
    return "(AP (AP (TMH \"vampire_or\") " + left + ") " + right + ")";
  };
  auto formulaImp = [](const std::string& left, const std::string& right) {
    return "(IMP " + left + " " + right + ")";
  };
  auto formula = [](const std::string& value) {
    return "(formula " + value + ")";
  };
  auto literalTerm = [](const std::string& value) {
    return "(literal " + value + ")";
  };
  auto clauseData = [](const std::vector<std::string>& literals) {
    std::string value = "(clause";
    for (const std::string& literal : literals) {
      value += " " + literal;
    }
    return value + ")";
  };
  auto clauseTerm = [&](const std::vector<std::string>& literals) {
    return "(clause " + clauseData(literals) + ")";
  };
  auto hypothesis = [&](const std::string& name) {
    return "(hyp " + quote(name) + ")";
  };
  auto parent = [&](const std::string& name) {
    return "(parent " + quote(name) + ")";
  };
  auto definition = [&](const std::string& name) {
    return "(definition " + quote(name) + ")";
  };
  auto known = [&](const std::string& name) {
    return "(known " + quote(name) + ")";
  };
  auto termApply = [](const std::string& proof, const std::string& term) {
    return "(term_apply " + proof + " " + term + ")";
  };
  auto proofApply = [](const std::string& left, const std::string& right) {
    return "(proof_apply " + left + " " + right + ")";
  };
  auto proofLambda = [&](const std::string& name,
                         const std::string& proposition,
                         const std::string& body) {
    return "(proof_lambda " + quote(name) + " " + proposition
      + " " + body + ")";
  };
  auto termLambda = [&](const std::string& name,
                        const std::string& type,
                        const std::string& body) {
    return "(term_lambda " + quote(name) + " " + type
      + " " + body + ")";
  };
  // Later counterexample stages apply earlier epsilon witnesses.  Keep every
  // stage beta-normal so adjacent Ivy proof applications use one proposition.
  PreservedSexprParser parser;
  auto betaNormalized = [&](const std::string& source,
                            std::string& normalized) {
    PreservedSexpr parsed;
    if (!parser.parse(source, parsed)) return false;
    normalized = betaNormalizeSexpr(parsed).render();
    return true;
  };
  auto substitutedTerm = [&](const std::vector<std::pair<std::string, std::string>>& bindings,
                             const std::string& body) {
    if (bindings.empty()) {
      return body;
    }
    std::string value = "(substitute (subst";
    for (const auto& [name, replacement] : bindings) {
      value += " (" + quote(name) + " " + replacement + ")";
    }
    return value + ") " + body + ")";
  };
  auto clauseFormula = [&](const std::vector<std::string>& literals,
                           std::string& value) {
    if (literals.empty()) {
      value = "(TMH \"vampire_false\")";
      return true;
    }
    std::vector<std::string> formulas(literals.size());
    for (std::size_t index = 0; index < literals.size(); ++index) {
      if (!literalFormula(literals[index], formulas[index])) {
        return false;
      }
    }
    value = formulas.back();
    for (std::size_t index = formulas.size() - 1; index > 0; --index) {
      value = formulaOr(formulas[index - 1], value);
    }
    return true;
  };
  auto quantifiedClauseFormula = [&](const RenderedKernelAvatarComponentParent& component,
                                     std::string& value) {
    if (!clauseFormula(component.literals, value)) {
      return false;
    }
    for (std::size_t index = component.variables.size(); index > 0; --index) {
      const RenderedKernelTypedVariable& variable = component.variables[index - 1];
      value = "(ALLV " + quote(variable.variable) + " "
        + variable.type.sexpr + " " + value + ")";
    }
    return true;
  };

  supportClaims.clear();
  termDefinitions.clear();
  if (stepId.empty() || !request.hasIvyProgram
      || request.sourceUnit.value.empty()
      || request.sourceLiterals.empty() || !request.hasResultFormula
      || request.cases.empty()) {
    error = "AVATAR split direct proof lacks producer source/target data";
    return false;
  }
  if (std::getenv("MEGALODON_CERT_DEBUG") != nullptr) {
    std::cerr << "megalodon direct AVATAR input " << stepId
              << ": source=" << request.sourceUnit.value
              << " source_vars=" << request.sourceVariables.size()
              << " components=" << request.componentParents.size()
              << " bindings=" << request.parentVarBindings.size()
              << " cases=" << request.cases.size()
              << " focus=" << (request.hasFocus
                    ? std::to_string(request.focusSplitVar)
                    : std::string("none")) << std::endl;
    for (const auto& variable : request.sourceVariables) {
      std::cerr << "  source-var " << variable.variable << ':'
                << variable.type.sexpr << std::endl;
    }
    for (const auto& component : request.componentParents) {
      std::cerr << "  component split_" << component.split.variable
                << " parent=" << component.unit.value << " vars=";
      for (const auto& variable : component.variables) {
        std::cerr << ' ' << variable.variable << ':' << variable.type.sexpr;
      }
      std::cerr << std::endl;
    }
    for (const auto& binding : request.parentVarBindings) {
      std::cerr << "  binding " << binding.parentVar << " -> "
                << (binding.hasComponentVar ? binding.componentVar : "<none>")
                << " split_" << binding.splitVar
                << " witness=" << (binding.hasCounterexampleProgram
                      ? std::to_string(binding.counterexampleProgram) + "/"
                        + std::to_string(binding.counterexampleStage)
                      : std::string("focus")) << std::endl;
    }
  }

  std::size_t fresh = 0;
  auto freshName = [&](const char* prefix) {
    return std::string("ivy_") + prefix + std::to_string(fresh++);
  };
  auto orIntroduction = [&](const std::string& left,
                            const std::string& right,
                            const std::string& proof,
                            bool injectLeft) {
    const std::string q = freshName("q");
    const std::string leftHyp = freshName("left");
    const std::string rightHyp = freshName("right");
    const std::string qTerm = "(TMH " + quote(q) + ")";
    return termLambda(
      q, "(PROP)",
      proofLambda(
        leftHyp, formula(formulaImp(left, qTerm)),
        proofLambda(
          rightHyp, formula(formulaImp(right, qTerm)),
          proofApply(hypothesis(injectLeft ? leftHyp : rightHyp), proof))));
  };
  auto injectClause = [&](const std::vector<std::string>& literals,
                          std::size_t literalIndex,
                          const std::vector<std::pair<std::string, std::string>>& bindings,
                          const std::string& proof) {
    std::function<std::string(std::size_t, std::size_t, const std::string&)> inject;
    inject = [&](std::size_t begin,
                 std::size_t target,
                 const std::string& inner) -> std::string {
      if (begin >= literals.size() || target >= literals.size()) {
        return std::string();
      }
      if (begin + 1 == literals.size()) {
        return begin == target ? inner : std::string();
      }
      std::string left;
      std::string right;
      if (!literalFormula(literals[begin], left)) {
        return std::string();
      }
      const std::vector<std::string> rest(
        literals.begin() + begin + 1, literals.end());
      if (!clauseFormula(rest, right)) {
        return std::string();
      }
      const std::string substitutedLeft =
        substitutedTerm(bindings, formula(left));
      const std::string substitutedRight =
        substitutedTerm(bindings, formula(right));
      if (begin == target) {
        const std::string q = freshName("q");
        const std::string leftHyp = freshName("left");
        const std::string rightHyp = freshName("right");
        const std::string qTerm = "(TMH " + quote(q) + ")";
        return termLambda(
          q, "(PROP)",
          proofLambda(
            leftHyp,
            substitutedTerm(bindings, formula(formulaImp(left, qTerm))),
            proofLambda(
              rightHyp,
              substitutedTerm(bindings, formula(formulaImp(right, qTerm))),
              proofApply(hypothesis(leftHyp), inner))));
      }
      const std::string nested = inject(begin + 1, target, inner);
      if (nested.empty()) {
        return std::string();
      }
      const std::string q = freshName("q");
      const std::string leftHyp = freshName("left");
      const std::string rightHyp = freshName("right");
      const std::string qTerm = "(TMH " + quote(q) + ")";
      return termLambda(
        q, "(PROP)",
        proofLambda(
          leftHyp,
          substitutedTerm(bindings, formula(formulaImp(left, qTerm))),
          proofLambda(
            rightHyp,
            substitutedTerm(bindings, formula(formulaImp(right, qTerm))),
            proofApply(hypothesis(rightHyp), nested))));
    };
    return inject(0, literalIndex, proof);
  };

  std::function<bool(const std::string&, std::string&)> targetAt;
  targetAt = [&](const std::string& path, std::string& target) {
    const auto leaf = std::find_if(
      request.cases.begin(), request.cases.end(),
      [&](const RenderedKernelAvatarSplitCase& item) {
        return item.path == path;
      });
    if (leaf != request.cases.end()) {
      target = leaf->formula.sexpr;
      return true;
    }
    const bool hasDescendant = std::any_of(
      request.cases.begin(), request.cases.end(),
      [&](const RenderedKernelAvatarSplitCase& item) {
        return item.path.size() > path.size()
          && item.path.compare(0, path.size(), path) == 0;
      });
    if (!hasDescendant) {
      return false;
    }
    std::string left;
    std::string right;
    if (!targetAt(path + "L", left) || !targetAt(path + "R", right)) {
      return false;
    }
    target = formulaOr(left, right);
    return true;
  };
  std::string targetFormula;
  if (!targetAt("", targetFormula)
      || targetFormula != request.resultFormula.sexpr) {
    error = "AVATAR split direct proof target paths do not rebuild its result";
    return false;
  }
  auto injectTarget = [&](const RenderedKernelAvatarSplitCase& item,
                          const std::string& proof) {
    std::function<std::string(const std::string&, const std::string&)> inject;
    inject = [&](const std::string& prefix,
                 const std::string& inner) -> std::string {
      if (prefix == item.path) {
        return inner;
      }
      std::string left;
      std::string right;
      if (!targetAt(prefix + "L", left) || !targetAt(prefix + "R", right)
          || prefix.size() >= item.path.size()) {
        return std::string();
      }
      if (item.path[prefix.size()] == 'L') {
        return orIntroduction(left, right, inject(prefix + "L", inner), true);
      }
      if (item.path[prefix.size()] == 'R') {
        return orIntroduction(left, right, inject(prefix + "R", inner), false);
      }
      return std::string();
    };
    return inject("", proof);
  };

  auto xmProof = [&](const std::string& proposition) {
    const std::string q = freshName("xm_q");
    const std::string left = freshName("xm_left");
    const std::string right = freshName("xm_right");
    const std::string notQ = freshName("xm_not_q");
    const std::string prop = freshName("xm_prop");
    const std::string qTerm = "(TMH " + quote(q) + ")";
    const std::string notProp = formulaImp(
      proposition, "(TMH \"vampire_false\")");
    const std::string qFromNotProp = proofApply(
      hypothesis(right),
      proofLambda(
        prop, formula(proposition),
        proofApply(
          hypothesis(notQ),
          proofApply(hypothesis(left), hypothesis(prop)))));
    return termLambda(
      q, "(PROP)",
      proofLambda(
        left, formula(formulaImp(proposition, qTerm)),
        proofLambda(
          right, formula(formulaImp(notProp, qTerm)),
          proofApply(
            termApply(
              known("e4b03c310442ae760be9945e176494db51515dfb952ee60fbd42e05527752af0"),
              formula(qTerm)),
            proofLambda(
              notQ,
              formula(formulaImp(qTerm, "(TMH \"vampire_false\")")),
              proofApply(hypothesis(notQ), qFromNotProp))))));
  };

  auto componentByIndex = [&](std::size_t index)
      -> const RenderedKernelAvatarComponentParent* {
    const auto found = std::find_if(
      request.componentParents.begin(), request.componentParents.end(),
      [&](const RenderedKernelAvatarComponentParent& component) {
        return component.refIndex == index;
      });
    return found == request.componentParents.end() ? nullptr : &*found;
  };
  auto componentBySplit = [&](unsigned split)
      -> const RenderedKernelAvatarComponentParent* {
    const auto found = std::find_if(
      request.componentParents.begin(), request.componentParents.end(),
      [&](const RenderedKernelAvatarComponentParent& component) {
        return component.split.variable == split;
      });
    return found == request.componentParents.end() ? nullptr : &*found;
  };
  auto classByIndex = [&](std::size_t index)
      -> const RenderedKernelAvatarLiteralClass* {
    const auto found = std::find_if(
      request.literalClasses.begin(), request.literalClasses.end(),
      [&](const RenderedKernelAvatarLiteralClass& item) {
        return item.index == index;
      });
    return found == request.literalClasses.end() ? nullptr : &*found;
  };
  auto counterexampleBySplit = [&](unsigned split)
      -> const RenderedKernelAvatarCounterexampleProgram* {
    const auto found = std::find_if(
      request.counterexamplePrograms.begin(), request.counterexamplePrograms.end(),
      [&](const RenderedKernelAvatarCounterexampleProgram& item) {
        return item.splitVar == split;
      });
    return found == request.counterexamplePrograms.end() ? nullptr : &*found;
  };
  auto counterexampleByIndex = [&](std::size_t index)
      -> const RenderedKernelAvatarCounterexampleProgram* {
    const auto found = std::find_if(
      request.counterexamplePrograms.begin(), request.counterexamplePrograms.end(),
      [&](const RenderedKernelAvatarCounterexampleProgram& item) {
        return item.index == index;
      });
    return found == request.counterexamplePrograms.end() ? nullptr : &*found;
  };
  std::map<std::pair<std::size_t, std::size_t>, std::string> witnessSymbols;
  for (const auto& counterexample : request.counterexamplePrograms) {
    for (const auto& stage : counterexample.stages) {
      std::string directWitness;
      if (stage.directWitnessSymbol.empty()
          || stage.type.sexpr.empty() || stage.directWitness.sexpr.empty()
          || !betaNormalized(stage.directWitness.sexpr, directWitness)
          || !witnessSymbols.emplace(
                std::make_pair(counterexample.index, stage.index),
                stage.directWitnessSymbol).second) {
        error = "AVATAR split has an incomplete producer witness definition";
        return false;
      }
      MegalodonKernelSyntax::ProducerTermDefinition definition;
      definition.stepId = stepId + "_avatar_witness_definition_"
        + std::to_string(counterexample.splitVar) + "_"
        + std::to_string(stage.index);
      definition.symbol = stage.directWitnessSymbol;
      definition.resultType = stage.type.sexpr;
      definition.body = std::move(directWitness);
      termDefinitions.push_back(std::move(definition));
    }
  }
  auto witnessSymbol = [&](const RenderedKernelAvatarCounterexampleProgram& program,
                           std::size_t stage) -> const std::string* {
    const auto found = witnessSymbols.find({program.index, stage});
    return found == witnessSymbols.end() ? nullptr : &found->second;
  };
  auto sourceNode = [&](std::size_t index)
      -> const RenderedKernelAvatarSplitSourceNode* {
    const auto found = std::find_if(
      request.sourceNodes.begin(), request.sourceNodes.end(),
      [&](const RenderedKernelAvatarSplitSourceNode& item) {
        return item.literal == index;
      });
    return found == request.sourceNodes.end() ? nullptr : &*found;
  };
  auto typeKnown = [](const std::string& type, bool choice) {
    if (type == "(SET)") {
      return choice ? std::string("vampire_exists_set_choice")
                    : std::string("vampire_not_forall_exists_set");
    }
    if (type == "(PROP)") {
      return choice ? std::string("vampire_exists_prop_choice")
                    : std::string("vampire_not_forall_exists_prop");
    }
    if (type == "(AR (SET) (PROP))") {
      return choice ? std::string("vampire_exists_set_prop_choice")
                    : std::string("vampire_not_forall_exists_set_prop");
    }
    if (type == "(AR (SET) (SET))") {
      return choice ? std::string("vampire_exists_set_set_choice")
                    : std::string("vampire_not_forall_exists_set_set");
    }
    if (type == "(AR (SET) (AR (SET) (PROP)))") {
      return choice ? std::string("vampire_exists_set_set_prop_choice")
                    : std::string("vampire_not_forall_exists_set_set_prop");
    }
    return std::string();
  };

  const RenderedKernelAvatarComponentParent* focusComponent = request.hasFocus
    ? componentByIndex(request.focusComponentParent)
    : nullptr;
  if (request.hasFocus && focusComponent == nullptr) {
    error = "AVATAR split direct proof has no declared focus component";
    return false;
  }
  const std::vector<RenderedKernelTypedVariable> focusVariables =
    focusComponent == nullptr
      ? std::vector<RenderedKernelTypedVariable>()
      : focusComponent->variables;
  auto isFocusVariable = [&](const RenderedKernelTypedVariable& variable) {
    return std::any_of(
      focusVariables.begin(), focusVariables.end(),
      [&](const RenderedKernelTypedVariable& focus) {
        return focus.variable == variable.variable
          && focus.type.sexpr == variable.type.sexpr;
      });
  };
  auto componentArguments = [&](const RenderedKernelAvatarComponentParent& component,
                                std::vector<std::string>& arguments) {
    const RenderedKernelAvatarCounterexampleProgram* counterexample =
      counterexampleBySplit(component.split.variable);
    for (const RenderedKernelTypedVariable& variable : component.variables) {
      if (isFocusVariable(variable)) {
        arguments.push_back("(TMH " + quote(variable.variable) + ")");
        continue;
      }
      if (counterexample == nullptr) {
        return false;
      }
      const auto stage = std::find_if(
        counterexample->stages.begin(), counterexample->stages.end(),
        [&](const auto& item) {
          return item.variable == variable.variable
            && item.type.sexpr == variable.type.sexpr;
        });
      if (stage == counterexample->stages.end()
          || stage->directWitness.sexpr.empty()) {
        return false;
      }
      const std::string* witness = witnessSymbol(
        *counterexample, stage->index);
      if (witness == nullptr) {
        return false;
      }
      arguments.push_back("(TMH " + quote(*witness) + ")");
    }
    return true;
  };
  auto componentBindings = [&](const RenderedKernelAvatarComponentParent& component,
                               const std::vector<std::string>& arguments) {
    std::vector<std::pair<std::string, std::string>> bindings;
    for (std::size_t index = 0; index < component.variables.size(); ++index) {
      bindings.push_back({component.variables[index].variable, arguments[index]});
    }
    return bindings;
  };

  struct Relation {
    std::string splitToComponent;
    std::string componentToSplit;
    std::string componentFormula;
  };
  auto relation = [&](const RenderedKernelAvatarComponentParent& component,
                      Relation& relationResult) {
    if (!quantifiedClauseFormula(component, relationResult.componentFormula)) {
      return false;
    }
    const std::string splitFormula =
      "(TMH " + quote("split_" + std::to_string(component.split.variable)) + ")";
    const std::string left = formulaImp(splitFormula, relationResult.componentFormula);
    const std::string right = formulaImp(relationResult.componentFormula, splitFormula);
    const std::string leftName = freshName("definition_left");
    const std::string rightName = freshName("definition_right");
    const std::string theorem = definition(component.unit.value);
    relationResult.splitToComponent = proofApply(
      termApply(theorem, formula(left)),
      proofLambda(
        leftName, formula(left),
        proofLambda(rightName, formula(right), hypothesis(leftName))));
    const std::string leftName2 = freshName("definition_left");
    const std::string rightName2 = freshName("definition_right");
    relationResult.componentToSplit = proofApply(
      termApply(theorem, formula(right)),
      proofLambda(
        leftName2, formula(left),
        proofLambda(rightName2, formula(right), hypothesis(rightName2))));
    return true;
  };

  auto negativeComponent = [&](const RenderedKernelAvatarComponentParent& component,
                               const Relation& componentRelation,
                               const std::string& notSplit,
                               std::string& proof) {
    const std::string componentHyp = freshName("closed_component");
    proof = proofLambda(
      componentHyp,
      formula(componentRelation.componentFormula),
      proofApply(
        notSplit,
        proofApply(componentRelation.componentToSplit, hypothesis(componentHyp))));
    const RenderedKernelAvatarCounterexampleProgram* counterexample =
      counterexampleBySplit(component.split.variable);
    if (component.variables.empty()) {
      return true;
    }
    if (counterexample == nullptr
        || counterexample->stages.size() != component.variables.size()) {
      return false;
    }
    for (std::size_t index = 0; index < component.variables.size(); ++index) {
      const RenderedKernelTypedVariable& variable = component.variables[index];
      const auto& stage = counterexample->stages[index];
      if (stage.variable != variable.variable
          || stage.type.sexpr != variable.type.sexpr
          || stage.openBody.sexpr.empty()
          || stage.positivePredicate.sexpr.empty()
          || stage.negativePredicate.sexpr.empty()) {
        return false;
      }
      const std::string notForall = typeKnown(variable.type.sexpr, false);
      const std::string choice = typeKnown(variable.type.sexpr, true);
      if (notForall.empty() || choice.empty()) {
        return false;
      }
      std::string openBody;
      std::string positivePredicate;
      std::string negativePredicate;
      if (!betaNormalized(stage.openBody.sexpr, openBody)
          || !betaNormalized(
               stage.positivePredicate.sexpr, positivePredicate)
          || !betaNormalized(
               stage.negativePredicate.sexpr, negativePredicate)) {
        return false;
      }
      const std::string pointwiseHyp = freshName("pointwise");
      const std::string pointwise = termLambda(
        variable.variable,
        variable.type.sexpr,
        proofLambda(
          pointwiseHyp,
          formula(formulaImp(
            openBody, "(TMH \"vampire_false\")")),
          hypothesis(pointwiseHyp)));
      const std::string existsNegative = proofApply(
        proofApply(
          termApply(
            termApply(
              known(notForall), formula(positivePredicate)),
            formula(negativePredicate)),
          pointwise),
        proof);
      proof = proofApply(
        termApply(known(choice), formula(negativePredicate)),
        existsNegative);
    }
    return true;
  };

  std::map<unsigned, std::string> negativeComponentSupports;
  auto negativeComponentTheorem = [&]
    (const RenderedKernelAvatarComponentParent& component,
     const Relation& componentRelation,
     std::string& theorem) {
    auto existing = negativeComponentSupports.find(component.split.variable);
    if (existing != negativeComponentSupports.end()) {
      theorem = parent(existing->second);
      return true;
    }
    const std::string splitFormula =
      "(TMH " + quote("split_" + std::to_string(component.split.variable))
      + ")";
    const std::string notSplitFormula =
      formulaImp(splitFormula, "(TMH \"vampire_false\")");
    const std::string notSplitHypothesis = freshName("not_split_support");
    std::string notComponentProof;
    if (!negativeComponent(
          component,
          componentRelation,
          hypothesis(notSplitHypothesis),
          notComponentProof)) {
      return false;
    }
    const std::string directTheorem = proofLambda(
      notSplitHypothesis,
      formula(notSplitFormula),
      notComponentProof);
    // Closed components have no repeated counterexample-witness expansion.
    // Keep their small theorem inline; sharing is reserved for quantified
    // components where it prevents exponential witness duplication.
    if (component.variables.empty()) {
      theorem = directTheorem;
      return true;
    }
    MegalodonKernelSyntax::ProducerProofClaim claim;
    claim.id = stepId + "_avatar_counterexample_"
      + std::to_string(component.split.variable);
    claim.replacesParent = claim.id + "_use";
    const RenderedKernelAvatarCounterexampleProgram* counterexample =
      counterexampleBySplit(component.split.variable);
    std::string finalBody;
    if (counterexample == nullptr || counterexample->finalBody.sexpr.empty()
        || !betaNormalized(counterexample->finalBody.sexpr, finalBody)) {
      return false;
    }
    claim.resultFormula = formulaImp(
      notSplitFormula,
      formulaImp(
        finalBody,
        "(TMH \"vampire_false\")"));
    claim.producerProof = directTheorem;
    theorem = parent(claim.replacesParent);
    negativeComponentSupports.emplace(
      component.split.variable, claim.replacesParent);
    supportClaims.push_back(std::move(claim));
    return true;
  };

  std::vector<std::pair<std::string, std::string>> sourceBindings;
  std::vector<std::string> sourceArguments;
  for (const RenderedKernelTypedVariable& variable : request.sourceVariables) {
    const auto binding = std::find_if(
      request.parentVarBindings.begin(), request.parentVarBindings.end(),
      [&](const auto& item) {
        return item.parentVar == variable.variable
          && item.hasType && item.type.sexpr == variable.type.sexpr;
      });
    if (binding == request.parentVarBindings.end()
        || !binding->hasComponentVar) {
      error = "AVATAR split direct proof lacks an exact source-variable binding";
      return false;
    }
    std::string argument;
    const RenderedKernelTypedVariable candidate{
      binding->componentVar, variable.type};
    if (isFocusVariable(candidate)) {
      argument = "(TMH " + quote(binding->componentVar) + ")";
    } else if (binding->hasCounterexampleProgram) {
      const RenderedKernelAvatarCounterexampleProgram* counterexample =
        counterexampleByIndex(binding->counterexampleProgram);
      if (counterexample == nullptr
          || binding->counterexampleStage >= counterexample->stages.size()) {
        error = "AVATAR split direct proof source witness index is unavailable";
        return false;
      }
      const std::string* witness = witnessSymbol(
        *counterexample, binding->counterexampleStage);
      if (witness == nullptr) {
        error = "AVATAR split direct proof source witness is malformed";
        return false;
      }
      argument = "(TMH " + quote(*witness) + ")";
    }
    if (argument.empty()) {
      error = "AVATAR split direct proof source binding has no producer witness";
      return false;
    }
    sourceArguments.push_back(argument);
    sourceBindings.push_back({variable.variable, argument});
  }

  std::string sourceProof = parent(request.sourceUnit.value);
  for (const std::string& argument : sourceArguments) {
    sourceProof = termApply(sourceProof, formula(argument));
  }

  struct Assignment {
    bool positive = false;
    std::string proof;
  };
  struct LiteralResult {
    bool contradiction = false;
    std::string proof;
  };
  using Assignments = std::map<unsigned, Assignment>;

  std::function<std::string(std::size_t, const Assignments&)> proveCases;
  auto proveTerminal = [&](const Assignments& assignments, std::string& terminal) {
    std::vector<std::string> terminalLiterals;
    std::vector<std::pair<std::string, std::string>> terminalBindings;
    std::string terminalTerm = formula(targetFormula);
    if (focusComponent != nullptr) {
      std::vector<std::string> arguments;
      if (!componentArguments(*focusComponent, arguments)) {
        return false;
      }
      terminalLiterals = focusComponent->literals;
      terminalBindings = componentBindings(*focusComponent, arguments);
      terminalTerm = substitutedTerm(
        terminalBindings, clauseTerm(terminalLiterals));
    }
    auto falseElim = [&](const std::string& contradiction) {
      return termApply(contradiction, terminalTerm);
    };
    auto assignment = [&](unsigned split) -> const Assignment* {
      const auto found = assignments.find(split);
      return found == assignments.end() ? nullptr : &found->second;
    };
    auto proveLiteral = [&](std::size_t literalIndex,
                            const std::string& literalProof,
                            LiteralResult& literalResult) {
      const RenderedKernelAvatarSplitSourceNode* node = sourceNode(literalIndex);
      if (node == nullptr || literalIndex >= request.sourceLiterals.size()) {
        return false;
      }
      if (node->action == RenderedKernelAvatarSplitSourceAction::Focus) {
        if (focusComponent == nullptr) {
          return false;
        }
        literalResult.proof = injectClause(
          terminalLiterals, node->componentLiteral, terminalBindings, literalProof);
        return !literalResult.proof.empty();
      }
      if (node->action == RenderedKernelAvatarSplitSourceAction::PreviousSplit) {
        if (node->caseIndex >= request.cases.size()) {
          return false;
        }
        const RenderedKernelAvatarSplitCase& item = request.cases[node->caseIndex];
        const Assignment* assigned = assignment(item.splitVar);
        if (assigned == nullptr) {
          return false;
        }
        if (item.positive && !assigned->positive) {
          literalResult.contradiction = true;
          literalResult.proof = proofApply(assigned->proof, literalProof);
          return true;
        }
        if (!item.positive && assigned->positive) {
          literalResult.contradiction = true;
          literalResult.proof = proofApply(literalProof, assigned->proof);
          return true;
        }
        return false;
      }

      const RenderedKernelAvatarLiteralClass* literalClass =
        classByIndex(node->literalClass);
      const RenderedKernelAvatarComponentParent* component =
        componentBySplit(node->splitVar);
      const Assignment* assigned = assignment(node->splitVar);
      if (literalClass == nullptr || component == nullptr || assigned == nullptr) {
        return false;
      }
      std::vector<std::string> arguments;
      if (!componentArguments(*component, arguments)) {
        return false;
      }
      const auto bindings = componentBindings(*component, arguments);
      Relation componentRelation;
      if (!relation(*component, componentRelation)) {
        return false;
      }
      if (literalClass->positive && !assigned->positive) {
        std::string clauseProof = injectClause(
          component->literals, node->componentLiteral, bindings, literalProof);
        std::string notComponentTheorem;
        if (clauseProof.empty()
            || !negativeComponentTheorem(
                 *component, componentRelation, notComponentTheorem)) {
          return false;
        }
        const std::string notComponent = proofApply(
          notComponentTheorem, assigned->proof);
        literalResult.contradiction = true;
        literalResult.proof = proofApply(notComponent, clauseProof);
        return true;
      }
      if (!literalClass->positive && assigned->positive) {
        if (node->componentLiteral >= component->literals.size()) {
          return false;
        }
        std::string componentProof = proofApply(
          componentRelation.splitToComponent, assigned->proof);
        for (const std::string& argument : arguments) {
          componentProof = termApply(componentProof, formula(argument));
        }
        const std::string& componentLiteral =
          component->literals[node->componentLiteral];
        const bool componentPositive =
          componentLiteral.compare(0, 5, "(pos ") == 0;
        const bool componentNegative =
          componentLiteral.compare(0, 5, "(neg ") == 0;
        if (!componentPositive && !componentNegative) {
          return false;
        }
        literalResult.contradiction = true;
        literalResult.proof = componentPositive
          ? proofApply(literalProof, componentProof)
          : proofApply(componentProof, literalProof);
        return true;
      }
      return false;
    };

    std::function<std::string(std::size_t, const std::string&)> project;
    project = [&](std::size_t literalIndex,
                  const std::string& proof) -> std::string {
      if (literalIndex >= request.sourceLiterals.size()) {
        return std::string();
      }
      if (literalIndex + 1 == request.sourceLiterals.size()) {
        LiteralResult literalResult;
        if (!proveLiteral(literalIndex, proof, literalResult)) {
          return std::string();
        }
        return literalResult.contradiction
          ? falseElim(literalResult.proof)
          : literalResult.proof;
      }
      const std::string leftName = freshName("source");
      const std::string restName = freshName("rest");
      LiteralResult leftResult;
      if (!proveLiteral(literalIndex, hypothesis(leftName), leftResult)) {
        return std::string();
      }
      const std::vector<std::string> rest(
        request.sourceLiterals.begin() + literalIndex + 1,
        request.sourceLiterals.end());
      const std::string rightBody = project(literalIndex + 1, hypothesis(restName));
      if (rightBody.empty()) {
        return std::string();
      }
      const std::string leftBody = leftResult.contradiction
        ? falseElim(leftResult.proof)
        : leftResult.proof;
      return proofApply(
        proofApply(
          termApply(proof, terminalTerm),
          proofLambda(
            leftName,
            substitutedTerm(
              sourceBindings, literalTerm(request.sourceLiterals[literalIndex])),
            leftBody)),
        proofLambda(
          restName,
          substitutedTerm(sourceBindings, clauseTerm(rest)),
          rightBody));
    };

    terminal = project(0, sourceProof);
    if (terminal.empty()) {
      return false;
    }
    if (focusComponent == nullptr) {
      return true;
    }
    for (std::size_t index = focusVariables.size(); index > 0; --index) {
      const RenderedKernelTypedVariable& variable = focusVariables[index - 1];
      terminal = termLambda(variable.variable, variable.type.sexpr, terminal);
    }
    Relation focusRelation;
    if (!relation(*focusComponent, focusRelation)) {
      return false;
    }
    const Assignment* focusAssignment = assignment(request.focusSplitVar);
    if (focusAssignment == nullptr || focusAssignment->positive) {
      return false;
    }
    const std::string splitProof = proofApply(
      focusRelation.componentToSplit, terminal);
    terminal = termApply(
      proofApply(focusAssignment->proof, splitProof),
      formula(targetFormula));
    return true;
  };

  proveCases = [&](std::size_t caseIndex,
                   const Assignments& assignments) -> std::string {
    if (caseIndex == request.cases.size()) {
      std::string terminal;
      return proveTerminal(assignments, terminal) ? terminal : std::string();
    }
    const RenderedKernelAvatarSplitCase& item = request.cases[caseIndex];
    const std::string splitFormula =
      "(TMH " + quote("split_" + std::to_string(item.splitVar)) + ")";
    const std::string trueName = freshName("case_true");
    const std::string falseName = freshName("case_false");
    Assignments trueAssignments = assignments;
    trueAssignments[item.splitVar] = {true, hypothesis(trueName)};
    Assignments falseAssignments = assignments;
    falseAssignments[item.splitVar] = {false, hypothesis(falseName)};
    const std::string trueBody = item.positive
      ? injectTarget(item, hypothesis(trueName))
      : proveCases(caseIndex + 1, trueAssignments);
    const std::string falseBody = item.positive
      ? proveCases(caseIndex + 1, falseAssignments)
      : injectTarget(item, hypothesis(falseName));
    if (trueBody.empty() || falseBody.empty()) {
      return std::string();
    }
    return proofApply(
      proofApply(
        termApply(xmProof(splitFormula), formula(targetFormula)),
        proofLambda(trueName, formula(splitFormula), trueBody)),
      proofLambda(
        falseName,
        formula(formulaImp(splitFormula, "(TMH \"vampire_false\")")),
        falseBody));
  };

  const std::string targetProof = proveCases(0, Assignments());
  if (targetProof.empty()) {
    error = "AVATAR split producer could not expand its explicit case program";
    return false;
  }
  std::vector<std::string> normalizedTarget;
  normalizedTarget.reserve(request.cases.size());
  for (const RenderedKernelAvatarSplitCase& item : request.cases) {
    const std::string atom =
      "(TMH " + quote("split_" + std::to_string(item.splitVar)) + ")";
    normalizedTarget.push_back(
      std::string(item.positive ? "(pos " : "(neg ") + atom + ")");
  }
  const std::string normalizedTargetTerm = clauseTerm(normalizedTarget);
  std::function<std::string(const std::string&, const std::string&)> normalizeTarget;
  normalizeTarget = [&](const std::string& path,
                        const std::string& proof) -> std::string {
    const auto leaf = std::find_if(
      request.cases.begin(), request.cases.end(),
      [&](const RenderedKernelAvatarSplitCase& item) {
        return item.path == path;
      });
    if (leaf != request.cases.end()) {
      return injectClause(
        normalizedTarget,
        static_cast<std::size_t>(leaf - request.cases.begin()),
        {},
        proof);
    }
    std::string left;
    std::string right;
    if (!targetAt(path + "L", left) || !targetAt(path + "R", right)) {
      return std::string();
    }
    const std::string leftName = freshName("normalize_left");
    const std::string rightName = freshName("normalize_right");
    const std::string leftBody =
      normalizeTarget(path + "L", hypothesis(leftName));
    const std::string rightBody =
      normalizeTarget(path + "R", hypothesis(rightName));
    if (leftBody.empty() || rightBody.empty()) return std::string();
    return proofApply(
      proofApply(
        termApply(proof, normalizedTargetTerm),
        proofLambda(leftName, formula(left), leftBody)),
      proofLambda(rightName, formula(right), rightBody));
  };
  result = normalizeTarget("", targetProof);
  if (result.empty()) {
    error = "AVATAR split producer could not normalize its target to a split clause";
    return false;
  }
  return true;
}

}
}
