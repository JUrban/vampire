#include "Shell/MegalodonChecker/MegalodonProofExpander.hpp"

#include "Kernel/SortHelper.hpp"
#include "Kernel/SubstHelper.hpp"
#include "Kernel/Substitution.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"
#include "Lib/DHMap.hpp"

#include <algorithm>
#include <cctype>
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
        error = "goal replay references missing parent " + id;
        return false;
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

  std::vector<const GoalReplayStep*> conjectures;
  std::vector<const GoalReplayStep*> negatedConjectures;
  for (const auto& step : steps) {
    if (reachable.find(step.id) == reachable.end()) {
      continue;
    }
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
  if (std::none_of(
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

  std::string render() const
  {
    if (atom) return token;
    std::string result = "(";
    for (std::size_t index = 0; index < items.size(); ++index) {
      if (index != 0) result += ' ';
      result += items[index].render();
    }
    return result + ')';
  }

  bool operator==(const PreservedSexpr& other) const
  {
    return atom == other.atom && token == other.token && items == other.items;
  }
};

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

PreservedSexpr substituteNamedVariableSexpr(
  const PreservedSexpr& source,
  const std::string& variable,
  const PreservedSexpr& replacement)
{
  if (namedTermSexpr(source, variable)) return replacement;
  PreservedSexpr result = source;
  if (result.atom) return result;
  if ((sexprHead(result, "ALLV")
       || sexprHead(result, "LAMV")
       || sexprHead(result, "VLAMV"))
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

  bool cnfFormulaClause(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const std::string& sourceFormula,
    const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
    const std::vector<std::string>& target,
    std::string& result)
  {
    PreservedSexprParser parser;
    PreservedSexpr source;
    if (parentId.empty() || !parser.parse(sourceFormula, source)) {
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
          return expected == declared
              && target[node.resultLiteralIndex] == declared.render()
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
      instantiate(parent(parentId), parentArguments));
    return !result.empty();
  }

  bool foolFormula(
    const std::string& parentId,
    const std::vector<std::string>& parentArguments,
    const MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
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
          return source == target && node.binders.empty()
              && node.children.empty()
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
            if (!parser.parse(renderedType.sexpr, type)
                || !sexprHead(sourceBody, "ALLV")
                || !sexprHead(targetBody, "ALLV")
                || sourceBody.items.size() != 4
                || targetBody.items.size() != 4
                || !sourceBody.items[1].atom
                || !targetBody.items[1].atom
                || sourceBody.items[1].token != quote(name)
                || targetBody.items[1].token != quote(name)
                || !(sourceBody.items[2] == type)
                || !(targetBody.items[2] == type)) {
              return std::string();
            }
            sourceBody = sourceBody.items[3];
            targetBody = targetBody.items[3];
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

        const bool propEqTrue = node.rule == "prop_eq_true"
          || node.rule == "prop_eq_true_lambda_alpha";
        const bool trueEqProp = node.rule == "true_eq_prop"
          || node.rule == "true_eq_prop_lambda_alpha";
        PreservedSexpr equalityType;
        PreservedSexpr equalityLeft;
        PreservedSexpr equalityRight;
        if ((!propEqTrue && !trueEqProp)
            || !node.binders.empty() || !node.children.empty()
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
        const std::string atomProofName = fresh("fool_atom");
        const std::string trueProofName = fresh("fool_true");
        const std::string atomToTrue = proofLambda(
          atomProofName, formula(atom.render()), truthProof());
        if (directionIs(node, "forward")) {
          const std::string trueToAtom = proofLambda(
            trueProofName, formula(trueTerm.render()), proof);
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
        return proofApply(
          proofApply(termApply(proof, motive), atomToTrue),
          truthProof());
      };

    if (parentId.empty() || program.version != "ivy_fool_formula_v1") {
      return false;
    }
    result = convert(
      program.root,
      instantiate(parent(parentId), parentArguments));
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
    if (injectLiteralOrSymmetry(
          target, otherOriented.render(), "proof_probe").empty()
        || injectLiteralOrSymmetry(
          target, introducedNegative.render(), "proof_probe").empty()) {
      return false;
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
    std::string& result)
  {
    if (equalityIndex >= equalityClause.size()
        || targetIndex >= targetClause.size()) {
      return false;
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
      return false;
    }

    PreservedSexpr equalityType;
    PreservedSexpr equalityLeft;
    PreservedSexpr equalityRight;
    if (!typedEqualitySexpr(
          equality.items[1], equalityType, equalityLeft, equalityRight)) {
      return false;
    }
    const bool leftToRight = equalityLeft == fromTerm && equalityRight == toTerm;
    const bool rightToLeft = equalityRight == fromTerm && equalityLeft == toTerm;
    if (!leftToRight && !rightToLeft) return false;

    PreservedSexpr directAtom;
    PreservedSexpr selectedAtPosition;
    if (!replaceSexprTermAtPosition(
          selectedTarget.items[1], position, toTerm,
          directAtom, &selectedAtPosition)
        || !(selectedAtPosition == fromTerm)) {
      return false;
    }
    const bool targetPositive = sexprHead(selectedTarget, "pos");
    const PreservedSexpr directLiteral = literalSexpr(targetPositive, directAtom);
    if (!rewriteSymmetry) {
      if (!(directLiteral == declaredRewritten)) return false;
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
        return false;
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
          return injectLiteral(
            target,
            equalityClause[equalityLiteralIndex],
            equalityProof);
        }
        return eliminate(
          targetClause,
          0,
          instantiate(parent(targetParent), targetParentArguments),
          targetTerm,
          [&](std::size_t targetLiteralIndex,
              const std::string& targetProof) {
            if (targetLiteralIndex != targetIndex) {
              return injectLiteral(
                target,
                targetClause[targetLiteralIndex],
                targetProof);
            }
            std::string directProof = equalityTransport(
              equalityType,
              selectedTarget,
              directAtom,
              position,
              leftToRight,
              equalityProof,
              targetProof);
            if (directProof.empty()) return std::string();
            if (rewriteSymmetry) {
              directProof = equalitySymmetry(directLiteral, directProof);
            }
            return directProof.empty()
              ? std::string()
              : injectLiteral(target, rewrittenLiteral, directProof);
          });
      });
    return !result.empty();
  }

private:
  std::size_t _fresh = 0;

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
    std::string value = "(clause (clause";
    for (const std::string& literal : literals) value += " " + literal;
    return value + "))";
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
    return std::string("ivy_sat_") + stem + std::to_string(_fresh++);
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
  std::string& error)
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
           result)) {
    error = "paramodulation is not the declared producer rewrite step";
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
  std::string& error)
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
        error = "positive AVATAR component direct proof does not support component variables";
        return false;
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
  const MegalodonKernelSyntax::RenderedKernelAvatarSplitStep& request,
  std::string& result,
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

  if (!request.hasIvyProgram || request.sourceUnit.value.empty()
      || request.sourceLiterals.empty() || !request.hasResultFormula
      || request.cases.empty()) {
    error = "AVATAR split direct proof lacks producer source/target data";
    return false;
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
      arguments.push_back(stage->directWitness.sexpr);
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
      const std::string pointwiseHyp = freshName("pointwise");
      const std::string pointwise = termLambda(
        variable.variable,
        variable.type.sexpr,
        proofLambda(
          pointwiseHyp,
          formula(formulaImp(
            stage.openBody.sexpr, "(TMH \"vampire_false\")")),
          hypothesis(pointwiseHyp)));
      const std::string existsNegative = proofApply(
        proofApply(
          termApply(
            termApply(
              known(notForall), formula(stage.positivePredicate.sexpr)),
            formula(stage.negativePredicate.sexpr)),
          pointwise),
        proof);
      proof = proofApply(
        termApply(known(choice), formula(stage.negativePredicate.sexpr)),
        existsNegative);
    }
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
      argument = counterexample->stages[binding->counterexampleStage]
        .directWitness.sexpr;
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
        std::string notComponent;
        if (clauseProof.empty()
            || !negativeComponent(
                 *component, componentRelation, assigned->proof, notComponent)) {
          return false;
        }
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
