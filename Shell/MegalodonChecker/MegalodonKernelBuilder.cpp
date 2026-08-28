#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"
#include "Shell/MegalodonChecker/MegalodonProofExpander.hpp"

#include "Kernel/Formula.hpp"
#include "Kernel/Signature.hpp"
#include "Kernel/Term.hpp"
#include "Kernel/Unit.hpp"
#include "Lib/Environment.hpp"
#include "SAT/SATClause.hpp"
#include "SAT/SATInference.hpp"

#include <algorithm>
#include <functional>
#include <limits>
#include <map>
#include <queue>
#include <set>
#include <tuple>
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

bool isRenderedVariableTerm(const std::string& term)
{
  const std::string prefix = "(TMH \"X";
  const std::string suffix = "\")";
  if (term.size() <= prefix.size() + suffix.size()
      || term.compare(0, prefix.size(), prefix) != 0
      || term.compare(term.size() - suffix.size(), suffix.size(), suffix) != 0) {
    return false;
  }
  return std::all_of(
    term.begin() + static_cast<std::ptrdiff_t>(prefix.size()),
    term.end() - static_cast<std::ptrdiff_t>(suffix.size()),
    [](char ch) { return ch >= '0' && ch <= '9'; });
}

bool isCanonicalDependency(
  const MegalodonKernelSyntax::RenderedKernelSkolemUse::Dependency& dependency)
{
  return dependency.termSexpr == "(TMH " + quote(dependency.variable) + ")";
}

MegalodonKernelSyntax::PrimitiveStep primitiveClauseStep(
  const std::string& rule,
  const std::string& id,
  const std::vector<std::string>& parentIds,
  const std::string& resultClause,
  const std::vector<std::pair<std::string, std::string>>& fields,
  const std::string& rendered,
  const std::vector<MegalodonKernelSyntax::ProducerFunctionApplication>&
    producerFunctionApplications = {})
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = rule;
  step.id = id;
  step.rendered = rendered;
  step.builderOwned = true;
  step.parentIds = parentIds;
  step.hasResultClause = true;
  step.resultClause = resultClause;
  step.producerFunctionApplications = producerFunctionApplications;
  step.fields = fields;
  return step;
}

std::string renderFoolProgramNode(
  const MegalodonKernelSyntax::RenderedKernelFoolProgramNode& node)
{
  std::string context = "(context";
  for (const auto& [name, type] : node.context) {
    context += " (variable " + quote(name) + " " + type.sexpr + ")";
  }
  context += ")";
  std::string binders = "(binders";
  for (const auto& [name, type] : node.binders) {
    binders += " (variable " + quote(name) + " " + type.sexpr + ")";
  }
  binders += ")";
  std::string children = "(children";
  for (const auto& child : node.children) {
    children += " " + renderFoolProgramNode(child);
  }
  children += ")";
  return
    "(node (index " + std::to_string(node.index) + ")"
    + " (rule " + quote(node.rule) + ")"
    + " (direction " + quote(node.direction) + ")"
    + " (source (formula " + node.source.sexpr + "))"
    + " (target (formula " + node.target.sexpr + "))"
    + " " + context
    + " " + binders
    + " " + children + ")";
}

}

std::string goalReplayBlock(
  const MegalodonKernelSyntax::RenderedKernelGoalReplay& replay)
{
  if (replay.version != "ivy_goal_replay_v1"
      || replay.finalStep.value.empty()
      || replay.conjectureStep.value.empty()
      || replay.conjectureFormula.sexpr.empty()
      || replay.negatedConjectureStep.value.empty()
      || replay.negatedConjectureFormula.sexpr.empty()
      || replay.closure != "classical_xm") {
    return "";
  }
  std::string sources = "(sources";
  for (const auto& source : replay.sources) {
    if (source.step.value.empty() || source.role.empty()) {
      return "";
    }
    sources +=
      " (source (step " + quote(source.step.value) + ")"
      + " (role " + quote(source.role) + "))";
  }
  sources += ")";
  return
    "(goal_replay_block " + quote(replay.version)
    + " (final " + quote(replay.finalStep.value) + ")"
    + " (conjecture (step " + quote(replay.conjectureStep.value) + ")"
    + " (formula " + replay.conjectureFormula.sexpr + "))"
    + " (negated_conjecture (step "
    + quote(replay.negatedConjectureStep.value) + ")"
    + " (formula " + replay.negatedConjectureFormula.sexpr + "))"
    + " " + sources
    + " (closure " + quote(replay.closure) + "))";
}

std::string PrimitiveChain::render(
  MegalodonKernelSyntax::PrimitiveStep primitive)
{
  const std::string rendered = primitive.rendered;
  _primitives[rendered] = std::move(primitive);
  return rendered;
}

bool PrimitiveChain::collect(
  const std::vector<std::string>& renderedSteps,
  std::vector<MegalodonKernelSyntax::PrimitiveStep>* primitiveSteps) const
{
  if (primitiveSteps == nullptr) {
    return true;
  }
  primitiveSteps->clear();
  for (const std::string& rendered : renderedSteps) {
    auto primitive = _primitives.find(rendered);
    if (primitive == _primitives.end()) {
      primitiveSteps->clear();
      return false;
    }
    primitiveSteps->push_back(primitive->second);
  }
  return true;
}

std::string skolemRefutationScopeBlock(
  const std::string& finalStep,
  const std::vector<MegalodonKernelSyntax::PrimitiveStep>& skolemSteps)
{
  if (finalStep.empty() || skolemSteps.empty()) {
    return "";
  }
  std::set<std::string> stepIds;
  std::set<std::string> symbols;
  std::string entries = "(entries";
  for (std::size_t index = 0; index < skolemSteps.size(); ++index) {
    const auto& step = skolemSteps[index];
    if (!step.builderOwned
      || step.rule != "skolem_formula"
      || step.id.empty()
      || step.certificateLocalSymbols.empty()
      || step.certificateLocalSymbols.size()
        != step.producerSkolemChoiceDefinitions.size()
      || !stepIds.insert(step.id).second) {
      return "";
    }
    entries +=
      " (entry (index " + std::to_string(index) + ")"
      + " (step " + quote(step.id) + ") (symbols";
    for (const std::string& symbol : step.certificateLocalSymbols) {
      if (symbol.empty() || !symbols.insert(symbol).second) {
        return "";
      }
      entries += " " + quote(symbol);
    }
    entries += ") (definitions";
    for (std::size_t definitionIndex = 0;
         definitionIndex < step.producerSkolemChoiceDefinitions.size();
         ++definitionIndex) {
      const auto& definition =
        step.producerSkolemChoiceDefinitions[definitionIndex];
      if (definition.symbol != step.certificateLocalSymbols[definitionIndex]
          || definition.witnessTypeSexpr.empty()
          || definition.witnessTermSexpr.empty()
          || definition.sourceFormulaSexpr.empty()) {
        return "";
      }
      entries +=
        " (choice_definition (index " + std::to_string(definitionIndex) + ")"
        + " (branch " + std::to_string(definition.branchIndex) + ")"
        + " (witness " + std::to_string(definition.witnessIndex) + ")"
        + " (symbol " + quote(definition.symbol) + ")"
        + " (witness_type " + definition.witnessTypeSexpr + ")"
        + " (term " + definition.witnessTermSexpr + ")"
        + " (parameters";
      for (const auto& parameter : definition.parameters) {
        entries +=
          " (variable " + quote(parameter.first) + " "
          + parameter.second + ")";
      }
      entries +=
        ") (source (formula " + definition.sourceFormulaSexpr + ")))";
    }
    entries += "))";
  }
  entries += ")";

  std::string dischargeOrder = "(discharge_order";
  for (auto step = skolemSteps.rbegin(); step != skolemSteps.rend(); ++step) {
    dischargeOrder += " " + quote(step->id);
  }
  dischargeOrder += ")";
  return
    "(skolem_scope_block \"smolka_refutation_v5\""
    " (final " + quote(finalStep) + ") "
    + entries + " " + dischargeOrder + ")";
}

std::string skolemRefutationUseBlock(
  const std::string& finalStep,
  const std::vector<MegalodonKernelSyntax::PrimitiveStep>& skolemSteps,
  const std::vector<MegalodonKernelSyntax::RenderedKernelSkolemUse>& uses)
{
  if (finalStep.empty() || skolemSteps.empty()) {
    return "";
  }
  std::map<std::pair<std::string, std::string>, std::size_t> declarations;
  for (const auto& step : skolemSteps) {
    if (!step.builderOwned
      || step.rule != "skolem_formula"
      || step.id.empty()
      || step.certificateLocalSymbols.empty()
      || step.certificateLocalSymbols.size()
        != step.certificateLocalSymbolDependencyCounts.size()) {
      return "";
    }
    for (std::size_t index = 0;
         index < step.certificateLocalSymbols.size();
         ++index) {
      const auto key = std::make_pair(
        step.id, step.certificateLocalSymbols[index]);
      if (key.second.empty()
        || !declarations.emplace(
          key, step.certificateLocalSymbolDependencyCounts[index]).second) {
        return "";
      }
    }
  }

  std::map<std::pair<std::string, std::string>,
    std::vector<MegalodonKernelSyntax::RenderedKernelSkolemUse>> grouped;
  std::set<std::tuple<std::string, std::string, std::string, std::string>> seen;
  for (const auto& use : uses) {
    const auto key = std::make_pair(use.skolemStep, use.symbol);
    auto declaration = declarations.find(key);
    if (declaration == declarations.end()
      || declaration->second != use.dependencyCount
      || use.unit.empty()
      || use.term.sexpr.empty()
      || !seen.emplace(
        use.skolemStep, use.symbol, use.unit, use.term.sexpr).second) {
      return "";
    }
    grouped[key].push_back(use);
  }

  std::string entries = "(entries";
  std::size_t entryIndex = 0;
  for (const auto& step : skolemSteps) {
    for (std::size_t symbolIndex = 0;
         symbolIndex < step.certificateLocalSymbols.size();
         ++symbolIndex) {
      const std::string& symbol = step.certificateLocalSymbols[symbolIndex];
      const auto key = std::make_pair(step.id, symbol);
      auto found = grouped.find(key);
      if (found == grouped.end() || found->second.empty()) {
        return "";
      }
      entries +=
        " (entry (index " + std::to_string(entryIndex++) + ")"
        + " (step " + quote(step.id) + ")"
        + " (symbol " + quote(symbol) + ")"
        + " (dependency_count "
        + std::to_string(step.certificateLocalSymbolDependencyCounts[symbolIndex])
        + ") (uses";
      for (std::size_t useIndex = 0;
           useIndex < found->second.size();
           ++useIndex) {
        const auto& use = found->second[useIndex];
        entries +=
          " (use (index " + std::to_string(useIndex) + ")"
          + " (unit " + quote(use.unit) + ")"
          + " (term " + use.term.sexpr + "))";
      }
      entries += "))";
    }
  }
  entries += ")";
  return
    "(skolem_use_block \"smolka_uses_v2\""
    " (final " + quote(finalStep) + ") " + entries + ")";
}

std::string skolemFiniteUnherbrandizationBlock(
  const std::string& finalStep,
  const std::vector<MegalodonKernelSyntax::RenderedKernelSkolemUse>& uses,
  const MegalodonKernelSyntax::RenderedKernelGroundProof& proof,
  std::string& error)
{
  using SkolemUse = MegalodonKernelSyntax::RenderedKernelSkolemUse;
  using ApplicationKey = std::tuple<std::string, std::string, std::string>;
  if (finalStep.empty() || uses.empty() || proof.instances.empty()) {
    error = "finite plan has no final step, applications, or instance graph";
    return "";
  }

  struct Application {
    const SkolemUse* canonical = nullptr;
    const SkolemUse* owner = nullptr;
    std::vector<const SkolemUse*> occurrences;
    std::vector<std::size_t> dependencies;
  };
  std::map<ApplicationKey, std::map<std::size_t, const SkolemUse*>> owners;
  std::map<std::pair<std::string, std::string>,
    std::vector<const SkolemUse*>> ownerFamilies;
  for (const auto& use : uses) {
    if (!use.skolemStepOwner) {
      continue;
    }
    const ApplicationKey key = {use.skolemStep, use.symbol, use.term.sexpr};
    if (!owners[key].emplace(use.groundInstance, &use).second) {
      error = "finite instance graph repeats a Skolem-step owner application";
      return "";
    }
    ownerFamilies[{use.skolemStep, use.symbol}].push_back(&use);
  }

  std::vector<std::size_t> rootDistance(
    proof.instances.size(), std::numeric_limits<std::size_t>::max());
  std::queue<std::size_t> distanceQueue;
  rootDistance[0] = 0;
  distanceQueue.push(0);
  for (const auto& instance : proof.instances) {
    if (instance.index >= rootDistance.size()) {
      error = "finite instance graph has a noncontiguous instance index";
      return "";
    }
    for (std::size_t parent : instance.parentInstances) {
      if (parent >= rootDistance.size()) {
        error = "finite instance graph has an out-of-bounds parent";
        return "";
      }
    }
  }
  while (!distanceQueue.empty()) {
    const std::size_t current = distanceQueue.front();
    distanceQueue.pop();
    for (std::size_t parent : proof.instances[current].parentInstances) {
      if (rootDistance[parent] > rootDistance[current] + 1) {
        rootDistance[parent] = rootDistance[current] + 1;
        distanceQueue.push(parent);
      }
    }
  }
  const auto nearestOwner =
    [&](const std::vector<const SkolemUse*>& candidates) -> const SkolemUse* {
      const SkolemUse* result = nullptr;
      for (const SkolemUse* candidate : candidates) {
        if (result == nullptr
            || std::make_pair(
                 rootDistance[candidate->groundInstance],
                 candidate->groundInstance)
               < std::make_pair(
                   rootDistance[result->groundInstance],
                   result->groundInstance)) {
          result = candidate;
        }
      }
      return result;
    };
  const auto findOwner =
    [&](const SkolemUse& use) -> const SkolemUse* {
      const ApplicationKey exactKey = {
        use.skolemStep, use.symbol, use.term.sexpr};
      std::vector<const SkolemUse*> exactCandidates;
      auto exact = owners.find(exactKey);
      if (exact != owners.end()) {
        for (const auto& candidate : exact->second) {
          exactCandidates.push_back(candidate.second);
        }
      }
      std::vector<const SkolemUse*> genericCandidates;
      auto family = ownerFamilies.find({use.skolemStep, use.symbol});
      if (family != ownerFamilies.end()) {
        for (const SkolemUse* candidate : family->second) {
          if (candidate->branchIndex != use.branchIndex
              || candidate->witnessIndex != use.witnessIndex
              || candidate->witnessTypeSexpr != use.witnessTypeSexpr
              || candidate->dependencies.size() != use.dependencies.size()) {
            continue;
          }
          bool compatible = true;
          for (std::size_t index = 0;
               index < candidate->dependencies.size();
               ++index) {
            const auto& canonical = candidate->dependencies[index];
            const auto& occurrence = use.dependencies[index];
            if (!isCanonicalDependency(canonical)
                || canonical.variable != occurrence.variable
                || canonical.typeSexpr != occurrence.typeSexpr) {
              compatible = false;
              break;
            }
          }
          if (compatible) {
            genericCandidates.push_back(candidate);
          }
        }
      }
      const bool symbolicOccurrence =
        !use.dependencies.empty()
        && std::all_of(
          use.dependencies.begin(),
          use.dependencies.end(),
          [](const auto& dependency) {
            return isRenderedVariableTerm(dependency.termSexpr);
          });
      if (symbolicOccurrence && !genericCandidates.empty()) {
        return nearestOwner(genericCandidates);
      }
      if (!exactCandidates.empty()) {
        return nearestOwner(exactCandidates);
      }
      return nearestOwner(genericCandidates);
    };

  std::map<ApplicationKey, std::size_t> groupedIndex;
  std::map<ApplicationKey, std::vector<std::size_t>> applicationIndices;
  std::vector<Application> applications;
  for (const auto& use : uses) {
    if (use.skolemStep.empty()
      || use.symbol.empty()
      || use.witnessTypeSexpr.empty()
      || use.sourceFormulaSexpr.empty()
      || use.sourceInstanceSexpr.empty()
      || use.stageSourceInstanceSexpr.empty()
      || use.stageTargetInstanceSexpr.empty()
      || use.dependencies.size() != use.dependencyCount
      || use.unit.empty()
      || use.term.sexpr.empty()
      || use.occurrenceCount == 0
      || !use.hasGroundInstance) {
      error = "finite application is missing typed producer data";
      return "";
    }
    const SkolemUse* owner = findOwner(use);
    if (owner == nullptr) {
      error = "finite application " + use.term.sexpr
        + " at " + use.unit + "/instance "
        + std::to_string(use.groundInstance)
        + " has no ancestor occurrence at Skolem step " + use.skolemStep;
      return "";
    }
    const ApplicationKey groupKey = {
      owner->skolemStep,
      owner->symbol,
      owner->term.sexpr,
    };
    auto inserted = groupedIndex.emplace(groupKey, applications.size());
    if (inserted.second) {
      Application application;
      application.canonical = owner;
      application.owner = owner;
      applications.push_back(std::move(application));
    }
    const std::size_t index = inserted.first->second;
    auto& indices =
      applicationIndices[{use.skolemStep, use.symbol, use.term.sexpr}];
    if (std::find(indices.begin(), indices.end(), index) == indices.end()) {
      indices.push_back(index);
    }
    applications[index].occurrences.push_back(&use);
  }

  std::vector<std::vector<std::size_t>> successors(applications.size());
  std::vector<std::size_t> indegree(applications.size(), 0);
  const auto addDependency =
    [&](std::size_t predecessor, std::size_t successor) {
      if (predecessor == successor
          || std::find(
               successors[predecessor].begin(),
               successors[predecessor].end(),
               successor) != successors[predecessor].end()) {
        return;
      }
      successors[predecessor].push_back(successor);
      ++indegree[successor];
    };
  for (std::size_t outer = 0; outer < applications.size(); ++outer) {
    std::set<std::size_t> nestedIndices;
    for (const auto& dependency : applications[outer].canonical->dependencies) {
      for (const auto& nested : dependency.nestedApplications) {
        auto found = applicationIndices.find({
          nested.skolemStep,
          nested.symbol,
          nested.termSexpr,
        });
        if (found == applicationIndices.end()) {
          error = "finite application references a missing nested dependency";
          return "";
        }
        for (std::size_t nestedIndex : found->second) {
          if (nestedIndex != outer) {
            nestedIndices.insert(nestedIndex);
          }
        }
      }
    }
    applications[outer].dependencies.assign(
      nestedIndices.begin(), nestedIndices.end());
    for (std::size_t inner : nestedIndices) {
      addDependency(inner, outer);
    }
  }

  // Scoped branch paths are recorded against the formula produced by all
  // earlier branches of the same Skolemization step.  Preserve that producer
  // chronology explicitly in the finite discharge plan.
  for (std::size_t successor = 0;
       successor < applications.size();
       ++successor) {
    const SkolemUse& current = *applications[successor].canonical;
    for (std::size_t predecessor = 0;
         predecessor < applications.size();
         ++predecessor) {
      const SkolemUse& prior = *applications[predecessor].canonical;
      if (prior.skolemStep == current.skolemStep
          && prior.branchIndex < current.branchIndex) {
        addDependency(predecessor, successor);
      }
    }
  }

  // A retained-ambient application abstracts a whole symbolic family.  Its
  // concrete members must be discharged first so that the uniform lift sees
  // the already-specialized branch proof.
  for (std::size_t symbolicIndex = 0;
       symbolicIndex < applications.size();
       ++symbolicIndex) {
    const SkolemUse& symbolic = *applications[symbolicIndex].canonical;
    const bool isSymbolic =
      !symbolic.dependencies.empty()
      && std::all_of(
           symbolic.dependencies.begin(),
           symbolic.dependencies.end(),
           [](const auto& dependency) {
             return isCanonicalDependency(dependency);
           });
    if (!isSymbolic) {
      continue;
    }
    for (std::size_t concreteIndex = 0;
         concreteIndex < applications.size();
         ++concreteIndex) {
      const SkolemUse& concrete = *applications[concreteIndex].canonical;
      const bool sameWitness =
        concrete.skolemStep == symbolic.skolemStep
        && concrete.symbol == symbolic.symbol
        && concrete.branchIndex == symbolic.branchIndex
        && concrete.witnessIndex == symbolic.witnessIndex;
      const bool isConcrete =
        concrete.dependencies.empty()
        || std::any_of(
             concrete.dependencies.begin(),
             concrete.dependencies.end(),
             [](const auto& dependency) {
               return !isCanonicalDependency(dependency);
             });
      if (sameWitness && isConcrete) {
        addDependency(concreteIndex, symbolicIndex);
      }
    }
  }

  for (std::size_t outer = 0; outer < applications.size(); ++outer) {
    const SkolemUse& current = *applications[outer].canonical;
    if (current.witnessIndex == 0) {
      continue;
    }
    std::vector<std::size_t> predecessors;
    for (std::size_t candidate = 0;
         candidate < applications.size();
         ++candidate) {
      const SkolemUse& prior = *applications[candidate].canonical;
      if (prior.skolemStep == current.skolemStep
          && prior.branchIndex == current.branchIndex
          && prior.witnessIndex + 1 == current.witnessIndex
          && prior.stageTargetInstanceSexpr
             == current.stageSourceInstanceSexpr) {
        predecessors.push_back(candidate);
      }
    }
    if (predecessors.size() != 1) {
      error = "finite witness stage has no unique preceding stage";
      return "";
    }
    const std::size_t predecessor = predecessors.front();
    addDependency(predecessor, outer);
  }

  std::priority_queue<
    std::size_t,
    std::vector<std::size_t>,
    std::greater<std::size_t>> ready;
  for (std::size_t index = 0; index < indegree.size(); ++index) {
    if (indegree[index] == 0) {
      ready.push(index);
    }
  }
  std::vector<std::size_t> order;
  while (!ready.empty()) {
    const std::size_t current = ready.top();
    ready.pop();
    order.push_back(current);
    for (std::size_t successor : successors[current]) {
      if (--indegree[successor] == 0) {
        ready.push(successor);
      }
    }
  }
  if (order.size() != applications.size()) {
    error = "finite application dependency graph is cyclic";
    return "";
  }

  std::string renderedApplications = "(applications";
  for (std::size_t index = 0; index < applications.size(); ++index) {
    const auto& application = applications[index];
    const auto& canonical = *application.canonical;
    const SkolemUse* owner = application.owner;
    if (owner == nullptr) {
      error = "finite application " + canonical.term.sexpr
        + " has no exact occurrence at Skolem step " + canonical.skolemStep;
      return "";
    }
    renderedApplications +=
      " (application (index " + std::to_string(index) + ")"
      + " (step " + quote(canonical.skolemStep) + ")"
      + " (branch " + std::to_string(canonical.branchIndex) + ")"
      + " (witness " + std::to_string(canonical.witnessIndex) + ")"
      + " (owner_instance " + std::to_string(owner->groundInstance) + ")"
      + " (symbol " + quote(canonical.symbol) + ")"
      + " (witness_type " + canonical.witnessTypeSexpr + ")"
      + " (term " + canonical.term.sexpr + ")"
      + " (source (formula " + canonical.sourceFormulaSexpr + "))"
      + " (source_instance (formula " + canonical.sourceInstanceSexpr + "))"
      + " (stage_source_instance (formula "
      + canonical.stageSourceInstanceSexpr + "))"
      + " (stage_target_instance (formula "
      + canonical.stageTargetInstanceSexpr + "))"
      + " (dependencies";
    for (std::size_t dependencyIndex = 0;
         dependencyIndex < canonical.dependencies.size();
         ++dependencyIndex) {
      const auto& dependency = canonical.dependencies[dependencyIndex];
      renderedApplications +=
        " (dependency (index " + std::to_string(dependencyIndex) + ")"
        + " (variable " + quote(dependency.variable) + ")"
        + " (type " + dependency.typeSexpr + ")"
        + " (term " + dependency.termSexpr + ")"
        + " (nested";
      std::set<std::size_t> renderedNested;
      for (const auto& nested : dependency.nestedApplications) {
        auto found = applicationIndices.find({
          nested.skolemStep,
          nested.symbol,
          nested.termSexpr,
        });
        if (found == applicationIndices.end()) {
          error = "finite dependency references an application omitted from the plan";
          return "";
        }
        for (std::size_t nestedIndex : found->second) {
          if (nestedIndex != index) {
            renderedNested.insert(nestedIndex);
          }
        }
      }
      for (std::size_t nested : renderedNested) {
        renderedApplications +=
          " (application " + std::to_string(nested) + ")";
      }
      renderedApplications += "))";
    }
    renderedApplications += ") (occurrences";
    std::size_t occurrenceIndex = 0;
    for (const auto* use : application.occurrences) {
      for (std::size_t ordinal = 0; ordinal < use->occurrenceCount; ++ordinal) {
        renderedApplications +=
          " (occurrence (index " + std::to_string(occurrenceIndex++) + ")"
          + " (unit " + quote(use->unit) + ")"
          + " (instance " + std::to_string(use->groundInstance) + ")"
          + " (term " + use->term.sexpr + ")"
          + " (specialization (subst";
        if (canonical.dependencies.size() != use->dependencies.size()) {
          error = "finite symbolic occurrence has a different dependency arity from its owner";
          return "";
        }
        for (std::size_t dependencyIndex = 0;
             dependencyIndex < canonical.dependencies.size();
             ++dependencyIndex) {
          const auto& sourceDependency =
            canonical.dependencies[dependencyIndex];
          const auto& occurrenceDependency =
            use->dependencies[dependencyIndex];
          if (isCanonicalDependency(sourceDependency)
              && sourceDependency.termSexpr
                 != occurrenceDependency.termSexpr) {
            renderedApplications +=
              " (" + quote(sourceDependency.variable) + " "
              + occurrenceDependency.termSexpr + ")";
          }
        }
        renderedApplications += "))";
        renderedApplications +=
          " (ordinal " + std::to_string(ordinal) + "))";
      }
    }
    renderedApplications += "))";
  }
  renderedApplications += ")";

  std::string dischargeOrder = "(discharge_order";
  for (std::size_t index : order) {
    dischargeOrder += " " + std::to_string(index);
  }
  dischargeOrder += ")";
  return
    "(skolem_unherbrandization_block \"smolka_finite_v5\""
    " (final " + quote(finalStep) + ") "
    + renderedApplications + " " + dischargeOrder + ")";
}

std::string skolemGroundProofBlock(
  const MegalodonKernelSyntax::RenderedKernelGroundProof& proof)
{
  if (proof.version != "ivy_instance_v3"
      || proof.finalStep.value.empty()
      || proof.instances.empty()) {
    return "";
  }
  std::string result =
    "(skolem_ground_proof_block " + quote(proof.version)
    + " (final " + quote(proof.finalStep.value) + ") (instances";
  for (std::size_t expected = 0; expected < proof.instances.size(); ++expected) {
    const auto& instance = proof.instances[expected];
    if (instance.index != expected || instance.unit.value.empty()) {
      return "";
    }
    result +=
      " (instance (index " + std::to_string(instance.index) + ")"
      + " (unit " + quote(instance.unit.value) + ")"
      + " (parametric " + (instance.parametric ? "true" : "false") + ")"
      + " (environment (subst";
    for (const auto& binding : instance.environment) {
      if (binding.variable.empty() || binding.term.sexpr.empty()) {
        return "";
      }
      result +=
        " (" + quote(binding.variable) + " " + binding.term.sexpr + ")";
    }
    if (instance.parentInstances.size()
        != instance.parentEnvironments.size()) {
      return "";
    }
    result += ")) (parents";
    for (std::size_t parentIndex = 0;
         parentIndex < instance.parentInstances.size();
         ++parentIndex) {
      result += " (parent (instance "
        + std::to_string(instance.parentInstances[parentIndex])
        + ") (environment (subst";
      for (const auto& binding : instance.parentEnvironments[parentIndex]) {
        if (binding.variable.empty() || binding.term.sexpr.empty()) {
          return "";
        }
        result +=
          " (" + quote(binding.variable) + " " + binding.term.sexpr + ")";
      }
      result += ")))";
    }
    result += ") (applications";
    for (const auto& application : instance.applications) {
      if (application.skolemStep.empty()
          || application.symbol.empty()
          || application.term.sexpr.empty()) {
        return "";
      }
      result +=
        " (application (step " + quote(application.skolemStep) + ")"
        + " (symbol " + quote(application.symbol) + ")"
        + " (term " + application.term.sexpr + "))";
    }
    result += "))";
  }
  return result + "))";
}

std::string avatarPrimitiveWithMetadata(
  const MegalodonKernelSyntax::PrimitiveStep& step)
{
  std::vector<std::pair<std::string, std::string>> fields{
    {"schema", MegalodonKernelSyntax::schema()},
    {"rule", step.rule},
    {"primitive_expansion", "prefix"},
    {"primitive_expansion_prefix", step.id},
    {"primitive_expansion_requires", step.rule},
  };
  fields.insert(fields.end(), step.fields.begin(), step.fields.end());
  if (step.hasResultClause) {
    fields.push_back({"result_clause", step.resultClause});
  }
  std::string rendered =
    "(step_extra " + quote(step.id) + " \"avatar_scope_v1\" (";
  for (std::size_t index = 0; index < fields.size(); ++index) {
    if (index != 0) {
      rendered += " ";
    }
    rendered += quote(fields[index].first + "=" + fields[index].second);
  }
  rendered += "))";
  return rendered + "\n  " + step.rendered;
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

MegalodonKernelSyntax::PrimitiveStep resolveIvyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& leftParent,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& rightParent,
  std::size_t leftPivot,
  std::size_t rightPivot,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::string>& leftLiterals,
  const std::vector<std::string>& rightLiterals,
  const std::vector<std::string>& resultLiterals,
  const std::string& producerProof)
{
  if (leftPivot >= leftLiterals.size()
    || rightPivot >= rightLiterals.size()
    || producerProof.empty()
    || resultLiterals.size() + 2 != leftLiterals.size() + rightLiterals.size()) {
    return resolveStep(
      id, leftParent, rightParent, leftPivot, rightPivot, result);
  }

  std::vector<bool> usedResult(resultLiterals.size(), false);
  std::size_t nodeIndex = 0;
  auto clauseSexpr = [](const std::vector<std::string>& literals) {
    std::string rendered = "(clause";
    for (const std::string& literal : literals) {
      rendered += " " + literal;
    }
    return rendered + ")";
  };
  auto sideProgram =
    [&](const char* side,
        const std::vector<std::string>& literals,
        std::size_t pivot,
        std::string& rendered) {
      rendered = "(" + std::string(side) + " (source "
        + clauseSexpr(literals) + ") (nodes";
      for (std::size_t literalIndex = 0; literalIndex < literals.size(); ++literalIndex) {
        rendered += " (node (index " + std::to_string(nodeIndex++)
          + ") (literal " + std::to_string(literalIndex) + ")";
        if (literalIndex == pivot) {
          rendered += " (action \"pivot\"))";
          continue;
        }
        std::size_t target = resultLiterals.size();
        for (std::size_t resultIndex = 0;
             resultIndex < resultLiterals.size();
             ++resultIndex) {
          if (!usedResult[resultIndex]
            && literals[literalIndex] == resultLiterals[resultIndex]) {
            target = resultIndex;
            break;
          }
        }
        if (target == resultLiterals.size()) {
          return false;
        }
        usedResult[target] = true;
        rendered += " (action \"copy\") (target "
          + std::to_string(target) + "))";
      }
      rendered += "))";
      return true;
    };

  std::string leftProgram;
  std::string rightProgram;
  if (!sideProgram("left", leftLiterals, leftPivot, leftProgram)
    || !sideProgram("right", rightLiterals, rightPivot, rightProgram)
    || std::find(usedResult.begin(), usedResult.end(), false) != usedResult.end()) {
    return resolveStep(
      id, leftParent, rightParent, leftPivot, rightPivot, result);
  }

  MegalodonKernelSyntax::PrimitiveStep step = resolveStep(
    id, leftParent, rightParent, leftPivot, rightPivot, result);
  step.rendered.pop_back();
  step.rendered += " (program \"ivy_resolve_v2\" "
    + leftProgram + " " + rightProgram
    + " (producer_proof (program \"ivy_nd_v1\" (proof "
    + producerProof + ")))))";
  return step;
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

MegalodonKernelSyntax::PrimitiveStep factorIvyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t leftLiteral,
  std::size_t rightLiteral,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  const std::string& producerProof)
{
  const std::size_t removed = std::max(leftLiteral, rightLiteral);
  const std::size_t retained = std::min(leftLiteral, rightLiteral);
  if (leftLiteral >= sourceLiterals.size()
    || rightLiteral >= sourceLiterals.size()
    || leftLiteral == rightLiteral
    || sourceLiterals[leftLiteral] != sourceLiterals[rightLiteral]
    || producerProof.empty()
    || resultLiterals.size() + 1 != sourceLiterals.size()) {
    return factorStep(id, parent, leftLiteral, rightLiteral, result);
  }

  std::vector<std::size_t> targets(sourceLiterals.size(), resultLiterals.size());
  std::vector<bool> usedResult(resultLiterals.size(), false);
  for (std::size_t sourceIndex = 0;
       sourceIndex < sourceLiterals.size();
       ++sourceIndex) {
    if (sourceIndex == removed) {
      continue;
    }
    for (std::size_t resultIndex = 0;
         resultIndex < resultLiterals.size();
         ++resultIndex) {
      if (!usedResult[resultIndex]
        && sourceLiterals[sourceIndex] == resultLiterals[resultIndex]) {
        targets[sourceIndex] = resultIndex;
        usedResult[resultIndex] = true;
        break;
      }
    }
    if (targets[sourceIndex] == resultLiterals.size()) {
      return factorStep(id, parent, leftLiteral, rightLiteral, result);
    }
  }
  if (targets[retained] == resultLiterals.size()
    || std::find(usedResult.begin(), usedResult.end(), false)
       != usedResult.end()) {
    return factorStep(id, parent, leftLiteral, rightLiteral, result);
  }
  targets[removed] = targets[retained];

  std::string sourceClause = "(clause";
  for (const std::string& literal : sourceLiterals) {
    sourceClause += " " + literal;
  }
  sourceClause += ")";
  std::string program =
    "(program \"ivy_factor_v2\" (source " + sourceClause + ") (nodes";
  for (std::size_t sourceIndex = 0;
       sourceIndex < sourceLiterals.size();
       ++sourceIndex) {
    program += " (node (index " + std::to_string(sourceIndex)
      + ") (literal " + std::to_string(sourceIndex) + ") (action \""
      + (sourceIndex == removed ? "merge" : "copy") + "\") (target "
      + std::to_string(targets[sourceIndex]) + "))";
  }
  program += ") (producer_proof (program \"ivy_nd_v1\" (proof "
    + producerProof + "))))";

  MegalodonKernelSyntax::PrimitiveStep step =
    factorStep(id, parent, leftLiteral, rightLiteral, result);
  step.rendered.pop_back();
  step.rendered += " " + program + ")";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep equalitySymmetryStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::string& producerProof)
{
  const std::string literalText = std::to_string(literal);
  MegalodonKernelSyntax::PrimitiveStep step = primitiveClauseStep(
    "equality_symmetry",
    id,
    {parent.value},
    result.sexpr,
    {{"literal", literalText}},
    "(equality_symmetry " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (result " + result.sexpr + "))");
  if (!producerProof.empty()) {
    step.rendered.pop_back();
    step.rendered +=
      " (program \"ivy_equality_symmetry_v2\""
      " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + ")))))";
    step.producerProof = producerProof;
  }
  return step;
}

MegalodonKernelSyntax::PrimitiveStep substituteStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelSubstitution& substitution,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::string& producerProof)
{
  MegalodonKernelSyntax::PrimitiveStep step = primitiveClauseStep(
    "substitute",
    id,
    {parent.value},
    result.sexpr,
    {{"substitution", substitution.sexpr}},
    "(substitute " + quote(id)
      + " (parent " + quote(parent.value) + ") " + substitution.sexpr
      + " (result " + result.sexpr + "))",
    result.producerFunctionApplications);
  if (!producerProof.empty()) {
    step.rendered.pop_back();
    step.rendered +=
      " (program \"ivy_substitute_v2\""
      " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + ")))))";
    step.producerProof = producerProof;
  }
  return step;
}

MegalodonKernelSyntax::PrimitiveStep equalityResolutionStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::pair<std::string, std::string>>& metadataFields,
  const std::string& producerProof)
{
  const std::string literalText = std::to_string(literal);
  MegalodonKernelSyntax::PrimitiveStep step = primitiveClauseStep(
    "equality_resolution",
    id,
    {parent.value},
    result.sexpr,
    metadataFields,
    "(equality_resolution " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + literalText + ")"
      + " (result " + result.sexpr + "))");
  if (!producerProof.empty()) {
    step.rendered.pop_back();
    step.rendered +=
      " (program \"ivy_equality_resolution_v2\""
      " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + ")))))";
  }
  return step;
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

MegalodonKernelSyntax::PrimitiveStep truthConflictStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  std::size_t literal,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::string& producerProof)
{
  MegalodonKernelSyntax::PrimitiveStep step = primitiveClauseStep(
    "truth_conflict",
    id,
    {parent.value},
    result.sexpr,
    {{"literal", std::to_string(literal)}},
    "(truth_conflict " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (literal " + std::to_string(literal) + ")"
      + " (result " + result.sexpr + "))");
  if (!producerProof.empty()) {
    step.rendered.pop_back();
    step.rendered +=
      " (program \"ivy_truth_conflict_v2\""
      " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + ")))))";
    step.producerProof = producerProof;
  }
  return step;
}

MegalodonKernelSyntax::PrimitiveStep paramodulateStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& equalityParent,
  std::size_t equalityLiteral,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& targetParent,
  std::size_t targetLiteral,
  const MegalodonKernelSyntax::RenderedKernelPosition& position,
  const MegalodonKernelSyntax::RenderedKernelTerm& from,
  const MegalodonKernelSyntax::RenderedKernelTerm& to,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  const std::string equalityLiteralText = std::to_string(equalityLiteral);
  const std::string targetLiteralText = std::to_string(targetLiteral);
  return primitiveClauseStep(
    "paramodulate",
    id,
    {equalityParent.value, targetParent.value},
    result.sexpr,
    {
      {"equality_literal", equalityLiteralText},
      {"target_literal", targetLiteralText},
      {"position", position.sexpr},
      {"from", from.sexpr},
      {"to", to.sexpr},
    },
    "(paramodulate " + quote(id)
      + " (equality " + quote(equalityParent.value) + " " + equalityLiteralText + ")"
      + " (target " + quote(targetParent.value) + " " + targetLiteralText + ") "
      + position.sexpr
      + " (from " + from.sexpr + ")"
      + " (to " + to.sexpr + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep paramodulateIvyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& equalityParent,
  std::size_t equalityLiteral,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& targetParent,
  std::size_t targetLiteral,
  const MegalodonKernelSyntax::RenderedKernelPosition& position,
  const MegalodonKernelSyntax::RenderedKernelTerm& from,
  const MegalodonKernelSyntax::RenderedKernelTerm& to,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::string>& equalityLiterals,
  const std::vector<std::string>& targetLiterals,
  const std::string& rewrittenLiteral,
  const std::vector<std::string>& resultLiterals,
  bool rewriteSymmetry,
  const std::string& producerProof)
{
  if (equalityLiteral >= equalityLiterals.size()
    || targetLiteral >= targetLiterals.size()
    || rewrittenLiteral.empty()
    || producerProof.empty()
    || resultLiterals.size() + 1
       != equalityLiterals.size() + targetLiterals.size()) {
    return paramodulateStep(
      id, equalityParent, equalityLiteral, targetParent, targetLiteral,
      position, from, to, result);
  }

  std::vector<bool> usedResult(resultLiterals.size(), false);
  std::size_t nodeIndex = 0;
  auto clauseSexpr = [](const std::vector<std::string>& literals) {
    std::string rendered = "(clause";
    for (const std::string& literal : literals) {
      rendered += " " + literal;
    }
    return rendered + ")";
  };
  auto takeTarget =
    [&](const std::string& literal, std::size_t& target) {
      target = resultLiterals.size();
      for (std::size_t resultIndex = 0;
           resultIndex < resultLiterals.size();
           ++resultIndex) {
        if (!usedResult[resultIndex]
          && literal == resultLiterals[resultIndex]) {
          target = resultIndex;
          usedResult[resultIndex] = true;
          return true;
        }
      }
      return false;
    };
  auto sideProgram =
    [&](const char* side,
        const std::vector<std::string>& literals,
        std::size_t selected,
        const char* selectedAction,
        const std::string* selectedResult,
        std::string& rendered) {
      rendered = "(" + std::string(side) + " (source "
        + clauseSexpr(literals) + ") (nodes";
      for (std::size_t literalIndex = 0;
           literalIndex < literals.size();
           ++literalIndex) {
        rendered += " (node (index " + std::to_string(nodeIndex++)
          + ") (literal " + std::to_string(literalIndex) + ")";
        if (literalIndex == selected && selectedResult == nullptr) {
          rendered += " (action \"" + std::string(selectedAction) + "\"))";
          continue;
        }
        const std::string& produced =
          literalIndex == selected ? *selectedResult : literals[literalIndex];
        std::size_t target = resultLiterals.size();
        if (!takeTarget(produced, target)) {
          return false;
        }
        rendered += " (action \""
          + std::string(literalIndex == selected ? selectedAction : "copy")
          + "\") (target " + std::to_string(target) + "))";
      }
      rendered += "))";
      return true;
    };

  std::string equalityProgram;
  std::string targetProgram;
  if (!sideProgram(
        "equality", equalityLiterals, equalityLiteral, "equality", nullptr,
        equalityProgram)
    || !sideProgram(
         "target", targetLiterals, targetLiteral,
         rewriteSymmetry ? "rewrite_symmetry" : "rewrite",
         &rewrittenLiteral, targetProgram)
    || std::find(usedResult.begin(), usedResult.end(), false)
       != usedResult.end()) {
    return paramodulateStep(
      id, equalityParent, equalityLiteral, targetParent, targetLiteral,
      position, from, to, result);
  }

  MegalodonKernelSyntax::PrimitiveStep step = paramodulateStep(
    id, equalityParent, equalityLiteral, targetParent, targetLiteral,
    position, from, to, result);
  step.rendered.pop_back();
  step.rendered += " (program \"ivy_paramodulate_v2\" "
    + equalityProgram + " " + targetProgram
    + " (rewritten " + rewrittenLiteral + ")"
    + " (producer_proof (program \"ivy_nd_v1\" (proof "
    + producerProof + ")))))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep foolAtomLiftStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFormula& target,
  const std::string& path,
  const std::vector<std::pair<
    std::string,
    MegalodonKernelSyntax::RenderedKernelType>>& context)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "fool_atom_lift";
  step.id = id;
  step.builderOwned = true;
  step.fields = {
    {"source_formula", source.sexpr},
    {"target_formula", target.sexpr},
    {"path", path},
  };
  std::string renderedContext = "(context";
  step.fields.push_back({"context_count", std::to_string(context.size())});
  for (std::size_t index = 0; index < context.size(); ++index) {
    renderedContext +=
      " (variable " + quote(context[index].first)
      + " " + context[index].second.sexpr + ")";
    step.fields.push_back({
      "context_" + std::to_string(index) + "_name",
      context[index].first,
    });
    step.fields.push_back({
      "context_" + std::to_string(index) + "_type",
      context[index].second.sexpr,
    });
  }
  renderedContext += ")";
  step.rendered =
    "(fool_atom_lift " + quote(id)
    + " (source (formula " + source.sexpr + "))"
    + " (target (formula " + target.sexpr + "))"
    + " (path " + quote(path) + ")"
    + " " + renderedContext
    + " (builder \"typed_v1\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep foolFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "fool_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {{"result_formula", result.sexpr}};
  step.rendered =
    "(fool_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (result (formula " + result.sexpr + ")))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep foolFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFoolProgram& program,
  const MegalodonKernelSyntax::RenderedKernelFormula& result,
  const std::string& producerProof)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "fool_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {
    {"source_formula", source.sexpr},
    {"result_formula", result.sexpr},
    {"program", program.version},
  };
  step.rendered =
    "(fool_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + "))"
    + " (result (formula " + result.sexpr + "))"
    + " (program " + quote(program.version) + " "
    + renderFoolProgramNode(program.root) + ")"
    + " (producer_proof (program \"ivy_nd_v1\" (proof "
    + producerProof + ")))"
    + " (builder \"typed_v3\"))";
  step.producerProof = producerProof;
  return step;
}

MegalodonKernelSyntax::PrimitiveStep foolBoolStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelLiteral& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "fool_bool";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.fields = {{"result_literal", result.sexpr}};
  step.rendered =
    "(fool_bool " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (result " + result.sexpr + "))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep rectifyFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelFormula& result,
  const MegalodonKernelSyntax::RenderedKernelRectifyRenamings& renamings)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "rectify_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields.push_back({"source_formula", source.sexpr});
  step.fields.push_back({
    "renaming_count",
    std::to_string(renamings.reportedCount),
  });
  if (renamings.hasVariableMap) {
    step.fields.push_back({
      "free_variable_map",
      renamings.variableMap.sexpr,
    });
  }

  std::string renderedRenamings;
  if (!renamings.renamings.empty()) {
    renderedRenamings = " (renamings";
    for (const auto& renaming : renamings.renamings) {
      renderedRenamings +=
        " (renaming (source (formula " + renaming.source.sexpr + ")) "
        + renaming.substitution.sexpr
        + " (ambient_variable_map " + renaming.ambientVariableMap.sexpr + ")"
        + " (target (formula " + renaming.target.sexpr + ")))";
      const std::string prefix =
        "renaming_" + std::to_string(renaming.index);
      step.fields.push_back({prefix + "_source", renaming.source.sexpr});
      step.fields.push_back({prefix + "_target", renaming.target.sexpr});
      step.fields.push_back({
        prefix + "_substitution",
        renaming.substitution.sexpr,
      });
      step.fields.push_back({
        prefix + "_ambient_variable_map",
        renaming.ambientVariableMap.sexpr,
      });
    }
    renderedRenamings += ")";
  }
  const std::string renderedVariableMap =
    renamings.hasVariableMap ? renamings.variableMap.sexpr : "(subst)";
  const std::string renderedProgram =
    renamings.hasProgram
      ? " (program " + MegalodonKernelSyntax::renderEnnfTrace(renamings.program) + ")"
      : "";
  if (renamings.hasProgram) {
    step.fields.push_back({
      "transport_program",
      MegalodonKernelSyntax::renderEnnfTrace(renamings.program),
    });
  }
  step.rendered =
    "(rectify_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + "))"
    + " (free_variable_map " + renderedVariableMap + ")"
    + renderedRenamings
    + renderedProgram
    + " (result (formula " + result.sexpr + "))"
    + " (builder \"typed_v2\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep cnfLiteralStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  return primitiveClauseStep(
    "cnf_literal",
    id,
    {parent.value},
    result.sexpr,
    {},
    "(cnf_literal " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep formulaCopyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelLiteral& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "formula_copy";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.fields = {{"result_literal", result.sexpr}};
  step.rendered =
    "(formula_copy " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (result " + result.sexpr + "))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep formulaTermCopyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "formula_term_copy";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {{"result_formula", result.sexpr}};
  step.rendered =
    "(formula_term_copy " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (result (formula " + result.sexpr + ")))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep ennfFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const MegalodonKernelSyntax::RenderedKernelEnnfTrace& trace,
  const MegalodonKernelSyntax::RenderedKernelFormula& result)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  const std::string renderedTrace =
    MegalodonKernelSyntax::renderEnnfTrace(trace);
  step.rule = "ennf_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {
    {"source_formula", source.sexpr},
    {"ennf_trace", renderedTrace},
    {"selection_source", "nnf_v1"},
    {"primitive_lowering_source", "nnf_v1"},
  };
  step.rendered =
    "(ennf_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + "))"
    + " (trace " + renderedTrace + ")"
    + " (result (formula " + result.sexpr + "))"
    + " (builder \"typed_v1\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep skolemFormulaStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  const std::vector<MegalodonKernelSyntax::RenderedKernelScopedSkolemBranch>& branches,
  const MegalodonKernelSyntax::RenderedKernelFormula& result,
  const std::string& producerProof)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "skolem_formula";
  step.id = id;
  step.builderOwned = true;
  step.parentIds = {parent.value};
  step.hasResultFormula = true;
  step.resultFormula = result.sexpr;
  step.fields = {
    {"source_formula", source.sexpr},
    {"branch_count", std::to_string(branches.size())},
    {"path_encoding", "binary_kernel_term_v1"},
    {"selection_source", "skolem_v1"},
    {"primitive_lowering_source", "skolem_v1"},
  };

  std::string renderedBranches = "(branches";
  for (const auto& branch : branches) {
    const std::string prefix = "branch_" + std::to_string(branch.index);
    step.fields.push_back({prefix + "_source", branch.source.sexpr});
    step.fields.push_back({prefix + "_target", branch.target.sexpr});
    std::string renderedPath = "(path";
    for (std::size_t child : branch.path) {
      renderedPath += " " + std::to_string(child);
    }
    renderedPath += ")";
    step.fields.push_back({prefix + "_path", renderedPath});
    step.fields.push_back({prefix + "_normalization", branch.normalization});
    std::string renderedContextProgram = "(context_program";
    for (const std::string& frame : branch.contextProgram) {
      renderedContextProgram += " (" + frame + ")";
    }
    renderedContextProgram += ")";
    step.fields.push_back({
      prefix + "_context_program",
      renderedContextProgram,
    });
    step.fields.push_back({
      prefix + "_context_count",
      std::to_string(branch.context.size()),
    });
    step.fields.push_back({
      prefix + "_witness_count",
      std::to_string(branch.witnesses.size()),
    });
    step.fields.push_back({
      prefix + "_context_stage_count",
      std::to_string(branch.contextStages.size()),
    });

    renderedBranches +=
      " (branch (index " + std::to_string(branch.index) + ")"
      + " " + renderedPath
      + " (normalization " + quote(branch.normalization) + ")"
      + " " + renderedContextProgram
      + " (source (formula " + branch.source.sexpr + "))"
      + " (ambient";
    for (const auto& variable : branch.ambient) {
      renderedBranches +=
        " (variable " + quote(variable.variable) + " " + variable.type.sexpr + ")";
    }
    renderedBranches += ")";
    renderedBranches += " (context";
    for (const auto& variable : branch.context) {
      renderedBranches +=
        " (variable " + quote(variable.variable) + " " + variable.type.sexpr + ")";
    }
    renderedBranches += ") (witnesses";
    for (std::size_t witnessIndex = 0;
         witnessIndex < branch.witnesses.size();
         ++witnessIndex) {
      const auto& witness = branch.witnesses[witnessIndex];
      step.certificateLocalSymbols.push_back(witness.symbol);
      step.certificateLocalSymbolDependencyCounts.push_back(
        witness.dependencies.size());
      const std::string witnessPrefix =
        prefix + "_witness_" + std::to_string(witnessIndex);
      step.fields.push_back({witnessPrefix + "_symbol", witness.symbol});
      step.fields.push_back({
        witnessPrefix + "_replaced_variable",
        witness.replacedVariable,
      });
      step.fields.push_back({witnessPrefix + "_sort", witness.replacedSort.sexpr});
      step.fields.push_back({witnessPrefix + "_term", witness.witnessTerm.sexpr});
      step.fields.push_back({
        witnessPrefix + "_stage_source",
        witness.stageSource.sexpr,
      });
      step.fields.push_back({
        witnessPrefix + "_raw_choice_target",
        witness.rawChoiceTarget.sexpr,
      });
      step.fields.push_back({
        witnessPrefix + "_stage_target",
        witness.stageTarget.sexpr,
      });
      step.fields.push_back({
        witnessPrefix + "_dependency_count",
        std::to_string(witness.dependencies.size()),
      });

      renderedBranches +=
        " (witness (index " + std::to_string(witnessIndex) + ")"
        + " (kind " + quote(witness.typeVariable ? "type" : "term") + ")"
        + " (symbol " + quote(witness.symbol) + ")"
        + " (replaced_variable " + quote(witness.replacedVariable) + ")"
        + " (sort " + witness.replacedSort.sexpr + ")"
        + " (term " + witness.witnessTerm.sexpr + ")"
        + " (dependencies";
      for (const auto& dependency : witness.dependencies) {
        renderedBranches +=
          " (variable " + quote(dependency.variable) + " "
          + dependency.type.sexpr + ")";
      }
      renderedBranches += ") (program"
        " (stage_source (formula " + witness.stageSource.sexpr + "))"
        " (choice (raw_target (formula "
        + witness.rawChoiceTarget.sexpr + ")))"
        " (normalization";
      if (!witness.hasTransportProgram) {
        for (const auto& path : witness.equalitySymmetryPaths) {
          renderedBranches += " (equality_symmetry (path";
          for (std::size_t child : path) {
            renderedBranches += " " + std::to_string(child);
          }
          renderedBranches += "))";
        }
      }
      renderedBranches += ")";
      if (witness.hasTransportProgram) {
        renderedBranches += " (transport "
          + MegalodonKernelSyntax::renderEnnfTrace(witness.transportProgram)
          + ")";
      }
      renderedBranches += " (stage_target (formula "
        + witness.stageTarget.sexpr + "))))";
    }
    renderedBranches += ") (context_stages";
    for (const auto& stage : branch.contextStages) {
      const std::string stagePrefix =
        prefix + "_context_stage_" + std::to_string(stage.index);
      step.fields.push_back({stagePrefix + "_primitive", stage.primitive});
      step.fields.push_back({stagePrefix + "_source", stage.source.sexpr});
      step.fields.push_back({stagePrefix + "_target", stage.target.sexpr});
      renderedBranches +=
        " (stage (index " + std::to_string(stage.index) + ")"
        + " (primitive " + quote(stage.primitive) + ")"
        + " (source (formula " + stage.source.sexpr + "))"
        + " (target (formula " + stage.target.sexpr + "))"
        + " (context";
      for (const auto& variable : stage.context) {
        renderedBranches +=
          " (variable " + quote(variable.variable) + " "
          + variable.type.sexpr + ")";
      }
      renderedBranches += "))";
    }
    renderedBranches +=
      ") (target (formula " + branch.target.sexpr + ")))";
  }
  renderedBranches += ")";
  if (producerProof.empty()) {
    return MegalodonKernelSyntax::PrimitiveStep();
  }
  step.rendered =
    "(skolem_formula " + quote(id)
    + " (parent " + quote(parent.value) + ")"
    + " (source (formula " + source.sexpr + ")) "
    + renderedBranches
    + " (producer_proof (program \"ivy_nd_v1\" (proof "
    + producerProof + ")))"
    + " (result (formula " + result.sexpr + "))"
    + " (builder \"typed_v5\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep cnfFormulaClauseStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelFormula& source,
  std::size_t index,
  std::size_t count,
  const MegalodonKernelSyntax::RenderedKernelCnfProjection& projection,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::string& producerProof)
{
  const std::string renderedProjection =
    MegalodonKernelSyntax::renderCnfProjection(projection);
  MegalodonKernelSyntax::PrimitiveStep step = primitiveClauseStep(
    "cnf_formula_clause",
    id,
    {parent.value},
    result.sexpr,
    {
      {"source_formula", source.sexpr},
      {"clause_index", std::to_string(index)},
      {"clause_count", std::to_string(count)},
      {"cnf_projection", renderedProjection},
    },
    "(cnf_formula_clause " + quote(id)
      + " (parent " + quote(parent.value) + ")"
      + " (source (formula " + source.sexpr + "))"
      + " (index " + std::to_string(index) + ")"
      + " (count " + std::to_string(count) + ")"
      + " (projection " + renderedProjection + ")"
      + " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + ")))"
      + " (result " + result.sexpr + ")"
      + " (builder \"typed_v3\"))");
  step.producerProof = producerProof;
  return step;
}

MegalodonKernelSyntax::PrimitiveStep predicateDefinitionStep(
  const std::string& id,
  const std::string& symbol,
  const MegalodonKernelSyntax::RenderedKernelPredicateDefinition& definition)
{
  MegalodonKernelSyntax::PrimitiveStep step;
  step.rule = "predicate_definition_intro";
  step.id = id;
  step.builderOwned = true;
  step.hasResultFormula = true;
  step.resultFormula = definition.resultFormula.sexpr;

  std::string binders = "(binders";
  for (const auto& binder : definition.binders) {
    binders += " (variable (index " + std::to_string(binder.index) + ")"
      + " (name " + quote(binder.variable) + ")"
      + " (type " + binder.type.sexpr + "))";
  }
  binders += ")";
  const std::string program =
    "(program \"ivy_predicate_definition_v1\" " + binders
    + " (body (formula " + definition.bodyFormula.sexpr + "))"
    + " (definiendum (formula " + definition.definiendumFormula.sexpr + "))"
    + " (negative (formula " + definition.negativeFormula.sexpr + "))"
    + " (target (formula " + definition.targetFormula.sexpr + "))"
    + " (body_side \"" + definition.bodySide + "\")"
    + " (definiendum_elimination \"" + definition.definiendumElimination + "\")"
    + " (steps"
      " (step (index 0) (rule \"or_intro_right\") (premise \"body\") (result \"target\"))"
      " (step (index 1) (rule \"not_body_to_negated_definiendum\") (premise \"not_body\") (result \"negative\"))"
      " (step (index 2) (rule \"or_intro_left\") (premise \"negative\") (result \"target\"))"
      " (step (index 3) (rule \"excluded_middle\") (premises \"body_branch\" \"negative_branch\") (result \"target\")))"
    + ")";
  step.fields = {
    {"predicate_definition_program", program},
    {"body_formula", definition.bodyFormula.sexpr},
    {"definiendum_formula", definition.definiendumFormula.sexpr},
    {"negative_formula", definition.negativeFormula.sexpr},
    {"target_formula", definition.targetFormula.sexpr},
  };
  step.rendered =
    "(predicate_definition " + quote(id)
    + " (symbol " + quote(symbol) + ")"
    + " (result (formula " + definition.resultFormula.sexpr + ")) "
    + program + " (builder \"typed_v2\"))";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep avatarComponentStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& definitions,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::string& producerProof)
{
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  for (const auto& definition : definitions) {
    parentIds.push_back(definition.value);
    renderedParents += " " + quote(definition.value);
  }
  renderedParents += ")";
  return primitiveClauseStep(
    "avatar_component",
    id,
    parentIds,
    result.sexpr,
    {
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_component " + quote(id) + " " + renderedParents
      + " (result " + result.sexpr + ")"
      + " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + "))))");
}

MegalodonKernelSyntax::PrimitiveStep avatarDefinitionStep(
  const std::string& id,
  unsigned splitVariable,
  bool splitPositive,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::string& producerProof,
  const std::string& resultProof)
{
  const std::string splitVariableText = std::to_string(splitVariable);
  const std::string splitPositiveText = splitPositive ? "true" : "false";
  return primitiveClauseStep(
    "avatar_definition",
    id,
    {},
    result.sexpr,
    {
      {"split_variable", splitVariableText},
      {"split_positive", splitPositiveText},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_definition " + quote(id)
      + " (split " + splitVariableText + " " + splitPositiveText + ")"
      + " (result " + result.sexpr + ")"
      + " (producer_proof (program \"ivy_nd_v1\" (proof "
      + producerProof + ")))"
      + " (result_proof (program \"ivy_nd_v1\" (proof "
      + resultProof + "))))");
}

MegalodonKernelSyntax::PrimitiveStep splitDependencyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& owner,
  const std::vector<MegalodonKernelSyntax::RenderedKernelSplitDependencyItem>& dependencies,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  std::string renderedDependencies = "(dependencies";
  for (const auto& dependency : dependencies) {
    if (!dependency.hasComponentClauseSexpr) {
      continue;
    }
    renderedDependencies +=
      " (dependency " + std::to_string(dependency.split.variable)
      + " " + (dependency.split.positive ? "true" : "false")
      + " (component " + dependency.componentClauseSexpr.sexpr + "))";
  }
  renderedDependencies += ")";
  return primitiveClauseStep(
    "split_dependency",
    id,
    {owner.value},
    result.sexpr,
    {
      {"dependency_count", std::to_string(dependencies.size())},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(split_dependency " + quote(id)
      + " (owner " + quote(owner.value) + ") "
      + renderedDependencies
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep avatarSplitStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& parents,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  for (const auto& parent : parents) {
    parentIds.push_back(parent.value);
    renderedParents += " " + quote(parent.value);
  }
  renderedParents += ")";
  return primitiveClauseStep(
    "avatar_split",
    id,
    parentIds,
    result.sexpr,
    {
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_split " + quote(id) + " " + renderedParents
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep avatarSplitIvyStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& parents,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const MegalodonKernelSyntax::RenderedKernelAvatarSplitStep& split)
{
  MegalodonKernelSyntax::PrimitiveStep step =
    avatarSplitStep(id, parents, result);
  if (!split.hasIvyProgram || !split.hasSourceClause
      || (!split.hasResultFormula && !split.hasResultClause)) {
    return step;
  }
  std::string directProof;
  std::string expansionError;
  if (!MegalodonProofExpander::expandAvatarSplitProof(
        split, directProof, expansionError)) {
    return step;
  }

  std::string program =
    "(program \"ivy_avatar_split_v1\""
    " (source " + split.sourceClause.sexpr + ")";
  if (split.hasResultFormula) {
    program += " (target (formula " + split.resultFormula.sexpr + "))";
  } else {
    program += " (target " + split.resultClause.sexpr + ")";
  }

  program += " (cases";
  for (const auto& item : split.cases) {
    program +=
      " (case (index " + std::to_string(item.index)
      + ") (split " + std::to_string(item.splitVar) + " "
      + (item.positive ? "true" : "false")
      + ") (path " + quote(item.path) + ") (formula "
      + item.formula.sexpr + "))";
  }
  program += ")";

  program += " (components";
  for (const auto& parent : split.componentParents) {
    if (!parent.hasClauseSexpr) {
      return step;
    }
    program +=
      " (component (index " + std::to_string(parent.refIndex)
      + ") (parent " + quote(parent.unit.value)
      + ") (split " + std::to_string(parent.split.variable) + " "
      + (parent.split.positive ? "true" : "false")
      + ") (body " + parent.clauseSexpr.sexpr + "))";
  }
  program += ")";

  program += " (classes";
  for (const auto& literalClass : split.literalClasses) {
    if (!literalClass.hasMatchedSplitVar
        || literalClass.parentLiteralIndices.size()
             != literalClass.literalCount) {
      return step;
    }
    program +=
      " (class (index " + std::to_string(literalClass.index)
      + ") (split " + std::to_string(literalClass.matchedSplitVar)
      + ") (positive " + (literalClass.positive ? "true" : "false")
      + ") (source_literals";
    for (std::size_t literal : literalClass.parentLiteralIndices) {
      program += " " + std::to_string(literal);
    }
    program += "))";
  }
  program += ")";

  program += " (bindings";
  for (const auto& binding : split.parentVarBindings) {
    if (!binding.hasType || !binding.hasComponentVar
        || !binding.hasSplitVar) {
      return step;
    }
    program +=
      " (binding (index " + std::to_string(binding.index)
      + ") (parent_var " + quote(binding.parentVar)
      + ") (type " + binding.type.sexpr
      + ") (component_var " + quote(binding.componentVar)
      + ") (split " + std::to_string(binding.splitVar) + ")";
    if (binding.hasCounterexampleProgram) {
      program +=
        " (witness (program "
        + std::to_string(binding.counterexampleProgram)
        + ") (stage " + std::to_string(binding.counterexampleStage) + "))";
    }
    program += ")";
  }
  program += ")";

  program += " (counterexamples";
  for (const auto& counterexample : split.counterexamplePrograms) {
    program +=
      " (counterexample (index " + std::to_string(counterexample.index)
      + ") (split " + std::to_string(counterexample.splitVar)
      + ") (source (formula " + counterexample.source.sexpr
      + ")) (body (formula " + counterexample.body.sexpr
      + ")) (stages";
    for (const auto& stage : counterexample.stages) {
      program +=
        " (stage (index " + std::to_string(stage.index)
        + ") (variable " + quote(stage.variable)
        + ") (type " + stage.type.sexpr
        + ") (source (formula " + stage.source.sexpr
        + ")) (predicate (formula " + stage.predicate.sexpr
        + ")) (witness (term " + stage.witness.sexpr
        + ")) (target (formula " + stage.target.sexpr + ")))";
    }
    program +=
      ") (final_body (formula " + counterexample.finalBody.sexpr + ")))";
  }
  program += ")";

  if (split.hasFocus) {
    program +=
      " (focus (split " + std::to_string(split.focusSplitVar)
      + ") (class " + std::to_string(split.focusLiteralClass)
      + ") (component " + std::to_string(split.focusComponentParent) + "))";
  } else {
    program += " (terminal \"contradiction\")";
  }

  program += " (source_nodes";
  for (const auto& node : split.sourceNodes) {
    program +=
      " (node (index " + std::to_string(node.index)
      + ") (literal " + std::to_string(node.literal) + ")";
    switch (node.action) {
      case MegalodonKernelSyntax::RenderedKernelAvatarSplitSourceAction::Focus:
        program +=
          " (action \"focus\") (class "
          + std::to_string(node.literalClass)
          + ") (component_literal "
          + std::to_string(node.componentLiteral) + ")";
        break;
      case MegalodonKernelSyntax::RenderedKernelAvatarSplitSourceAction::Counterexample:
        program +=
          " (action \"counterexample\") (class "
          + std::to_string(node.literalClass)
          + ") (component_literal "
          + std::to_string(node.componentLiteral)
          + ") (split " + std::to_string(node.splitVar) + ")";
        break;
      case MegalodonKernelSyntax::RenderedKernelAvatarSplitSourceAction::PreviousSplit:
        program +=
          " (action \"previous_split\") (case "
          + std::to_string(node.caseIndex) + ")";
        break;
    }
    program += ")";
  }
  program += ") (producer_proof (program \"ivy_nd_v1\" (proof "
    + directProof + "))))";

  step.rendered.pop_back();
  step.rendered += " " + program + ")";
  return step;
}

MegalodonKernelSyntax::PrimitiveStep avatarContradictionStep(
  const std::string& id,
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef>& parents,
  const MegalodonKernelSyntax::RenderedKernelClause& result)
{
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  for (const auto& parent : parents) {
    parentIds.push_back(parent.value);
    renderedParents += " " + quote(parent.value);
  }
  renderedParents += ")";
  return primitiveClauseStep(
    "avatar_contradiction",
    id,
    parentIds,
    result.sexpr,
    {
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_contradiction " + quote(id) + " " + renderedParents
      + " (result " + result.sexpr + "))");
}

MegalodonKernelSyntax::PrimitiveStep avatarContradictionIvyStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelUnitRef& parent,
  const MegalodonKernelSyntax::RenderedKernelClause& result,
  const std::vector<std::string>& sourceLiterals,
  const std::vector<std::string>& resultLiterals,
  const std::vector<std::string>& parentArguments)
{
  const std::vector<MegalodonKernelSyntax::RenderedKernelUnitRef> parents{parent};
  MegalodonProofExpander::AvatarContradictionProofRequest request;
  request.parentId = parent.value;
  request.parentArguments = parentArguments;
  request.sourceLiterals = sourceLiterals;
  request.resultLiterals = resultLiterals;
  std::string directProof;
  std::string expansionError;
  if (!MegalodonProofExpander::expandAvatarContradictionProof(
        request, directProof, expansionError)) {
    return avatarContradictionStep(id, parents, result);
  }
  std::string sourceClause = "(clause";
  for (const std::string& literal : sourceLiterals) {
    sourceClause += " " + literal;
  }
  sourceClause += ")";

  std::string program =
    "(program \"ivy_avatar_contradiction_v1\" (source "
    + sourceClause + ") (nodes";
  for (std::size_t offset = 0; offset < sourceLiterals.size(); ++offset) {
    const std::size_t sourceIndex = sourceLiterals.size() - offset - 1;
    program += " (node (index " + std::to_string(offset)
      + ") (literal " + std::to_string(sourceIndex) + ") (action \""
      + (offset == 0 ? "start" : "or") + "\"))";
  }
  program +=
    ") (producer_proof (program \"ivy_nd_v1\" (proof "
    + directProof + "))))";

  MegalodonKernelSyntax::PrimitiveStep step =
    avatarContradictionStep(id, parents, result);
  step.rendered.pop_back();
  step.rendered += " " + program + ")";
  return step;
}

namespace {

using SatLiteral = MegalodonKernelSyntax::RenderedKernelSatLiteral;
using SatClause = std::vector<SatLiteral>;

enum class ExactSatOperationKind {
  Resolve,
  Factor,
  Permute,
};

struct ExactSatOperation {
  ExactSatOperationKind kind = ExactSatOperationKind::Permute;
  unsigned rightParent = 0;
  std::size_t leftIndex = 0;
  std::size_t rightIndex = 0;
  SatClause result;
};

std::string renderSatClause(const SatClause& clause)
{
  std::string rendered = "(sat_clause";
  for (const SatLiteral& literal : clause) {
    rendered +=
      " (lit " + std::to_string(literal.variable)
      + " " + (literal.positive ? "true" : "false") + ")";
  }
  return rendered + ")";
}

std::vector<std::string> renderSatClauseLiterals(const SatClause& clause)
{
  std::vector<std::string> result;
  result.reserve(clause.size());
  for (const SatLiteral& literal : clause) {
    result.push_back(
      std::string(literal.positive ? "(pos " : "(neg ")
      + "(TMH \"split_" + std::to_string(literal.variable) + "\"))");
  }
  return result;
}

std::string satProofNodeId(unsigned id)
{
  return "sat_" + std::to_string(id);
}

bool satLiteralLess(const SatLiteral& left, const SatLiteral& right)
{
  if (left.variable != right.variable) {
    return left.variable < right.variable;
  }
  return left.positive < right.positive;
}

bool sameSatClauseMultiset(SatClause left, SatClause right)
{
  std::sort(left.begin(), left.end(), satLiteralLess);
  std::sort(right.begin(), right.end(), satLiteralLess);
  return left == right;
}

bool exactSatPermutation(
  const SatClause& source,
  const SatClause& target,
  std::vector<std::size_t>& permutation)
{
  if (source.size() != target.size()) {
    return false;
  }
  std::vector<bool> used(source.size(), false);
  permutation.clear();
  permutation.reserve(target.size());
  for (const SatLiteral& literal : target) {
    std::size_t sourceIndex = 0;
    while (sourceIndex < source.size()
           && (used[sourceIndex] || source[sourceIndex] != literal)) {
      ++sourceIndex;
    }
    if (sourceIndex == source.size()) {
      permutation.clear();
      return false;
    }
    used[sourceIndex] = true;
    permutation.push_back(sourceIndex);
  }
  return true;
}

std::string renderSatPermutation(const std::vector<std::size_t>& permutation)
{
  std::string rendered = "(permutation";
  for (std::size_t index : permutation) {
    rendered += " " + std::to_string(index);
  }
  return rendered + ")";
}

bool complementarySatLiterals(const SatLiteral& left, const SatLiteral& right)
{
  return left.variable == right.variable && left.positive != right.positive;
}

SatClause removeSatLiteral(const SatClause& clause, std::size_t index)
{
  SatClause result;
  result.reserve(clause.size() - 1);
  for (std::size_t current = 0; current < clause.size(); ++current) {
    if (current != index) {
      result.push_back(clause[current]);
    }
  }
  return result;
}

void factorSatClause(SatClause& clause, std::vector<ExactSatOperation>& operations)
{
  while (true) {
    bool found = false;
    for (std::size_t left = 0; left < clause.size() && !found; ++left) {
      for (std::size_t right = left + 1; right < clause.size(); ++right) {
        if (clause[left] != clause[right]) {
          continue;
        }
        clause = removeSatLiteral(clause, right);
        ExactSatOperation operation;
        operation.kind = ExactSatOperationKind::Factor;
        operation.leftIndex = left;
        operation.rightIndex = right;
        operation.result = clause;
        operations.push_back(std::move(operation));
        found = true;
        break;
      }
    }
    if (!found) {
      return;
    }
  }
}

bool lowerOrderedSatResolution(
  const SatClause& current,
  const std::vector<std::pair<unsigned, SatClause>>& parents,
  std::size_t parentIndex,
  const SatClause& target,
  std::vector<ExactSatOperation>& operations)
{
  if (parentIndex == parents.size()) {
    return sameSatClauseMultiset(current, target);
  }
  const auto& [rightParent, rightClause] = parents[parentIndex];
  for (std::size_t leftIndex = 0; leftIndex < current.size(); ++leftIndex) {
    for (std::size_t rightIndex = 0; rightIndex < rightClause.size(); ++rightIndex) {
      if (!complementarySatLiterals(current[leftIndex], rightClause[rightIndex])) {
        continue;
      }
      const std::size_t checkpoint = operations.size();
      SatClause next = removeSatLiteral(current, leftIndex);
      SatClause rightRest = removeSatLiteral(rightClause, rightIndex);
      next.insert(next.end(), rightRest.begin(), rightRest.end());
      ExactSatOperation operation;
      operation.kind = ExactSatOperationKind::Resolve;
      operation.rightParent = rightParent;
      operation.leftIndex = leftIndex;
      operation.rightIndex = rightIndex;
      operation.result = next;
      operations.push_back(std::move(operation));
      factorSatClause(next, operations);
      if (lowerOrderedSatResolution(
            next, parents, parentIndex + 1, target, operations)) {
        return true;
      }
      operations.resize(checkpoint);
    }
  }
  return false;
}

bool lowerAvatarSatProof(
  const std::vector<MegalodonKernelSyntax::RenderedKernelSatProofStep>& sourceSteps,
  std::string& rendered,
  std::string& renderedProofs,
  std::size_t& exactStepCount,
  std::size_t& rupStepCount)
{
  unsigned maximumSourceId = 0;
  for (const auto& step : sourceSteps) {
    maximumSourceId = std::max(maximumSourceId, step.id);
  }
  if (maximumSourceId == std::numeric_limits<unsigned>::max()) {
    return false;
  }
  unsigned nextSyntheticId = maximumSourceId + 1;
  std::map<unsigned, SatClause> checked;
  rendered = "(sat_proof";
  renderedProofs = "(producer_proofs";
  auto appendProof = [&](unsigned id, const std::string& proof) {
    renderedProofs +=
      " (node " + std::to_string(id)
      + " (program \"ivy_nd_v1\" (proof " + proof + ")))";
  };
  exactStepCount = 0;
  rupStepCount = 0;
  for (const auto& step : sourceSteps) {
    if (step.id == 0 || checked.find(step.id) != checked.end()) {
      return false;
    }
    if (step.kind == "input") {
      if (!step.hasOriginUnit || !step.hasOriginLiterals
          || !sameSatClauseMultiset(step.originLiterals, step.literals)) {
        return false;
      }
      if (step.originLiterals == step.literals) {
        checked.emplace(step.id, step.literals);
        rendered +=
          " (sat_input " + std::to_string(step.id)
          + " (origin " + quote(step.originUnit.value) + ")"
          + " " + renderSatClause(step.literals) + ")";
        std::string proof;
        std::string error;
        if (!MegalodonProofExpander::expandAvatarSatProjectionProof(
              step.originUnit.value,
              renderSatClauseLiterals(step.originLiterals),
              renderSatClauseLiterals(step.literals),
              proof,
              error)) {
          return false;
        }
        appendProof(step.id, proof);
        ++exactStepCount;
      } else {
        if (nextSyntheticId == std::numeric_limits<unsigned>::max()) {
          return false;
        }
        const unsigned originInputId = nextSyntheticId++;
        checked.emplace(originInputId, step.originLiterals);
        std::vector<std::size_t> permutation;
        if (!exactSatPermutation(
              step.originLiterals, step.literals, permutation)) {
          return false;
        }
        rendered +=
          " (sat_input " + std::to_string(originInputId)
          + " (origin " + quote(step.originUnit.value) + ")"
          + " " + renderSatClause(step.originLiterals) + ")";
        std::string originProof;
        std::string originError;
        if (!MegalodonProofExpander::expandAvatarSatProjectionProof(
              step.originUnit.value,
              renderSatClauseLiterals(step.originLiterals),
              renderSatClauseLiterals(step.originLiterals),
              originProof,
              originError)) {
          return false;
        }
        appendProof(originInputId, originProof);
        rendered +=
          " (sat_permute " + std::to_string(step.id)
          + " (parent " + std::to_string(originInputId) + ")"
          + " " + renderSatPermutation(permutation)
          + " (result " + renderSatClause(step.literals) + "))";
        std::string permutationProof;
        std::string permutationError;
        if (!MegalodonProofExpander::expandAvatarSatProjectionProof(
              satProofNodeId(originInputId),
              renderSatClauseLiterals(step.originLiterals),
              renderSatClauseLiterals(step.literals),
              permutationProof,
              permutationError)) {
          return false;
        }
        appendProof(step.id, permutationProof);
        checked.emplace(step.id, step.literals);
        exactStepCount += 2;
      }
      continue;
    }
    if (step.kind != "rup" || step.parents.empty()) {
      return false;
    }
    ++rupStepCount;
    std::vector<std::pair<unsigned, SatClause>> parents;
    for (const auto& parent : step.parents) {
      const auto found = checked.find(parent.id);
      if (found == checked.end()) {
        return false;
      }
      parents.emplace_back(parent.id, found->second);
    }
    SatClause initial = parents.front().second;
    std::vector<ExactSatOperation> operations;
    factorSatClause(initial, operations);
    if (!lowerOrderedSatResolution(
          initial, parents, 1, step.literals, operations)) {
      return false;
    }
    const SatClause finalClause = operations.empty() ? initial : operations.back().result;
    if (operations.empty() || finalClause != step.literals) {
      ExactSatOperation permutation;
      permutation.kind = ExactSatOperationKind::Permute;
      permutation.result = step.literals;
      operations.push_back(std::move(permutation));
    }
    unsigned currentId = parents.front().first;
    for (std::size_t index = 0; index < operations.size(); ++index) {
      const ExactSatOperation& operation = operations[index];
      const bool finalOperation = index + 1 == operations.size();
      if (!finalOperation && nextSyntheticId == 0) {
        return false;
      }
      const unsigned operationId =
        finalOperation ? step.id : nextSyntheticId++;
      const auto current = checked.find(currentId);
      if (current == checked.end()) {
        return false;
      }
      std::string directProof;
      std::string directProofError;
      switch (operation.kind) {
        case ExactSatOperationKind::Resolve:
          rendered +=
            " (sat_resolve " + std::to_string(operationId)
            + " (left " + std::to_string(currentId)
            + " " + std::to_string(operation.leftIndex) + ")"
            + " (right " + std::to_string(operation.rightParent)
            + " " + std::to_string(operation.rightIndex) + ")"
            + " (result " + renderSatClause(operation.result) + "))";
          {
            const auto right = checked.find(operation.rightParent);
            if (right == checked.end()
                || !MegalodonProofExpander::expandAvatarSatResolutionProof(
                     satProofNodeId(currentId),
                     renderSatClauseLiterals(current->second),
                     operation.leftIndex,
                     satProofNodeId(operation.rightParent),
                     renderSatClauseLiterals(right->second),
                     operation.rightIndex,
                     renderSatClauseLiterals(operation.result),
                     directProof,
                     directProofError)) {
              return false;
            }
          }
          break;
        case ExactSatOperationKind::Factor:
          rendered +=
            " (sat_factor " + std::to_string(operationId)
            + " (parent " + std::to_string(currentId) + ")"
            + " (literals " + std::to_string(operation.leftIndex)
            + " " + std::to_string(operation.rightIndex) + ")"
            + " (result " + renderSatClause(operation.result) + "))";
          if (!MegalodonProofExpander::expandAvatarSatProjectionProof(
                satProofNodeId(currentId),
                renderSatClauseLiterals(current->second),
                renderSatClauseLiterals(operation.result),
                directProof,
                directProofError)) {
            return false;
          }
          break;
        case ExactSatOperationKind::Permute:
          {
          std::vector<std::size_t> permutation;
          if (!exactSatPermutation(
                current->second, operation.result, permutation)) {
            return false;
          }
          rendered +=
            " (sat_permute " + std::to_string(operationId)
            + " (parent " + std::to_string(currentId) + ")"
            + " " + renderSatPermutation(permutation)
            + " (result " + renderSatClause(operation.result) + "))";
          if (!MegalodonProofExpander::expandAvatarSatProjectionProof(
                satProofNodeId(currentId),
                renderSatClauseLiterals(current->second),
                renderSatClauseLiterals(operation.result),
                directProof,
                directProofError)) {
            return false;
          }
          break;
          }
      }
      appendProof(operationId, directProof);
      checked.emplace(operationId, operation.result);
      currentId = operationId;
      ++exactStepCount;
    }
    if (checked.find(step.id) == checked.end()) {
      checked.emplace(step.id, step.literals);
    }
  }
  rendered += ")";
  renderedProofs += ")";
  return !sourceSteps.empty();
}

}

bool collectAvatarSatProof(
  SAT::SATClause* root,
  MegalodonKernelSyntax::RenderedKernelAvatarRefutation* refutation)
{
  if (root == nullptr || refutation == nullptr) {
    return false;
  }
  struct CompareSATClauses {
    bool operator()(SAT::SATClause* left, SAT::SATClause* right) const
    {
      return left->number < right->number;
    }
  };
  std::set<SAT::SATClause*, CompareSATClauses> proof;
  std::vector<SAT::SATClause*> todo{root};
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
    auto* prop = static_cast<SAT::PropInference*>(inference);
    for (SAT::SATClause* parent : Lib::iterTraits(prop->getPremises()->iter())) {
      todo.push_back(parent);
    }
  }

  refutation->inputs.clear();
  refutation->proofSteps.clear();
  refutation->hasSatRefutationClause = true;
  refutation->satRefutationClause =
    MegalodonKernelSyntax::clause(renderSatClause(
      [&]() {
        SatClause literals;
        for (SAT::SATLiteral literal : root->iter()) {
          literals.push_back({literal.var(), literal.positive()});
        }
        return literals;
      }()));
  std::size_t proofIndex = 0;
  std::size_t inputIndex = 0;
  for (SAT::SATClause* clause : proof) {
    MegalodonKernelSyntax::RenderedKernelSatProofStep step;
    step.index = proofIndex++;
    step.id = clause->number;
    for (SAT::SATLiteral literal : clause->iter()) {
      step.literals.push_back({literal.var(), literal.positive()});
    }
    step.hasClause = true;
    step.clause = MegalodonKernelSyntax::clause(renderSatClause(step.literals));
    SAT::SATInference* inference = clause->inference();
    if (inference == nullptr) {
      return false;
    }
    if (inference->getType() == SAT::SATInference::FO_CONVERSION) {
      Kernel::Unit* origin = inference->foConversion()->getOrigin();
      if (origin == nullptr) {
        return false;
      }
      step.kind = "input";
      step.hasOriginUnit = true;
      step.originUnit =
        MegalodonKernelSyntax::unitRef("u" + std::to_string(origin->number()));
      MegalodonKernelSyntax::RenderedKernelSatInput input;
      input.index = inputIndex++;
      input.hasClause = true;
      input.clause = step.clause;
      input.hasOriginUnit = true;
      input.originUnit = step.originUnit;
      refutation->inputs.push_back(std::move(input));
    } else if (inference->getType() == SAT::SATInference::PROP_INF) {
      step.kind = "rup";
      auto* prop = static_cast<SAT::PropInference*>(inference);
      std::size_t parentIndex = 0;
      for (SAT::SATClause* parent : Lib::iterTraits(prop->getPremises()->iter())) {
        MegalodonKernelSyntax::RenderedKernelSatProofParent renderedParent;
        renderedParent.index = parentIndex++;
        renderedParent.id = parent->number;
        SatClause parentLiterals;
        for (SAT::SATLiteral literal : parent->iter()) {
          parentLiterals.push_back({literal.var(), literal.positive()});
        }
        renderedParent.hasClause = true;
        renderedParent.clause =
          MegalodonKernelSyntax::clause(renderSatClause(parentLiterals));
        step.parents.push_back(std::move(renderedParent));
      }
    } else {
      return false;
    }
    refutation->proofSteps.push_back(std::move(step));
  }
  return true;
}

bool avatarRefutationStep(
  const std::string& id,
  const MegalodonKernelSyntax::RenderedKernelAvatarRefutation& refutation,
  MegalodonKernelSyntax::PrimitiveStep* result)
{
  if (result == nullptr || !refutation.hasResultClause) {
    return false;
  }
  std::string satProof;
  std::string producerProofs;
  std::size_t exactStepCount = 0;
  std::size_t rupStepCount = 0;
  if (!lowerAvatarSatProof(
        refutation.proofSteps,
        satProof,
        producerProofs,
        exactStepCount,
        rupStepCount)) {
    return false;
  }
  std::vector<std::string> parentIds;
  std::string renderedParents = "(parents";
  std::string renderedSatClauses = "(sat_clauses";
  for (const auto& input : refutation.inputs) {
    if (!input.hasOriginUnit || !input.hasClause) {
      return false;
    }
    parentIds.push_back(input.originUnit.value);
    renderedParents += " " + quote(input.originUnit.value);
    renderedSatClauses += " " + input.clause.sexpr;
  }
  renderedParents += ")";
  renderedSatClauses += ")";
  *result = primitiveClauseStep(
    "avatar_refutation",
    id,
    parentIds,
    refutation.resultClause.sexpr,
    {
      {"sat_input_count", std::to_string(refutation.inputs.size())},
      {"sat_proof_format", "resolution_v1"},
      {"sat_lowering_source", "rup_resolution_v1"},
      {"sat_proof_step_count", std::to_string(exactStepCount)},
      {"sat_rup_source_step_count", std::to_string(rupStepCount)},
      {"selection_source", "avatar_v1"},
      {"scope", "certificate_local_block_v1"},
      {"primitive_lowering_source", "avatar_v1"},
    },
    "(avatar_refutation " + quote(id) + " " + renderedParents
      + " " + renderedSatClauses + " " + satProof
      + " " + producerProofs
      + " (result " + refutation.resultClause.sexpr + "))");
  return true;
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
