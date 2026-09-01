/*
 * This file is part of the source code of the software program
 * Vampire. It is protected by applicable copyright laws.
 *
 * This source code is distributed under the licence found here
 * https://vprover.github.io/license.html
 * and in the source directory
 */

#include "Shell/MegalodonChecker/MegalodonProofExpander.hpp"
#include "Shell/MegalodonChecker/MegalodonKernelBuilder.hpp"
#include "Kernel/EqHelper.hpp"
#include "Test/HOLUtils.hpp"
#include "Test/UnitTesting.hpp"

#include <algorithm>
#include <string>
#include <vector>

using namespace Shell::MegalodonProofExpander;
using namespace Test::HOL;

namespace {

bool contains(const std::string& value, const std::string& needle)
{
  return value.find(needle) != std::string::npos;
}

std::size_t occurrenceCount(
  const std::string& value, const std::string& needle)
{
  std::size_t result = 0;
  std::size_t position = 0;
  while ((position = value.find(needle, position)) != std::string::npos) {
    ++result;
    position += needle.size();
  }
  return result;
}

}

TEST_FUN(boolNotFalseThenEqualitySymmetry)
{
  const std::string equality =
    "(TPAP (TMH \"5a6af35fb6d6bea477dd0f822b8e01ca0d57cc50dfd41744307bc94597fdaa4a\") (PROP))";
  const std::string falseTerm = "(TMH \"vampire_false\")";
  const std::string trueTerm = "(TMH \"vampire_true\")";
  const std::string notFalse =
    "(AP (TMH \"vNOT\") " + falseTerm + ")";
  const auto positiveEquality = [&](const std::string& left,
                                    const std::string& right) {
    return "(pos (AP (AP " + equality + " " + left + ") " + right + "))";
  };
  const std::vector<std::string> source{
    positiveEquality(falseTerm, notFalse),
    "(neg (TMH \"split_65\"))",
    "(neg (TMH \"split_67\"))",
  };
  const std::vector<std::string> rewritten{
    positiveEquality(falseTerm, trueTerm),
    source[1],
    source[2],
  };
  const std::vector<std::string> target{
    positiveEquality(trueTerm, falseTerm),
    source[1],
    source[2],
  };

  ClauseBoolSimplificationPlan plan;
  std::string error;
  ALWAYS(planClauseBoolSimplification(source, target, plan, error));
  ALWAYS(plan.selectedLiteral == 0);
  ALWAYS(plan.position == std::vector<unsigned>({1}));
  ALWAYS(plan.from == notFalse);
  ALWAYS(plan.to == trueTerm);
  ALWAYS(plan.rewrittenLiterals == rewritten);
  ALWAYS(plan.requiresEqualitySymmetry);

  std::string boolProof;
  ALWAYS(expandClauseBoolSimplificationProof(
    "u2126_split_dependency",
    {},
    source,
    0,
    {1},
    notFalse,
    trueTerm,
    rewritten,
    boolProof,
    error));
  ALWAYS(!boolProof.empty());

  std::string symmetryProof;
  ALWAYS(expandClauseEqualitySymmetryProof(
    "u2127_bool_simplify0",
    {},
    rewritten,
    0,
    target,
    symmetryProof,
    error));
  ALWAYS(!symmetryProof.empty());
}

HOL_TEST_FUN(freeDeBruijnRewriteCannotEnterLambda)
{
  const TypedTermList openBody = app(D.f, db(0));
  const TypedTermList lambda = LAM(D.srt, openBody);
  Literal* underLambda = Literal::createEquality(
    true, lambda, D.f, D.fSrt);
  Literal* atTop = Literal::createEquality(
    true, openBody, D.a, D.srt);

  ALWAYS(Kernel::EqHelper::replacementCapturesFreeDeBruijn(
    underLambda, openBody, openBody, D.a));
  ALWAYS(!Kernel::EqHelper::replacementCapturesFreeDeBruijn(
    atTop, openBody, openBody, D.a));
  ALWAYS(!Kernel::EqHelper::replacementCapturesFreeDeBruijn(
    underLambda, openBody, x(0), D.a));
}

TEST_FUN(resolutionAppliesEveryProducerParentArgument)
{
  const std::string atom = "(TMH \"p\")";
  const std::string argument = "X4294967295";
  const std::string renderedArgument = "(TMH \"" + argument + "\")";
  std::string proof;
  std::string error;
  ALWAYS(expandClauseResolutionProof(
    "left",
    {argument},
    {"(pos " + atom + ")"},
    0,
    "right",
    {argument},
    {"(neg " + atom + ")"},
    0,
    {},
    proof,
    error));
  ALWAYS(contains(
    proof,
    "(term_apply (parent \"left\") (term " + renderedArgument + "))"));
  ALWAYS(contains(
    proof,
    "(term_apply (parent \"right\") (term " + renderedArgument + "))"));
}

TEST_FUN(scopedChoiceSerializerInternsProducerContexts)
{
  using namespace Shell::MegalodonKernelSyntax;

  RenderedKernelChoiceProof proof;
  proof.version = "ivy_ground_scoped_choice_dag_v1";
  proof.finalStep = "ivy_ground_0_final";
  proof.eliminatedSymbols = {"sK0"};

  RenderedKernelIvyContextFrame frame;
  frame.binder = "Xscope";
  frame.witnessType = "(SET)";
  frame.hypothesis = "Hscope";
  frame.sourceFormula = "(AP (TMH \"p\") (TMH \"Xscope\"))";

  RenderedKernelChoiceProofNode first;
  first.index = 0;
  first.step = "ivy_ground_0_first";
  first.hasResultFormula = true;
  first.resultFormula = frame.sourceFormula;
  first.producerProof = "(hyp \"Hscope\")";
  first.ivyContext = {frame};
  proof.nodes.push_back(first);

  RenderedKernelChoiceProofNode second;
  second.index = 1;
  second.step = "ivy_ground_0_second";
  second.parents = {first.step};
  second.hasResultFormula = true;
  second.resultFormula = frame.sourceFormula;
  second.producerProof = "(parent \"ivy_ground_0_first\")";
  second.ivyContext = {frame};
  proof.nodes.push_back(second);

  RenderedKernelChoiceProofNode final;
  final.index = 2;
  final.step = proof.finalStep;
  final.parents = {second.step};
  final.hasResultClause = true;
  final.resultClause = "(clause)";
  final.producerProof = "(parent \"ivy_ground_0_second\")";
  proof.nodes.push_back(final);

  const std::string serialized =
    Shell::MegalodonKernelBuilder::skolemChoiceProofBlock(proof);
  ALWAYS(!serialized.empty());
  ALWAYS(occurrenceCount(
    serialized,
    "(context \"ivy_scope_context_0\" \"ivy_scope_context_v1\"") == 1);
  ALWAYS(occurrenceCount(
    serialized, "(context \"ivy_scope_context_0\")") == 2);
  ALWAYS(contains(
    serialized,
    "(frame (binder \"Xscope\") (witness_type (SET))"
    " (hypothesis \"Hscope\")"
    " (source (formula (AP (TMH \"p\") (TMH \"Xscope\")))))"));

  proof.nodes[1].ivyContext[0].sourceFormula =
    "(AP (TMH \"q\") (TMH \"Xscope\"))";
  const std::string distinct =
    Shell::MegalodonKernelBuilder::skolemChoiceProofBlock(proof);
  ALWAYS(!distinct.empty());
  ALWAYS(occurrenceCount(distinct, "\"ivy_scope_context_v1\"") == 2);
  ALWAYS(contains(distinct, "(context \"ivy_scope_context_1\")"));

  proof.nodes[0].ivyContext[0].binder.clear();
  ALWAYS(Shell::MegalodonKernelBuilder::skolemChoiceProofBlock(proof).empty());
}

TEST_FUN(scopedLambdaParamodulationMarksItsEqualityParentParametric)
{
  using namespace Shell::MegalodonKernelSyntax;
  ParamodulateClauseStep step;
  step.id = "rewrite";
  step.equalityParent = unitRef("equality_parent");
  step.targetParent = unitRef("target_parent");
  step.position = position("(position 0)");
  step.from = term("(TMH \"from\")");
  step.to = term("(TMH \"to\")");
  step.result = clause("(clause)");
  step.producerUsesEqualityParentUnderBinder = true;
  step.hasProducerEqualityParentBinderVariable = true;
  step.producerEqualityParentBinderVariable = 17;

  ClauseStepRequest request;
  request.step = std::move(step);
  ClauseExpansion result;
  std::string error;
  ALWAYS(expandClauseProof({request}, "rewrite", result, error));
  ALWAYS(result.primitives.size() == 1);
  ALWAYS(result.primitives.front().producerParametricParentIds
         == std::vector<std::string>({"equality_parent"}));
  ALWAYS((result.primitives.front().producerFreshParentVariables
          == std::vector<std::pair<std::string, unsigned>>(
               {{"equality_parent", 17}})));
}

TEST_FUN(choiceProoftransSpecializesResolutionPivotAfterLocalElimination)
{
  using namespace Shell::MegalodonKernelSyntax;
  using IvyRule = RenderedKernelIvyRule;
  const std::string variable = "X0";
  const std::string local = "sK0";
  const std::string variableTerm = "(TMH \"" + variable + "\")";
  const std::string localTerm = "(TMH \"" + local + "\")";
  const auto atom = [](const std::string& argument) {
    return "(AP (TMH \"p\") " + argument + ")";
  };
  const std::string residual = "(TMH \"residual\")";
  const std::string leftLiteral = "(pos " + atom(localTerm) + ")";
  const std::string rightLiteral = "(neg " + atom(localTerm) + ")";
  const std::string residualLiteral = "(pos " + residual + ")";

  ChoiceProofStep left;
  left.hasParameterContract = true;
  left.parameters = {{variable, "(SET)"}};
  left.primitive.rule = "input";
  left.primitive.id = "left";
  left.primitive.builderOwned = true;
  left.primitive.hasResultClause = true;
  left.primitive.resultClause =
    "(clause (pos " + atom(variableTerm) + "))";
  left.primitive.producerProof = "(parent \"external_left\")";

  ChoiceProofStep right;
  right.hasParameterContract = true;
  right.parameters = left.parameters;
  right.primitive.rule = "input";
  right.primitive.id = "right";
  right.primitive.builderOwned = true;
  right.primitive.hasResultClause = true;
  right.primitive.resultClause =
    "(clause " + rightLiteral + " " + residualLiteral + ")";
  right.primitive.producerProof = "(parent \"external_right\")";

  ChoiceProofStep child;
  child.hasParameterContract = true;
  child.parameters = left.parameters;
  child.primitive.rule = "resolve";
  child.primitive.id = "result";
  child.primitive.builderOwned = true;
  child.primitive.parentIds = {left.primitive.id, right.primitive.id};
  child.primitive.hasResultClause = true;
  child.primitive.resultClause = "(clause " + residualLiteral + ")";
  child.primitive.fields = {{"pivot_left", "0"}, {"pivot_right", "0"}};
  std::string error;
  ALWAYS(expandClauseResolutionProof(
    left.primitive.id,
    {local},
    {leftLiteral},
    0,
    right.primitive.id,
    {variable},
    {rightLiteral, residualLiteral},
    0,
    {residualLiteral},
    child.primitive.producerProof,
    error));

  ChoiceTermDefinition definition;
  definition.stepId = right.primitive.id;
  definition.symbol = local;
  definition.resultType = "(SET)";
  definition.body = "(TMH \"ground_witness\")";
  definition.emitDefinitionClaim = false;
  definition.includeInEliminatedInventory = true;

  std::vector<ChoiceProofStep> steps;
  steps.push_back(std::move(left));
  steps.push_back(std::move(right));
  steps.push_back(std::move(child));
  RenderedKernelChoiceProof result;
  ALWAYS(expandChoiceNormalizedProof(
    steps, {}, {definition}, "result", result, error));
  const auto renderedChild = std::find_if(
    result.nodes.begin(), result.nodes.end(),
    [](const auto& node) { return node.step == "ivy_choice_result"; });
  ALWAYS(renderedChild != result.nodes.end());
  ALWAYS(renderedChild->ivyJustification.rule == IvyRule::Resolve);
  ALWAYS(renderedChild->ivyJustification.parentArguments.size() == 2);
  ALWAYS(renderedChild->ivyJustification.parentArguments[0]
         == std::vector<std::string>({
              "(term (TMH \"vampire_ivy_shared_term_0\"))"}));
  ALWAYS(renderedChild->ivyJustification.parentArguments[1]
         == std::vector<std::string>({
              "(term " + variableTerm + ")"}));
}

TEST_FUN(groundProoftransSpecializesEliminatedParentVariable)
{
  using namespace Shell::MegalodonKernelSyntax;
  const std::string variable = "X4294967295";
  const std::string witness = "(TMH \"ground_witness\")";
  const std::string canonical =
    "(AP (TMH \"Eps_i\")"
    " (LAMV \"ivy_inhabitant_X4294967295_set\""
    " (SET) (TMH \"vampire_true\")))";

  RenderedKernelChoiceProof source;
  source.version = "ivy_choice_dag_v3";
  source.finalStep = "ivy_choice_u_result";

  RenderedKernelChoiceProofNode parent;
  parent.index = 0;
  parent.step = "ivy_choice_u_parent";
  parent.parameters = {{variable, "(SET)"}};
  parent.hasResultClause = true;
  parent.resultClause = "(clause (pos (TMH \"p\")))";
  parent.producerProof = "(parent \"source_axiom\")";
  source.nodes.push_back(parent);

  RenderedKernelChoiceProofNode child;
  child.index = 1;
  child.step = source.finalStep;
  child.parents = {parent.step};
  child.hasResultClause = true;
  child.resultClause = "(clause)";
  child.producerProof =
    "(term_apply"
    " (term_lambda \"" + variable + "\" (SET)"
    " (term_apply (parent \"" + parent.step + "\")"
    " (term (TMH \"" + variable + "\"))))"
    " (term " + canonical + "))";
  source.nodes.push_back(child);

  RenderedKernelGroundProof ground;
  ground.version = "ivy_instance_v3";
  ground.finalStep = unitRef("u_result");
  RenderedKernelGroundInstance childInstance;
  childInstance.index = 0;
  childInstance.unit = unitRef("u_result");
  childInstance.parentInstances = {1};
  childInstance.parentEnvironments = {{}};
  ground.instances.push_back(childInstance);
  RenderedKernelGroundInstance parentInstance;
  parentInstance.index = 1;
  parentInstance.unit = unitRef("u_parent");
  parentInstance.environment.push_back({variable, term(witness)});
  ground.instances.push_back(parentInstance);

  RenderedKernelFiniteSkolemProof finite;
  finite.version = "ivy_atomic_choice_v1";
  finite.finalStep = ground.finalStep;

  RenderedKernelChoiceProof result;
  std::string error;
  ALWAYS(expandGroundChoiceProof(source, ground, finite, result, error));
  ALWAYS(result.finalStep == "ivy_ground_0_ivy_choice_u_result");
  const auto renderedChild = std::find_if(
    result.nodes.begin(), result.nodes.end(),
    [&](const auto& node) { return node.step == result.finalStep; });
  ALWAYS(renderedChild != result.nodes.end());
  ALWAYS(renderedChild->producerProof
         == "(parent \"ivy_ground_1_ivy_choice_u_parent\")");
  ALWAYS(!contains(renderedChild->producerProof, variable));
  ALWAYS(!contains(renderedChild->producerProof, "ivy_inhabitant_"));
}

TEST_FUN(groundProoftransUsesProducerParentEdgeEnvironment)
{
  using namespace Shell::MegalodonKernelSyntax;
  const std::string variable = "X0";
  const std::string variableTerm = "(TMH \"" + variable + "\")";
  const std::string witness = "(TMH \"ground_witness\")";
  const auto clause = [](const std::string& argument) {
    return "(clause (pos (AP (TMH \"p\") " + argument + ")))";
  };

  RenderedKernelChoiceProof source;
  source.version = "ivy_choice_dag_v3";
  source.finalStep = "ivy_choice_u_child";

  RenderedKernelChoiceProofNode parent;
  parent.index = source.nodes.size();
  parent.step = "ivy_choice_u_parent";
  parent.parameters = {{variable, "(SET)"}};
  parent.hasResultClause = true;
  parent.resultClause = clause(variableTerm);
  parent.producerProof =
    "(term_apply (parent \"source_parent\") (term "
    + variableTerm + "))";
  source.nodes.push_back(parent);

  RenderedKernelChoiceProofNode child;
  child.index = source.nodes.size();
  child.step = source.finalStep;
  child.parents = {parent.step};
  child.parameters = {{variable, "(SET)"}};
  child.hasResultClause = true;
  child.resultClause = clause(variableTerm);
  child.producerProof =
    "(term_apply (parent \"" + parent.step + "\") (term "
    + variableTerm + "))";
  source.nodes.push_back(child);

  RenderedKernelGroundProof ground;
  ground.version = "ivy_instance_v3";
  ground.finalStep = unitRef("u_child");
  RenderedKernelGroundInstance childInstance;
  childInstance.index = 0;
  childInstance.unit = ground.finalStep;
  childInstance.parentInstances = {1};
  childInstance.parentEnvironments = {{{variable, term(witness)}}};
  ground.instances.push_back(childInstance);
  RenderedKernelGroundInstance parentInstance;
  parentInstance.index = 1;
  parentInstance.unit = unitRef("u_parent");
  parentInstance.environment = {{variable, term(witness)}};
  ground.instances.push_back(parentInstance);

  RenderedKernelFiniteSkolemProof finite;
  finite.version = "ivy_atomic_choice_v1";
  finite.finalStep = ground.finalStep;

  RenderedKernelChoiceProof result;
  std::string error;
  ALWAYS(expandGroundChoiceProof(source, ground, finite, result, error));
  const auto renderedChild = std::find_if(
    result.nodes.begin(), result.nodes.end(),
    [&](const auto& node) { return node.step == result.finalStep; });
  ALWAYS(renderedChild != result.nodes.end());
  ALWAYS(renderedChild->parameters.empty());
  ALWAYS(renderedChild->resultClause == clause(witness));
  ALWAYS(renderedChild->producerProof
         == "(parent \"ivy_ground_1_ivy_choice_u_parent\")");
}

TEST_FUN(groundProoftransSpecializesCompactResolutionFromGeneratedParent)
{
  using namespace Shell::MegalodonKernelSyntax;
  using IvyRule = RenderedKernelIvyRule;
  const std::string variable = "X4294967295";
  const std::string variableTerm = "(TMH \"" + variable + "\")";
  const std::string witness = "(TMH \"ground_witness\")";
  const auto atom = [](const std::string& predicate,
                       const std::string& argument) {
    return "(AP (TMH \"" + predicate + "\") " + argument + ")";
  };

  RenderedKernelChoiceProof source;
  source.version = "ivy_choice_dag_v3";
  source.finalStep = "ivy_choice_u_result";

  RenderedKernelChoiceProofNode shared;
  shared.index = source.nodes.size();
  shared.step = "ivy_choice_u_shared";
  shared.parameters = {{variable, "(SET)"}};
  shared.hasResultClause = true;
  shared.resultClause =
    "(clause (pos " + atom("p", variableTerm) + "))";
  shared.producerProof = "(parent \"source_shared\")";
  shared.producerShareAcrossGroundInstances = true;
  source.nodes.push_back(shared);

  RenderedKernelChoiceProofNode generated;
  generated.index = source.nodes.size();
  generated.step = "ivy_choice_u_generated";
  generated.parameters = {{variable, "(SET)"}};
  generated.hasResultClause = true;
  generated.resultClause =
    "(clause (neg " + atom("p", variableTerm) + ")"
    " (pos " + atom("q", variableTerm) + "))";
  generated.producerProof =
    "(term_apply (parent \"source_generated\")"
    " (term " + variableTerm + "))";
  source.nodes.push_back(generated);

  RenderedKernelChoiceProofNode child;
  child.index = source.nodes.size();
  child.step = source.finalStep;
  child.parents = {shared.step, generated.step};
  child.parameters = {{variable, "(SET)"}};
  child.hasResultClause = true;
  child.resultClause =
    "(clause (pos " + atom("q", variableTerm) + "))";
  child.producerProof = "compact_resolution";
  child.ivyJustification.rule = IvyRule::Resolve;
  child.ivyJustification.parents = child.parents;
  child.ivyJustification.indices = {0, 0};
  child.ivyJustification.parentArguments = {
    {variableTerm}, {variableTerm}};
  source.nodes.push_back(child);

  RenderedKernelGroundProof ground;
  ground.version = "ivy_instance_v3";
  ground.finalStep = unitRef("u_result");
  RenderedKernelGroundInstance childInstance;
  childInstance.index = 0;
  childInstance.unit = ground.finalStep;
  childInstance.parentInstances = {1};
  childInstance.parentEnvironments = {{}};
  ground.instances.push_back(childInstance);
  RenderedKernelGroundInstance generatedInstance;
  generatedInstance.index = 1;
  generatedInstance.unit = unitRef("u_generated");
  generatedInstance.environment.push_back({variable, term(witness)});
  ground.instances.push_back(generatedInstance);

  RenderedKernelFiniteSkolemProof finite;
  finite.version = "ivy_atomic_choice_v1";
  finite.finalStep = ground.finalStep;

  RenderedKernelChoiceProof result;
  std::string error;
  ALWAYS(expandGroundChoiceProof(source, ground, finite, result, error));
  const auto renderedChild = std::find_if(
    result.nodes.begin(), result.nodes.end(),
    [&](const auto& node) { return node.step == result.finalStep; });
  ALWAYS(renderedChild != result.nodes.end());
  ALWAYS(renderedChild->parameters.empty());
  ALWAYS(renderedChild->resultClause
         == "(clause (pos " + atom("q", witness) + "))");
  ALWAYS(renderedChild->ivyJustification.parents.size() == 2);
  ALWAYS(renderedChild->ivyJustification.parentArguments.size() == 2);
  ALWAYS(renderedChild->ivyJustification.parentArguments[0]
         == std::vector<std::string>({witness}));
  ALWAYS(renderedChild->ivyJustification.parentArguments[1].empty());
}

TEST_FUN(groundProoftransDoesNotCaptureDifferentSortParentVariable)
{
  using namespace Shell::MegalodonKernelSyntax;
  using IvyRule = RenderedKernelIvyRule;
  const std::string childVariable = "X0";
  const std::string childSetVariable = "X1";
  const std::string parentPropVariable = "X2";
  const std::string groundSet = "(TMH \"ground_set\")";
  const auto named = [](const std::string& name) {
    return "(TMH \"" + name + "\")";
  };
  const auto atom = [](const std::string& argument) {
    return "(AP (TMH \"q\") " + argument + ")";
  };

  RenderedKernelChoiceProof source;
  source.version = "ivy_choice_dag_v3";
  source.finalStep = "ivy_choice_u_child";

  RenderedKernelChoiceProofNode parent;
  parent.index = source.nodes.size();
  parent.step = "ivy_choice_u_parent";
  parent.parameters = {
    {childVariable, "(SET)"}, {parentPropVariable, "(PROP)"}};
  parent.hasResultClause = true;
  parent.resultClause =
    "(clause (pos " + atom(named(parentPropVariable)) + "))";
  parent.producerProof =
    "(term_apply (term_apply (parent \"source_parent\")"
    " (term " + named(childVariable) + "))"
    " (term " + named(parentPropVariable) + "))";
  source.nodes.push_back(parent);

  RenderedKernelChoiceProofNode child;
  child.index = source.nodes.size();
  child.step = source.finalStep;
  child.parents = {parent.step};
  child.parameters = {
    {childVariable, "(PROP)"}, {childSetVariable, "(SET)"}};
  child.hasResultClause = true;
  child.resultClause =
    "(clause (pos " + atom(named(childVariable)) + "))";
  child.producerProof = "compact_instantiation";
  child.ivyJustification.rule = IvyRule::Instantiate;
  child.ivyJustification.parents = child.parents;
  child.ivyJustification.terms = {
    named(childSetVariable), named(childVariable)};
  source.nodes.push_back(child);

  RenderedKernelGroundProof ground;
  ground.version = "ivy_instance_v3";
  ground.finalStep = unitRef("u_child");
  RenderedKernelGroundInstance childInstance;
  childInstance.index = 0;
  childInstance.unit = ground.finalStep;
  childInstance.parentInstances = {1};
  childInstance.parentEnvironments = {{}};
  childInstance.environment.push_back(
    {childSetVariable, term(groundSet)});
  ground.instances.push_back(childInstance);
  RenderedKernelGroundInstance parentInstance;
  parentInstance.index = 1;
  parentInstance.unit = unitRef("u_parent");
  parentInstance.environment.push_back(
    {childVariable, term(groundSet)});
  ground.instances.push_back(parentInstance);

  RenderedKernelFiniteSkolemProof finite;
  finite.version = "ivy_atomic_choice_v1";
  finite.finalStep = ground.finalStep;

  RenderedKernelChoiceProof result;
  std::string error;
  ALWAYS(expandGroundChoiceProof(source, ground, finite, result, error));
  const auto renderedChild = std::find_if(
    result.nodes.begin(), result.nodes.end(),
    [&](const auto& node) { return node.step == result.finalStep; });
  ALWAYS(renderedChild != result.nodes.end());
  ALWAYS((renderedChild->parameters
          == std::vector<std::pair<std::string, std::string>>(
               {{childVariable, "(PROP)"}})));
  ALWAYS(renderedChild->resultClause
         == "(clause (pos " + atom(named(childVariable)) + "))");
  ALWAYS(renderedChild->ivyJustification.terms
         == std::vector<std::string>(
              {named(childVariable)}));
  ALWAYS(!contains(renderedChild->resultClause, "ground_set"));
}
