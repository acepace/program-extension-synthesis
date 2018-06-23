package pexyn.planning;

import java.util.function.Predicate;

import pexyn.ArrayListTrace;
import pexyn.Trace;

/**
 * An algorithm that finds a path of actions from the given input state to a
 * state satisfying the goal.
 * 
 * @author romanm
 *
 * @param <StateType>
 *            The type of states in the state space.
 * @param <ActionType>
 *            The type of actions that label transitions in the transition
 *            relation.
 */
public interface Planner<StateType, ActionType> extends Searcher<StateType, ActionType> {
	/**
	 * Attempts to finds a sequence of actions from the given input state to a state
	 * satisfying the goal.
	 * 
	 * @param input
	 *            The start state.
	 * @param goalTest
	 *            A predicate that tests whether a state satisfies the goal
	 *            condition.
	 * @param addToPlan
	 *            If a plan is found, it is appended to this one.
	 * @return The result of the search.
	 */
    SearchResultType findPlan(StateType input, Predicate<StateType> goalTest,
                              Trace<StateType, ActionType> addToPlan);

	@Override
    default SearchResult<StateType> findState(StateType input, Predicate<StateType> goalTest) {
		Trace<StateType, ActionType> plan = new ArrayListTrace<>(input);
		SearchResultType result = findPlan(input, goalTest, plan);
		switch (result) {
		case OK:
			return SearchResult.of(plan.lastState());
		case NO_SOLUTION_EXISTS:
			return SearchResult.noSolutionExists();
		case OUT_OF_RESOURCES:
			return SearchResult.outOfResources();
		default:
			throw new Error("Unexpected search result type: " + result.getClass().getSimpleName());
		}
	}
}