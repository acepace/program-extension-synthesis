package pexyn.planning;

import java.util.Collection;
import java.util.Iterator;

/**
 * A non-deterministic transition relation with a positive weight associated
 * with each transition.
 * 
 * @author romanm
 *
 * @param <StateType>
 *            The type of states in the state space.
 * @param <ActionType>
 *            The type of actions in the transition relation.
 */
public interface TR<StateType, ActionType> {
	/**
	 * A convenient value for the maximum possible cost.
	 */
    float MAX_COST = Float.MAX_VALUE;

	/**
	 * Returns the set of actions that are enabled for the given state.
	 */
    Collection<ActionType> enabledActions(StateType state);

	/**
	 * Returns an iterator of the set of enabled actions.
	 */
	default Iterator<ActionType> enabledActionsIterator(StateType state) {
		return enabledActions(state).iterator();
	}

	/**
	 * Returns the cost of taking the transition from the source state to the
	 * destination state with the given action.
	 */
    float transitionCost(StateType src, ActionType action, StateType dst);

	/**
	 * Applies the given action to the given state and returns the resulting
	 * (possibly empty) collection of states.
	 */
    Collection<StateType> apply(StateType state, ActionType action);

	/**
	 * Returns the maximal cost of taking a transition from the source state to any
	 * destination state with the given action.
	 */
	default float actionCost(StateType src, ActionType action) {
		float result = 0;
		for (StateType dst : apply(src, action)) {
			result = Math.max(result, transitionCost(src, action, dst));
		}
		return result;
	}

	/**
	 * Returns a lower bound on the cost of any path from the given state to a goal
	 * state.
	 */
	default float estimateDistToGoal(StateType state) {
		return 0;
	}
}