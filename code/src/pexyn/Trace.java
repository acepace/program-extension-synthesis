package pexyn;

/**
 * Defines a sequence of actions and intermediate states, starting from an input
 * state and leading to a goal state.
 * 
 * @author romanm
 *
 * @param <StateType>
 *            The type of states.
 * @param <ActionType>
 *            The type of actions applied to states.
 */
public interface Trace<StateType, ActionType> {
	/**
	 * Returns the number of states in the plan.
	 */
	int size();

	/**
	 * Holds if there are no states in this plan.
	 */
	default boolean isEmpty() {
		return size() == 0;
	}

	/**
	 * Allows iterating over the sequence of states in this trace.
	 */
	Iterable<StateType> states();

	/**
	 * Allows iterating over the sequence of actions in this trace.
	 */
	Iterable<ActionType> actions();

	/**
	 * Returns the state at the given position, which must be within 0 and
	 * <code>size()</code>.
	 */
	StateType stateAt(int i);

	/**
	 * Returns the action at the given position, which must be within 0 and
	 * <code>size()-1</code>.
	 */
	ActionType actionAt(int i);

	default StateType firstState() {
		return stateAt(0);
	}

	default StateType lastState() {
		assert !isEmpty();
		return stateAt(size() - 1);
	}

	void setFirst(StateType state);

	/**
	 * Precondition: <code>!isEmpty()</code>
	 */
	void append(ActionType action, StateType state);

	/**
	 * Precondition: <code>!isEmpty()</code>
	 */
	void prepend(ActionType action, StateType state);

	/**
	 * Precondition: <code>!isEmpty()</code>
	 */
	default void appendPlan(Trace<StateType, ActionType> other) {
		if (other.isEmpty()) {
			return;
		} else {
			if (!other.firstState().equals(this.lastState())) {
				throw new IllegalArgumentException("First state of given plan must match last state of this plan!");
			}
			for (int i = 0; i < other.size() - 1; ++i) {
				append(other.actionAt(i), other.stateAt(i + 1));
			}
		}
	}

	/**
	 * Precondition: <code>!isEmpty()</code>
	 */
	void prependPlan(Trace<StateType, ActionType> other);

	/**
	 * Compares two plans, assuming actions are deterministic.
	 */
	default boolean eqDeterministic(Trace<StateType, ActionType> other) {
		return this.firstState().equals(other.firstState()) && this.actions().equals(other.actions());
	}
}