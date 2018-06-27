package pexyn;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import pexyn.Semantics.Guard;
import pexyn.Semantics.Cmd;
import pexyn.Semantics.Store;

/**
 * A program semantics.
 * 
 * @author romanm
 *
 * @param <StoreType>
 *            The type of data values (configurations) in the semantics.
 * @param <CmdType>
 *            The type of operations that can modify stores.
 * @param <GuardType>
 *            The type of predicates on stores.
 */
public interface Semantics<StoreType extends Store, CmdType extends Cmd, GuardType extends Guard> {
	/**
	 * The name of this semantics.
	 */
    String name();

	/**
	 * Returns the always-true predicate.
	 */
    GuardType getTrue();

	/**
	 * Tests whether the given predicate holds for the given store.
	 * 
	 * @param guard
	 *            A value of type {@link GuardType}. A case down should be safe for
	 *            the instantiating semantics.
	 * @param store
	 *            A value of type {@link StoreType}. A cast down should be safe for
	 *            the instantiating semantics.
	 */
    boolean test(GuardType guard, StoreType store);

	/**
	 * Returns the cost of the given guard, which is used as a preference for guard
	 * inference.
	 */
    float guardCost(GuardType guard);

	/**
	 * Tests whether the first store matches (i.e., subsumed by) the second store.
	 */
    boolean match(StoreType first, StoreType second);

	/**
	 * Attempts to apply the given update to the given value.
	 * 
	 * @param update
	 *            An update of type {@link CmdType}.
	 * @param value
	 *            An input value.
	 * @return the resulting value, if the update can be applied to the input value
	 *         and empty otherwise.
	 */
    Optional<StoreType> apply(CmdType update, StoreType value);

	/**
	 * Returns a list of likely predicates for the given plans.
	 */
    List<GuardType> generateGuards(List<Trace<StoreType, CmdType>> plans);

	/**
	 * Returns a list of likely atomic predicates for the given plans.
	 */
    List<GuardType> generateBasicGuards(List<Trace<StoreType, CmdType>> plans);

	/**
	 * Constructs a disjunction of guards.
	 */
    GuardType or(GuardType l, GuardType r);

	/**
	 * Constructs a conjunction of guards.
	 */
    GuardType and(GuardType l, GuardType r);

	/**
	 * Constructs a negated guard.
	 */
	public GuardType not(GuardType l);

	/**
	 * Returns a complete list (including Boolean negation) of likely atomic
	 * predicates for the given plans
	 */
	default List<GuardType> generateCompleteBasicGuards(List<Trace<StoreType, CmdType>> plans) {
		var basicGuards = generateBasicGuards(plans);
		var result = new ArrayList<GuardType>(basicGuards);
		for (var guard : basicGuards) {
			result.add(not(guard));
		}
		return result;
	}

	/**
	 * An interface marking semantics stores (values).
	 * 
	 * @author romanm
	 */
    interface Store {
	}

	/**
	 * A marker interface for a store resulting from an application of a command to
	 * a store that is not in its domain.
	 * 
	 * @author romanm
	 */
    interface ErrorStore {
		/**
		 * Returns a textual description of the error.
		 */
        String message();
	}

	/**
	 * An interface marking operations that modify semantics stores.
	 * 
	 * @author romanm
	 */
    interface Cmd {
	}

	/**
	 * An interface for marking predicates over stores.
	 * 
	 * @author romanm
	 */
    interface Guard {
	}
}