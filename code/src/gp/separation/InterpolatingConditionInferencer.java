package gp.separation;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import gp.Domain;
import gp.Domain.Value;
import grammar.CachedLanguageIterator;
import heap.BoolExpr;
import heap.PWhileInterpreter;
import heap.Stmt;
import heap.Store;

/**
 * An inferencer based on finding a Boolean Craig interpolant.
 * 
 * @author romanm
 *
 * @param <StateType>
 *            The type of states over which conditions range.
 */
public class InterpolatingConditionInferencer extends ConditionInferencer<Store, Stmt, BoolExpr> {
	private String outputDir;
	public Map<Store, List<Boolean>> predicates;

	private final CachedLanguageIterator citer;

	// TODO - remove @outputDir (env variables?)
	public InterpolatingConditionInferencer(Domain<Store, Stmt, BoolExpr> domain, CachedLanguageIterator citer,
			String outputDir) {
		super(domain);
		this.outputDir = outputDir;
		this.predicates = new HashMap<>();
		this.citer = citer;
	}

	@Override
	public Optional<BoolExpr> infer(Collection<? extends Value> first, Collection<? extends Value> second) {
		BoolExpr result = null;
		Interpolator intp = new Interpolator(outputDir);

		int maxPredicateIndx = 0;
		for (Collection<? extends Value> states : Arrays.asList(first, second)) {
			initStatePredicates(states);
			for (Value v : states) {
				Store state = (Store) v;
				if (maxPredicateIndx < this.predicates.get(state).size()) {
					maxPredicateIndx = this.predicates.get(state).size();
				}
			}
		}

		while (true) {
			List<List<Boolean>> thisTerm = new ArrayList<>();
			List<List<Boolean>> othersTerm = new ArrayList<>();

			for (Value v1 : first) {
				Store state = (Store) v1;
				thisTerm.add(predicates.get(state));
			}
			for (Value v2 : second) {
				Store state = (Store) v2;
				othersTerm.add(predicates.get(state));
			}

			BoolExpr interpol = intp.genInterpolant(thisTerm, othersTerm, citer);
			if (interpol == null) {
				// 1) first evaluate EXISTING predicates for all the states
				// (make sure the predicates lists cover all the existing predicates for each
				// state)
				// 2) when the lists have the same length - generate a NEW predicate
				boolean updateall = true;
				while (updateall) {
					for (Collection<? extends Value> states : Arrays.asList(first, second)) {
						for (Value v : states) {
							Store state = (Store) v;
							int nextPredIndx = this.predicates.get(state).size();
							if (nextPredIndx < maxPredicateIndx) {
								updateall = false;
								if (!extendStatePredicates(state)) {
									// no more predicates are available
									return Optional.empty();
								}
							}
						}
					}

					if (updateall) {
						maxPredicateIndx++;
					}
				}
			} else {
				result = interpol;
				break;
			}
		}
		return Optional.of(result);
	}

	private boolean extendStatePredicates(Store state) {
		List<Boolean> statePredicates = this.predicates.get(state);
		int nextPredIndx = statePredicates.size();
		Boolean test = null;
		while (test == null) {
			if (citer.has(nextPredIndx)) {
				// TODO: unsafe casting to BoolExpr - refactor
				BoolExpr condition = (BoolExpr) citer.get(nextPredIndx);
				test = PWhileInterpreter.v.test(condition, state);
				// false, if predicate value is undefined for this state
				if (test == null) {
					test = false;
				}
				statePredicates.add(test);
				nextPredIndx++;
			} else {
				break;
			}
		}
		return (test != null);
	}

	private void initStatePredicates(Collection<? extends Value> states) {
		for (Value v : states) {
			Store state = (Store) v;
			Boolean initialized = false;
			List<Boolean> preds = this.predicates.get(state);
			if (preds == null) {
				preds = new ArrayList<>();
				this.predicates.put(state, preds);
			}
			for (Boolean pred : this.predicates.get(state)) {
				if (pred != null) {
					initialized = true;
					break;
				}
			}
			if (!initialized) {
				extendStatePredicates(state);
			}
		}
	}
}