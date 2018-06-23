package pexyn.guardInference;

/**
 * A domain for Boolean formulae.
 * 
 * @author romanm
 *
 * @param <ExampleType>
 *            The type of examples.
 * @param <FormulaType>
 *            The type of formulae.
 */
public interface BooleanDomain<ExampleType, FormulaType> {
	FormulaType getTrue();

	FormulaType getFalse();

	FormulaType and(FormulaType first, FormulaType second);

	FormulaType or(FormulaType first, FormulaType second);

	boolean test(ExampleType example, FormulaType feature);
}
