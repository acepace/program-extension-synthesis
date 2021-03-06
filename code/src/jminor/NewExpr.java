package jminor;

import java.util.List;

import bgu.cs.util.treeGrammar.Node;
import bgu.cs.util.treeGrammar.Visitor;

/**
 * The operator corresponding to an object allocation.
 * 
 * @author romanm
 */
public class NewExpr extends Expr {
	public NewExpr(RefType type) {
		super(type);
	}

	public RefType getType() {
		return (RefType) args.get(0);
	}

	protected NewExpr(List<Node> args) {
		super(args);
		assertNumOfArgs(1);
	}

	@Override
	public NewExpr clone(List<Node> args) {
		return new NewExpr(args);
	}

	@Override
	public void accept(Visitor v) {
		JminorVisitor whileVisitor = (JminorVisitor) v;
		whileVisitor.visit(this);
	}
}