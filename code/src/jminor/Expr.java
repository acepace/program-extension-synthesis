package jminor;

import java.util.*;

import bgu.cs.util.treeGrammar.Node;

/**
 * The base class of Jminor expressions.
 * 
 * @author romanm
 */
public abstract class Expr extends Node {
	protected final List<Node> args;

	@Override
	public final List<Node> getArgs() {
		return args;
	}

	protected Expr(Collection<Node> nodes) {
		super(countNonterminals(nodes));
		args = Collections.unmodifiableList(new ArrayList<>(nodes));
	}

	@Override
	public String toString() {
		return Renderer.render(this);
	}

	@Override
	public boolean equals(Object o) {
		if (o == null) {
			return false;
		}
		if (o == this) {
			return true;
		}
		if (!this.getClass().equals(o.getClass())) {
			return false;
		}
		Expr other = (Expr) o;
		for (var i = 0; i < args.size(); ++i) {
			if (!args.get(i).equals(other.args.get(i))) {
				return false;
			}
		}
		return true;
	}

	protected Expr(Node... nodes) {
		super(countNonterminals(nodes));
		var argList = new ArrayList<Node>(nodes.length);
		argList.addAll(Arrays.asList(nodes));
		args = Collections.unmodifiableList(argList);
	}
}