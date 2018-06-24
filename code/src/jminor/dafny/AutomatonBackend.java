package jminor.dafny;

import java.io.File;
import java.util.ArrayList;
import java.util.logging.Logger;

import org.apache.commons.configuration2.Configuration;
import org.stringtemplate.v4.ST;

import bgu.cs.util.FileUtils;
import bgu.cs.util.STGLoader;
import bgu.cs.util.StringUtils;
import bgu.cs.util.graph.MultiGraph.Edge;
import jminor.JminorDebugger;
import jminor.JminorProblem;
import jminor.PrimitiveVar;
import jminor.RefVar;
import jminor.Stmt;
import jminor.Var;
import pexyn.generalization.Action;
import pexyn.generalization.Automaton;
import pexyn.generalization.State;

/**
 * Generates a Java implementation from an automaton.
 * 
 * @author romanm
 */
public class AutomatonBackend {
	private final STGLoader templates = new STGLoader(AutomatonBackend.class);

	private final Automaton automaton;
	private final JminorProblem problem;
	private final Configuration config;
	private final JminorDebugger debugger;
	private final Logger logger;

	public AutomatonBackend(Automaton automaton, JminorProblem problem, Configuration config, JminorDebugger debugger, Logger logger) {
		this.automaton = automaton;
		this.problem = problem;
		this.config = config;
		this.debugger = debugger;
		this.logger = logger;
	}

	public void generate() {
		if (automaton.outDegree(automaton.getInitial()) == 0) {
			logger.info("Encountered degenerate automaton. Skipped Java code generation.");
			return;
		}		
		var className = StringUtils.capitalizeFirst(problem.name);
		var methodName = problem.name;
		var classFileName = className + ".dfy";
		var classFileST = templates.load("ClassFile");
		classFileST.add("className", className);
		classFileST.add("methodName", methodName);
		for (var inputArg : problem.inputArgs) {
			classFileST.add("args", new JavaVar(inputArg));
		}
		for (var outputArg : problem.outputArgs) {
			classFileST.add("returnArg", new JavaVar(outputArg));
		}
		for (var temp : problem.temps) {
			classFileST.add("locals", new JavaVar(temp));
		}

		for (var state : automaton.getNodes()) {
			classFileST.add("states", stateName(state.toString()));
		}

		for (var state : automaton.getNodes()) {
			if (state == automaton.getFinal()) {
				continue;
			}

			var stateCodeST = templates.load("StateCode");
			stateCodeST.add("name", stateName(state.toString()));
			var trans = new ArrayList<Transition>();
			for (var edge : automaton.succEdges(state)) {
				trans.add(new Transition(edge));
			}
			if (trans.size() == 1) {
				trans.get(0).type = TransitionType.UPDATE;
			} else {
				trans.get(0).type = TransitionType.FIRST;
				for (int i = 1; i < trans.size() - 1; ++i) {
					trans.get(i).type = TransitionType.MIDDLE;
				}
				trans.get(trans.size() - 1).type = TransitionType.LAST;
			}
			for (var transition : trans) {
				ST transST = null;
				switch (transition.type) {
				case UPDATE:
					transST = templates.load("UpdateTransition");
					break;
				case FIRST:
					transST = templates.load("IfTransition");
					transST.add("guard", transition.guard);
					break;
				case MIDDLE:
					transST = templates.load("ElseIfTransition");
					transST.add("guard", transition.guard);
					break;
				case LAST:
					transST = templates.load("ElseTransition");
					break;
				}
				transST.add("update", transition.command);
				transST.add("succ", transition.succ);
				stateCodeST.add("transitions", transST.render());
			}
			classFileST.add("stateCodes", stateCodeST.render());
		}

		var text = classFileST.render();
		debugger.addCodeFile("dfy-implementation.txt", text, "A Dafny implementation");
		FileUtils.stringToFile(text, config.getString("pexyn.implementationDir", ".") + File.separator + classFileName);
	}

	public enum TransitionType {
		UPDATE, FIRST, MIDDLE, LAST
	}

	public final class Transition {
		public final String succ;
		public final String guard;
		public final String command;
		public TransitionType type;

		public Transition(Edge<State, Action> e) {
			this.succ = stateName(e.getDst().toString());
			var guard = e.getLabel().guard();
			if (guard != null) {
				this.guard = guard.toString();
			} else {
				this.guard = null;
			}
			var update = e.getLabel().update;
			if (update.toString().equals("return")) {
				this.command = "// finish";
			} else {
				this.command = Renderer.render((Stmt) update);
			}
		}
	}

	public static final class JavaVar {
		public final String name;
		public final String type;
		public final String defaultVal;

		public JavaVar(Var v) {
			this.name = v.name;
			this.type = v.getType().getName();
			if (v instanceof PrimitiveVar) {
				this.defaultVal = "0";
			} else if (v instanceof RefVar) {
				this.defaultVal = "null";
			} else {
				throw new Error("Unsupported variable type: " + v);
			}
		}
	}

	public static String stateName(String originalName) {
		switch (originalName) {
			case "initial":
				return "ENTRY";
			case "final":
				return "EXIT";
			default:
				return originalName;
		}
	}
}
