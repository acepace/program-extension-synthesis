package jminor.analyser;

import bgu.cs.util.FileUtils;
import bgu.cs.util.STGLoader;
import bgu.cs.util.graph.HashMultiGraph;
import jminor.*;
import jminor.codegen.AutomatonCodegen;
import jminor.codegen.DafnySemanticsRenderer;
import jminor.codegen.JavaVar;
import jminor.codegen.SemanticsRenderer;
import org.apache.commons.configuration2.Configuration;
import org.stringtemplate.v4.ST;
import pexyn.GPDebugger;
import pexyn.Semantics;
import pexyn.generalization.Action;
import pexyn.generalization.Automaton;
import pexyn.generalization.State;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;


/*
    Core algorithm
    For each node and each edge, we want to generate a dafny test method
        NodeX_EdgeC_1_NodeY
*/

public class DafnyAnalyser {
    private JminorProblem problem;
    private Automaton program;
    private Configuration config;
    private GPDebugger<JmStore, Stmt, BoolExpr> debugger;
    private Collection<Semantics.Guard> guards;
    private Map<Integer, Semantics.Guard> idToGuard;
    private Map<Semantics.Guard, Integer> guardToId;
    private Collection<Semantics.Cmd> cmds;
    private Collection<Method> currentMethods;
    private SemanticsRenderer renderer;
    private STGLoader templates;

    public DafnyAnalyser(JminorProblem problem, Automaton automaton, Configuration config, GPDebugger<JmStore, Stmt, BoolExpr> debugger) {
        this.debugger = debugger;
        this.problem = problem;
        this.program = automaton;
        this.guards = automaton.getGuards();
        this.cmds = automaton.getCommands();
        this.config = config;
        this.idToGuard = new HashMap<>(guards.size());
        this.guardToId = new HashMap<>(guards.size());
        int i = 0;
        for (Semantics.Guard guard : guards) {
            idToGuard.put(i, guard);
            guardToId.put(guard, i);
            i++;
        }

        renderer = new DafnySemanticsRenderer();
        templates = new STGLoader(AutomatonCodegen.class, "DafnyAutomatonCodegen.stg");
    }


    private Set<Semantics.Guard> collectValidMethodAssertions(Method method) {
        debugger.info("Collecting assertions for method " + method.getMethodName());
        String fileText = method.toString();
        Set<Semantics.Guard> methodFailedGuards = new HashSet<>();
        var fileName = config.getString("pexyn.implementationDir", ".") + File.separator + "dafnyTestAnalyser.dfy";
        try {
            FileUtils.stringToFile(fileText, fileName);
            String[] dafnyResults = DafnyRunner.runDafny(config, fileName);
            //we have errors, extract and append to method
            for (String assertString : dafnyResults) {
                var lineNum = Integer.valueOf(assertString.substring(assertString.indexOf("(") + 1, assertString.indexOf(",")));
                String assertLine = fileText.split("\n")[lineNum - 1];
                String assertNum = assertLine.substring(assertLine.indexOf("//") + 2).replaceAll("\\s+", "");
                int assertNumber = Integer.valueOf(assertNum);
                var failedGuard = idToGuard.get(assertNumber);
                methodFailedGuards.add(failedGuard);
            }

            Files.deleteIfExists(Paths.get(fileName));
        } catch (IOException e) {
            e.printStackTrace(); //total failure
        }
        var toRet = new HashSet<>(method.post);
        toRet.removeAll(methodFailedGuards);
        return toRet;

    }

    public void analyseAutomaton() {
        /*
        Start from initial state
            For each state, check what assertions work in the end, add them.
                For each edge successor edge, add the same checks, adding the now asserts as requirements
                in case of loops do a JOIN operation

         */
        Queue<State> worklist = new LinkedList<>(program.getNodes());
        debugger.info("Starting point iteration");

        while (!worklist.isEmpty()) {
            var currentState = worklist.remove();
            for (var edge : program.succEdges(currentState)) {

                //currently handle only assignments
                if (!(edge.label.update instanceof AssignStmt)) {
                    debugger.warning("Edge " + edge.toString() + "Missing an update" + edge.label.update);
                    continue;
                }
                //TOO handle loops somehow
                boolean changed = handleEdge(currentState, edge);
                if (changed) {
                    if (!worklist.contains(edge.dst)) {
                        worklist.add(edge.dst);
                    }
                    if (!worklist.contains(edge.src)) {
                        worklist.add(edge.src);
                    }
                }
            }
        }
        debugger.info("Fixed point iteration ends");

    }

    private boolean handleEdge(State currentState, HashMultiGraph<State, Action>.HashEdge edge) {
        var command = (AssignStmt) edge.label.update;
        var dst = edge.dst;
        var method = new Method();
        method.src = currentState;
        method.dst = dst;
        method.update = command;
        method.pre = new HashSet<>(currentState.assertions);
        method.post = new HashSet<>(guards);
        Set<Semantics.Guard> validGuards = collectValidMethodAssertions(method);
        currentState.assertions.addAll(validGuards);
        dst.requirements.addAll(validGuards);
        return (!method.pre.equals(validGuards));
    }

    private Collection<Method> getMethodsInit() {
        //Generate all the methods starting off
        Collection<Method> methods = new HashSet<>();

        Collection<State> states = program.getNodes();
        for (State state : states) {
            //edges out
            for (var edge : program.succEdges(state)) {
                //currently handle only assignments
                if (!(edge.label.update instanceof AssignStmt)) {
                    continue;
                }
                var command = (AssignStmt) edge.label.update;
                var dst = edge.dst;
                var method = new Method();
                method.src = state;
                method.dst = dst;
                method.update = command;
                method.pre = new HashSet<>(guards);
                method.post = new HashSet<>(guards);
                methods.add(method);
            }
        }

        return methods;
    }


    public Automaton getGuardedAutomaton() {
        return program.clone();
    }

    class Method {
        State src;
        State dst;
        AssignStmt update;
        Collection<Semantics.Guard> pre;
        Collection<Semantics.Guard> post;


        String getMethodName() {
            var escapedUpdate = update.toString()
                    .replace("=", "_").replace(" ", "")
                    .replace("(", "").replace(")", "")
                    .replace(";", "")
                    .replace("-", "MIN").replace("+", "PL")
                    .replace("*","TIMES").replace("/","DIV");
            return src.toString() + "_" + escapedUpdate + "_" + dst.toString();
        }

        ST toDafnyMethod() {
            ST classFileST = templates.load("AnalyserClassFile");
            var className = "DafnyClass" + src.toString() + "_" + dst.toString();

            classFileST.add("className", className);
            classFileST.add("methodName", getMethodName());

            List<JavaVar> methodArgs = new ArrayList<>();

            for (var inputArg : problem.inputArgs) {
                var javaVar = new JavaVar(inputArg);
                methodArgs.add(javaVar);
                classFileST.add("args", javaVar);
            }
            for (var local : problem.temps) {
                var javaVar = new JavaVar(local);
                methodArgs.add(javaVar);
                classFileST.add("args", javaVar);
            }
            for (var outArg : problem.outputArgs) {
                var javaVar = new JavaVar(outArg);
                methodArgs.add(javaVar);
                classFileST.add("args", javaVar);
            }

            /*for (var inputArg : methodArgs) {
                AutomatonCodegen.JavaVar arg = null;
                if (inputArg instanceof VarExpr) {
                    var realArg = ((VarExpr) inputArg).getVar();
                    arg = new AutomatonCodegen.JavaVar(realArg);
                } else if (inputArg instanceof PrimitiveVar) {
                    var realArg = ((PrimitiveVar) inputArg);
                    arg = new AutomatonCodegen.JavaVar(realArg);
                }
                String argName = arg.name;
                assert inputArg instanceof VarExpr;
                if (problem.inputArgs.stream().noneMatch(x -> ((PrimitiveVar) x).name.equals(argName))) {
                    classFileST.add("args", arg);
                }
            }*/

            var lhs = update.getLhs().getArgs().get(0);
            var realArg = ((PrimitiveVar) lhs);

            if (methodArgs.stream().noneMatch(methodArg ->
                    methodArg.name.equals(realArg.name))) {
                var lhsVar = new JavaVar(realArg);
                classFileST.add("locals", lhsVar);
            } else { //already existed
                classFileST.add("init_code", "var " + realArg.getName() + " := " + realArg.getName() + ";");
            }


            classFileST.add("stateCodes", renderer.renderCmd(update));
            //now time to add in pre/post
            for (var preCond : pre) {
                var preAssert = "requires " + renderer.renderGuard(preCond) + ";" + "//" + guardToId.get(preCond).toString();
                classFileST.add("requireStmts", preAssert);
            }
            for (var postCond : post) {
                var preAssert = "assert " + renderer.renderGuard(postCond) + ";" + "//" + guardToId.get(postCond).toString();
                classFileST.add("postStmts", preAssert);
            }
            return classFileST;
        }

        @Override
        public String toString() {


            return toDafnyMethod().render();
        }
    }
}
