package jminor.analyser;

import bgu.cs.util.FileUtils;
import bgu.cs.util.STGLoader;
import bgu.cs.util.treeGrammar.Node;
import jminor.AssignStmt;
import jminor.JminorProblem;
import jminor.PrimitiveVar;
import jminor.VarExpr;
import jminor.codegen.AutomatonCodegen;
import jminor.codegen.DafnySemanticsRenderer;
import jminor.codegen.SemanticsRenderer;
import org.apache.commons.configuration2.Configuration;
import org.stringtemplate.v4.ST;
import pexyn.Semantics;
import pexyn.generalization.Automaton;
import pexyn.generalization.State;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.*;
import java.util.stream.Collectors;


/*
    Core algorithm
    For each node and each edge, we want to generate a dafny test method
        NodeX_EdgeC_1_NodeY
*/

public class DafnyAnalyser {
    private JminorProblem problem;
    private Automaton program;
    private Configuration config;
    private Collection<Semantics.Guard> guards;
    private Map<Integer, Semantics.Guard> idToGuard;
    private Map<Semantics.Guard, Integer> guardToId;
    private Collection<Semantics.Cmd> cmds;
    private Collection<Method> currentMethods;
    private SemanticsRenderer renderer;
    private STGLoader templates;

    public DafnyAnalyser(JminorProblem problem, Automaton automaton, Configuration config, Collection<Semantics.Guard> guards, Collection<Semantics.Cmd> cmds) {
        this.problem = problem;
        this.program = automaton;
        this.config = config;
        this.guards = guards;
        this.idToGuard = new HashMap<>(guards.size());
        this.guardToId = new HashMap<>(guards.size());
        int i = 0;
        for (Semantics.Guard guard : guards) {
            idToGuard.put(i, guard);
            guardToId.put(guard, i);
            i++;
        }

        this.cmds = cmds;

        renderer = new DafnySemanticsRenderer();
        templates = new STGLoader(AutomatonCodegen.class, "DafnyAutomatonCodegen.stg");
    }

    public void collectAssertions() {
        currentMethods = getMethodsInit();
        var textResList = currentMethods.stream().map(Method::toString).collect(Collectors.toList());
        StringBuilder sb = new StringBuilder();
        for (String s : textResList) {
            sb.append(s);
            sb.append("\n\n");
        }

        var fileName = config.getString("pexyn.implementationDir", ".") + File.separator + "dafnyTestAnalyser.dfy";

        try {
            FileUtils.stringToFile(sb.toString(), fileName);
            String[] dafnyResults = DafnyRunner.runDafny(config, fileName);
            if (dafnyResults.length == 0) {
                //all went ok, not sure what to do then :)
            }
            //we have errors, extract and append to method

            Files.deleteIfExists(Paths.get(fileName));
        } catch (IOException e) {
            e.printStackTrace(); //total failure
        }


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

    private class Method {
        State src;
        State dst;
        AssignStmt update;
        Collection<Semantics.Guard> pre;
        Collection<Semantics.Guard> post;

        @Override
        public String toString() {
            ST classFileST = templates.load("AnalyserClassFile");
            var className = "DafnyClass" + src.toString() + "_" + dst.toString();
            var escapedUpdate = update.toString()
                    .replace("=", "_").replace(" ", "")
                    .replace("(", "").replace(")", "")
                    .replace(";", "")
                    .replace("-", "MIN").replace("+", "PL");
            var methodName = src.toString() + "_" + escapedUpdate + "_" + dst.toString();
            classFileST.add("className", className);
            classFileST.add("methodName", methodName);

            List<Node> methodArgs = update.getRhs().getArgs(); //get assignment args

            for (var inputArg : problem.inputArgs) {
                classFileST.add("args", new AutomatonCodegen.JavaVar(inputArg));
            }

            var lhs = update.getLhs().getArgs().get(0);
            var realArg = ((PrimitiveVar) lhs);

            if (methodArgs.stream().noneMatch(methodArg -> {
                if (methodArg instanceof VarExpr) {
                    return ((VarExpr) methodArg).getVar().equals(lhs);
                } else {
                    return methodArg.equals(lhs);
                }
            })) {
                var lhsVar = new AutomatonCodegen.JavaVar(realArg);
                classFileST.add("locals", lhsVar);
            } else { //already existed
                classFileST.add("init_code", "var " + realArg.getName() + " := " + realArg.getName() + ";");
            }


            classFileST.add("stateCodes", renderer.renderCmd(update));
            //now time to add in pre/post
            for (var preCond : pre) {
                var preAssert = "requires " + renderer.renderGuard(preCond) + ";" + "//" + guardToId.get(preCond).toString() ;
                classFileST.add("requireStmts", preAssert);
            }
            for (var postCond : post) {
                var preAssert = "assert " + renderer.renderGuard(postCond) + ";" + "//" + guardToId.get(postCond).toString() ;
                classFileST.add("postStmts", preAssert);
            }
            return classFileST.render();
        }
    }
}
