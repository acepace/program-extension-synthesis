package jminor;

import bgu.cs.util.Timer;
import jminor.analyser.DafnyAnalyser;
import jminor.ast.ASTProblem;
import jminor.ast.JminorParser;
import jminor.ast.ProblemCompiler;
import jminor.codegen.AutomatonCodegen;
import org.apache.commons.configuration2.Configuration;
import org.apache.commons.configuration2.builder.fluent.Configurations;
import org.apache.commons.configuration2.ex.ConfigurationException;
import pexyn.PETISynthesizer;
import pexyn.StructuredSemantics;
import pexyn.generalization.AutomatonToStructuredCmd;
import pexyn.planning.AStar;

import java.io.File;
import java.io.IOException;
import java.util.logging.FileHandler;
import java.util.logging.Logger;
import java.util.logging.SimpleFormatter;

/**
 * Synthesizes programs from a heap-format specification file.
 *
 * @author romanm
 */
public class Main {
    protected final Logger logger = Logger.getLogger(Logger.GLOBAL_LOGGER_NAME);

    private static final String OUTPUT_DIR_KEY = "pexyn.outputDir";
    private static final String PROPERTIES_FILE_NAME = "pexyn.properties";

    private String outputDirPath = null;

    private final Timer synthesisTime = new Timer();
    private final Timer planningTime = new Timer();

    private File logFile = null;
    private String logFilePath = null;

    private JminorDebugger debugger = null;

    private Configuration config = null;

    private final String filename;

    public Main(String filename) {
        this.filename = filename;
    }

    public static void main(String[] args) {
        if (args.length != 1) {
            throw new Error("Expected a file name!");
        }
        String filename = args[0];
        Main main = new Main(filename);
        main.run();
    }

    public JminorProblem genProblem() {
        JminorParser parser = new JminorParser();
        ASTProblem root = null;
        try {
            System.out.print("Parsing " + filename + "... ");
            root = parser.parseFile(filename);
            System.out.println("done");
        } catch (Exception e) {
            throw new Error(e.getMessage());
        }
        System.out.print("Compiling... ");
        ProblemCompiler compiler = new ProblemCompiler(root);
        JminorProblem problem = compiler.compile();
        System.out.println("done");
        return problem;
    }

    /**
     * Starts the ball rolling.
     */
    public void run() {
        var configs = new Configurations();
        try {
            config = configs.properties(new File(PROPERTIES_FILE_NAME));
            outputDirPath = config.getString(OUTPUT_DIR_KEY, "./");
            var dir = new File(outputDirPath);
            outputDirPath = dir.getAbsolutePath();
            dir.mkdirs();
        } catch (ConfigurationException cex) {
            logger.severe("Initialization failed: unable to load " + PROPERTIES_FILE_NAME + "!");
            return;
        }

        setOutputDirectory();
        debugger = new JminorDebugger(config, logger, filename, outputDirPath);
        logger.info("Synthesizer: started");
        synthesisTime.reset();
        planningTime.reset();
        try {
            var problem = genProblem();
            debugger.addLink(logFile.getName(), "Events log");
            debugger.addCodeFile("problem.txt", problem.toString(), "Specification");
            debugger.printExamples(problem.examples);
            synthesisTime.start();
            var planner = new AStar<>(new BasicJminorTR(problem.semantics));
            var synthesizer = new PETISynthesizer<>(planner, config, debugger);
            var synthesisResult = synthesizer.synthesize(problem);
            if (synthesisResult.success()) {
                debugger.info("PETI: found program automaton!");
                // We have to structure _after_ testing against the test examples,
                // since currently a command sequence is counted as an atomic
                // command, which fails the tests.
                var automaton = synthesisResult.get();
                //analysis before compression because then we lose the data
                if (config.getBoolean("pexyn.collectAssertions", false)) {
                    var analyser = new DafnyAnalyser(problem, synthesizer, automaton, config, debugger, DafnyAnalyser.GuardSource.ALL_CONDITIONS);
                    analyser.analyseAutomaton();
                    automaton = analyser.getGuardedAutomaton();
                }
                String safeAutomaton = automaton.toStringWithAsserts();
                logger.info(safeAutomaton);
                if (config.getBoolean("pexyn.structureResultAutomaton", false)) {
                    new AutomatonToStructuredCmd<>(
                            (StructuredSemantics<JmStore, Stmt, BoolExpr>) problem.semantics()).compress(automaton);
                    debugger.printAutomaton(automaton, "Compressed automaton");
                }


                if (config.getBoolean("jminor.generateJavaImplementation", true)) {
                    var backend = AutomatonCodegen.forJava(automaton, problem, config, debugger, logger);
                    backend.generate();
                }
                if (config.getBoolean("jminor.generateDafnyImplementation", true)) {
                    var backend = AutomatonCodegen.forDafny(automaton, problem, config, debugger, logger);
                    backend.generate();
                }

            } else {
                debugger.warning("PETI: failed to find program automaton!");
            }
        } catch (Throwable t) {
            debugger.severe(t.toString());
            t.printStackTrace();
        } finally {
            synthesisTime.stop();
            debugger.info("Planning time: " + planningTime.toSeconds());
            debugger.info("Synthesizer: done! (" + synthesisTime.toSeconds() + ")");
            debugger.refresh();
        }
    }

    private void setOutputDirectory() {
        var outputDirProp = config.getString("pexyn.outputDir", "output");
        var outputDirFile = new File(outputDirProp);
        outputDirFile.mkdir();
        String outputDirPath;
        try {
            outputDirPath = outputDirFile.getCanonicalPath();
            config.setProperty(OUTPUT_DIR_KEY, outputDirPath);
        } catch (IOException e) {
            logger.severe(
                    "Unable to set up output directory: " + outputDirFile.getName() + " (" + e.getMessage() + ")");
        }
        setOutLogFile();
    }

    private void setOutLogFile() {
        try {
            logFile = new File(outputDirPath + File.separator + "log.txt");
            logFilePath = logFile.getCanonicalPath();
            FileHandler logFileHandler = new FileHandler(logFilePath);
            logFileHandler.setFormatter(new SimpleFormatter());
            logger.addHandler(logFileHandler);
        } catch (SecurityException | IOException e) {
            logger.severe("Unable to set log file: " + e.getMessage() + "!");
        }
    }
}