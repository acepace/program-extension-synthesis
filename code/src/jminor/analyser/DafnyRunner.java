package jminor.analyser;

import org.apache.commons.configuration2.Configuration;
import org.apache.commons.exec.CommandLine;
import org.apache.commons.exec.DefaultExecutor;
import org.apache.commons.exec.PumpStreamHandler;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.util.Arrays;

/**
 * This class is a wrapper around the Dafny compiler.
 * Using it we can pass in programs for Dafny to analyse and receive the results
 */
final class DafnyRunner {

    // We want to avoid irrelevent textual output. Also no need for generating executables.
    private static String[] commandLineFlags = new String[]{"/nologo", "/compile:0"};

    static String [] runDafny(Configuration config, String dafnyProgramPath) throws IOException {
        var path = config.getString("pexyn.dafnyPath");
        CommandLine cmdLine = new CommandLine(path);
        Arrays.stream(commandLineFlags).forEach(cmdLine::addArgument);
        cmdLine.addArgument(dafnyProgramPath);
        DefaultExecutor executor = new DefaultExecutor();
        ByteArrayOutputStream outputStream = new ByteArrayOutputStream();

        PumpStreamHandler streamHandler = new PumpStreamHandler(outputStream);
        executor.setStreamHandler(streamHandler);
        /*
            Dafny returns error codes for different analysis failures.
            To avoid our executor from complaining, I mask those codes.
         */
        executor.setExitValues(new int[]{0,1,2,3,4,5});

        int exitValue = executor.execute(cmdLine);
        if (exitValue == 0) {
            return new String[0];
        }
        String[] newLines = outputStream.toString().split("\n");

        return Arrays.stream(newLines).filter(line -> line.contains(dafnyProgramPath)).toArray(String[]::new);
    }



}
