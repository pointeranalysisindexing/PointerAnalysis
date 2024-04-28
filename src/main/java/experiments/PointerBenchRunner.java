package experiments;

import indexing.PointerFlowGraph;

import java.io.File;
import java.io.IOException;

public class PointerBenchRunner {
    /*static String[] benchmarks = new String[] {"Branching1", "Interprocedural1", "Interprocedural2", "Loops1", "Loops2", "Parameter1", "Parameter2",
            "Recursion1", "ReturnValue1", "ReturnValue2", "ReturnValue3","SimpleAlias1"};

    static String[] benchmarks = new String[] {"AccessPath1", "ContextSensitivity1", "ContextSensitivity2", "ContextSensitivity3",
            "FieldSensitivity1", "FieldSensitivity2", "FlowSensitivity1", "ObjectSensitivity1",
            "ObjectSensitivity2", "StrongUpdate1", "StrongUpdate2"};*/

    static String[] benchmarks = new String[] {"Branching1", "Interprocedural1", "Interprocedural2", "Loops1", "Loops2", "Parameter1", "Parameter2",
            "Recursion1", "ReturnValue1", "ReturnValue2", "ReturnValue3","SimpleAlias1"};

    static int NUMBER_OF_ITERATIONS = 0;

    public static void main(String[] args) {
        String classPath = "PointerBench-develop\\src\\basicJars";
        String outputPath = "pointerBenchOutput\\basic";
        System.out.println("classpath ::"+outputPath);
        System.out.println("outputPath ::"+classPath);
        String CS = "0"; //to run the context-sensitive analysis
        String FS = "1"; //to run the field-sensitive analysis
        String other = "2"; //to just build the points-to graph and get statistics without CS or FS analysis
        String javaHome = System.getProperty("java.home");
        String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
        for (String bench : benchmarks) {
            ProcessBuilder processBuilder =new ProcessBuilder(
                    new String[]{javaBin, "-Xmx16g", "-Xss164m", "-cp", System.getProperty("java.class.path"),
                            PointerFlowGraph.class.getName(), classPath, CS, bench, outputPath, String.valueOf(NUMBER_OF_ITERATIONS)});
            processBuilder.inheritIO();
            Process process;
            try {
                process = processBuilder.start();
                process.waitFor();
            } catch (IOException | InterruptedException e) {
                e.printStackTrace();
            }
        }
    }
}

