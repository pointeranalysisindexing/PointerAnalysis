package experiments;

import indexing.PointerFlowGraph;

import java.io.File;
import java.io.IOException;

public class DacapoRunner {

    //static String[] benchmarks = new String[] {"antlr", "bloat", "chart", "eclipse", "fop", "jython", "pmd"};
    static String[] benchmarks = new String[] {"antlr"};
    static int NUMBER_OF_ITERATIONS = 1;

    public static void main(String[] args) throws IOException {

        String classPath = "dacapo\\";
        String outputPath = "dacapoOutput\\IndexingGraphCS";
        System.out.println("classpath ::"+classPath);
        System.out.println("outputPath ::"+outputPath);
        String CS = "0"; //to run the context-sensitive analysis
        String FS = "1"; //to run the field-sensitive analysis
        String other = "2"; //to just build the points-to graph and get statistics without CS or FS analysis

        String javaHome = System.getProperty("java.home");
        String javaBin = javaHome + File.separator + "bin" + File.separator + "java";
        for (int i = 0; i < NUMBER_OF_ITERATIONS; i++) {
            for (String bench : benchmarks) {
                ProcessBuilder processBuilder = new ProcessBuilder(
                        new String[]{javaBin, "-Xmx12g", "-Xss164m", "-cp", System.getProperty("java.class.path"),
                                PointerFlowGraph.class.getName(), classPath + bench, CS, bench, outputPath + "\\" + bench, String.valueOf(i)});
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
}
