package core;

import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyXESSerializer;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.time.LocalDate;

public class Evaluator {

    public static void main(String[] args) throws Exception {
        long start = System.nanoTime();

        int l = 20;
        int minl = 10;
        int ntrace = 30;
        String alsFilename = "./data/temp.als";
        String outFilename = "./data/" + LocalDate.now() + "-L" + l + "-T";

        doStuff(l, minl, ntrace, alsFilename, outFilename);

        long end = System.nanoTime();
        System.out.println((end - start) / 1_000_000);
    }

    private static void doStuff(int traceLength, int minTraceLength, int numberOfTraces, String alsFilename, String outFilename) throws Err, IOException, IllegalAccessException {
        System.out.println("Maximum no of traces: " + numberOfTraces);

        int bitwidth = (int) Math.ceil(Math.log((double) traceLength) / Math.log(2.0D));
        String declare = GetDeclare();
        AlloyCodeGenerator gen = new AlloyCodeGenerator(traceLength, minTraceLength, bitwidth);
        gen.Run(declare);
        String alloyCode = gen.getAlloyCode();

        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(traceLength, bitwidth);

        System.out.println("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyXESSerializer serializer = new AlloyXESSerializer(world, gen.generateNumericMap(), gen.getTraceAttr());
        serializer.serialize(solution, numberOfTraces, outFilename, traceLength);
    }

    private static String GetDeclare() throws FileNotFoundException {
        return IOHelper.readAllText(new FileInputStream("./data/example.decl"));
    }
}
