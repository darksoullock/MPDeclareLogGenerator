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

        int minLength = 7;
        int maxLength = 12;
        int nTraces = 30;
        String inFilename = "./data/example.decl";
        String alsFilename = "./data/temp.als";
        String outFilename = "./data/" + LocalDate.now() + "-L" + minLength + "-" + maxLength + "-T";

        doStuff(maxLength, minLength, nTraces, inFilename, alsFilename, outFilename);

        long end = System.nanoTime();
        System.out.println((end - start) / 1_000_000);

        StatisticsHelper.print();
    }

    private static void doStuff(int maxTraceLength, int minTraceLength, int numberOfTraces, String inFilename, String alsFilename, String outFilename) throws Err, IOException, IllegalAccessException {
        System.out.println("Maximum no of traces: " + numberOfTraces);

        int bitwidth = Math.max((int) Math.ceil(Math.log((double) maxTraceLength) / Math.log(2.0D)), 4);
        String declare = GetDeclare(inFilename);
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth);
        gen.Run(declare);
        String alloyCode = gen.getAlloyCode();

        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        System.out.println("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyXESSerializer serializer = new AlloyXESSerializer(world, gen.generateNumericMap(), gen.getTraceAttr());
        serializer.serialize(solution, numberOfTraces, outFilename, maxTraceLength);
    }

    private static String GetDeclare(String file) throws FileNotFoundException {
        return IOHelper.readAllText(new FileInputStream(file));
    }
}
