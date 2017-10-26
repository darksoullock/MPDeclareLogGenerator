package core;

import com.sun.javaws.exceptions.InvalidArgumentException;
import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyXESSerializer;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import sun.plugin.dom.exception.InvalidStateException;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.time.LocalDate;

public class Evaluator {

    public static void main(String[] args) throws Exception {
        long start = System.nanoTime();

        int l = 20;
        int minl = 5;
        int ntrace = 30;
        String inFilename = "./data/example.decl";
        String alsFilename = "./data/temp.als";
        String outFilename = "./data/" + LocalDate.now() + "-L" + l + "-T";

        doStuff(l, minl, ntrace, inFilename, alsFilename, outFilename);

        long end = System.nanoTime();
        System.out.println((end - start) / 1_000_000);
    }

    private static void doStuff(int traceLength, int minTraceLength, int numberOfTraces, String inFilename, String alsFilename, String outFilename) throws Err, IOException, IllegalAccessException {
        System.out.println("Maximum no of traces: " + numberOfTraces);

        int bitwidth = Math.max((int) Math.ceil(Math.log((double) traceLength) / Math.log(2.0D)), 4);
        if ((traceLength- minTraceLength)>Math.pow(2,bitwidth-1)-1)
            throw new InvalidStateException("minimal trace length cannot be so low"); // it would be InvalidArgumentException if not it's stupid constructor with String[]

        String declare = GetDeclare(inFilename);
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

    private static String GetDeclare(String file) throws FileNotFoundException {
        return IOHelper.readAllText(new FileInputStream(file));
    }
}
