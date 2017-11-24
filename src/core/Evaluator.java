package core;

import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyLogExtractor;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.*;
import java.time.LocalDate;

public class Evaluator {

    public static void main(String[] args) throws Exception {
        long start = System.nanoTime();

        /*
        should be 1 if 'same' or 'different' constraints
        not used or used at most once for any task.
        should be <=N if 'same'/'different' constraint
        used more than once and solution not found (or found few)
         */
        int intervalSplits = 2;
        int minLength = 13;
        int maxLength = 20;
        int nTraces = 100;
        String inFilename = "./data/example1.decl";
        String alsFilename = "./data/temp.als";
        String outFilename = "./data/" + LocalDate.now() + "-L" + minLength + "-" + maxLength + "-T";

        XLog plog = getLog(maxLength, minLength, nTraces, 4, GetDeclare(inFilename), alsFilename, intervalSplits, true);

        System.out.println();
        System.out.println("Writing XES for: " + outFilename + plog.size() + ".xes");
        FileOutputStream fileOS = new FileOutputStream(outFilename + plog.size() + ".xes");
        new XesXmlSerializer().serialize(plog, fileOS);

        long end = System.nanoTime();
        System.out.println((end - start) / 1_000_000);

        StatisticsHelper.print();
    }

    public static XLog getLog(int maxTraceLength,
                              int minTraceLength,
                              int numberOfTraces,
                              int maxSameInstances,
                              String declare,
                              String alsFilename,
                              int intervalSplits,
                              boolean vacuity)
            throws Err, IOException {

        System.out.println("Maximum no of traces: " + numberOfTraces);

        int bitwidth = 5;
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth, maxSameInstances, intervalSplits, vacuity);
        gen.Run(declare);
        String alloyCode = gen.getAlloyCode();

        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        System.out.println("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyLogExtractor serializer = new AlloyLogExtractor(world, gen.generateNumericMap(), gen.getTraceAttr(), gen.getNamesEncoding());
        return serializer.extract(solution, numberOfTraces, maxTraceLength);
    }

    private static String GetDeclare(String file) throws FileNotFoundException {
        return IOHelper.readAllText(file);
    }
}
