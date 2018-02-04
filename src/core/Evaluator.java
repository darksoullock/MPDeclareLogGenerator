package core;

import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyLogExtractor;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.time.Duration;
import java.time.LocalDate;
import java.time.LocalDateTime;

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
        int minLength = 38;
        int maxLength = 40;
        int nTraces = 10;
        String inFilename = "./data/bt_for_test_smv_data.decl";
        String alsFilename = "./data/temp.als";
        String outFilename = "./data/" + LocalDate.now() + "-L" + minLength + "-" + maxLength + "-T";

        XLog plog = getLog(
                maxLength,
                minLength,
                nTraces,
                2,
                GetDeclare(inFilename),
                alsFilename,
                intervalSplits,
                false,
                false,
                LocalDateTime.now(),
                Duration.ofHours(4));

        Global.log.accept("Writing XES for: " + outFilename + plog.size() + ".xes");
        FileOutputStream fileOS = new FileOutputStream(outFilename + plog.size() + ".xes");
        new XesXmlSerializer().serialize(plog, fileOS);
        fileOS.close();

        long end = System.nanoTime();
        Global.log.accept(((end - start) / 1_000_000) + "");

        StatisticsHelper.print();
    }

    public static XLog getLog(int maxTraceLength,
                              int minTraceLength,
                              int numberOfTraces,
                              int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                              String declare,
                              String alsFilename,
                              int intervalSplits,
                              boolean vacuity,
                              boolean negativeTraces,
                              LocalDateTime start,
                              Duration duration)
            throws Err, IOException, DeclareParserException, BadSolutionException {

        Global.log.accept("Maximum no of traces: " + numberOfTraces);

        int bitwidth = 5;
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth, maxSameInstances, intervalSplits, vacuity);
        gen.Run(declare, negativeTraces);

        String alloyCode = gen.getAlloyCode();
        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        Global.log.accept("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyLogExtractor ale = new AlloyLogExtractor(world, gen.generateNumericMap(), gen.getTraceAttr(), gen.getNamesEncoding(), start, duration);
        return ale.extract(solution, numberOfTraces, maxTraceLength);
    }

    private static String GetDeclare(String file) throws FileNotFoundException {
        return IOHelper.readAllText(file);
    }
}
