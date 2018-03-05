package core;

import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyLogExtractor;
import core.helpers.IOHelper;
import core.helpers.StatisticsHelper;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.model.impl.XLogImpl;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.time.Duration;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.Random;

public class Evaluator {

    public static void main(String[] args) throws Exception {
        //setting default parameters
        /*
        should be 1 if 'same' or 'different' constraints
        not used or used at most once for any task.
        should be <=N if 'same'/'different' constraint
        used more than once and solution not found (or found few)
         */
        int intervalSplits = 2;
        int minLength = 0;
        int maxLength = 5;
        int nTraces = 500;
        String inFilename = "./data/sampleModel.decl";
        String alsFilename = "./data/temp.als";
        String outFilename = "./data/" + LocalDate.now() + "-L" + minLength + "-" + maxLength + "-T";

        if (args.length > 4) {
            minLength = Integer.parseInt(args[0]);
            maxLength = Integer.parseInt(args[1]);
            nTraces = Integer.parseInt(args[2]);
            inFilename = args[3];
            outFilename = args[4];
        } else {
            System.out.println("usage: java -jar AlloyToLog.jar minLength maxLength NTraces input output");
        }

        long start = System.nanoTime();
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

    public static XLog getLogWithNoise(int maxTraceLength,
                                       int minTraceLength,
                                       int numberOfPositiveTracesWithoutVacuity,
                                       int numberOfPositiveTracesWithVacuity,
                                       int numberOfNegativeTraces,
                                       int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                                       String declare,
                                       String alsFilename,
                                       int intervalSplits,
                                       LocalDateTime start,
                                       Duration duration)
            throws Err, IOException, DeclareParserException, BadSolutionException {

        XLog positive = getLog(maxTraceLength, minTraceLength, numberOfPositiveTracesWithVacuity, maxSameInstances, declare, alsFilename, intervalSplits, true, false, start, duration);
        XLog positiveV = getLog(maxTraceLength, minTraceLength, numberOfPositiveTracesWithoutVacuity, maxSameInstances, declare, alsFilename, intervalSplits, false, false, start, duration);
        XLog negative = getLog(maxTraceLength, minTraceLength, numberOfNegativeTraces, maxSameInstances, declare, alsFilename, intervalSplits, false, true, start, duration);
        return shuffle(positive, positiveV, negative);
    }

    public static XLog shuffle(XLog positive, XLog positiveV, XLog negative) {
        int n = positive.size() + positiveV.size() + negative.size();
        int i = positive.size();
        int j = positiveV.size();
        int k = negative.size();
        Random rnd = new Random();
        XLog result = new XLogImpl(positive.getAttributes());
        while (i + j + k > 0) {
            int val = rnd.nextInt(n);
            if (i > 0 && (val < positive.size() || j == 0 && k == 0))
                result.add(positive.get(--i));
            else if (j > 0 && (val < positive.size() + positiveV.size() || k == 0))
                result.add(positiveV.get(--j));
            else
                result.add(negative.get(--k));
        }

        for (i = 0; i < n; ++i)
            result.get(i).getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Case No. " + (i + 1)));

        return result;
    }

    public static XLog getLogEvenTraceLengthDistribution(int maxTraceLength,
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
        int n = numberOfTraces / (maxTraceLength - minTraceLength + 1);
        XLog log = getLog(maxTraceLength, maxTraceLength, n, maxSameInstances, declare, alsFilename, intervalSplits, vacuity, negativeTraces, start, duration);
        for (int i = minTraceLength; i < maxTraceLength; ++i) {
            Global.log.accept("\ngeneration for length " + i);
            XLog log2 = getLog(i, i, n, maxSameInstances, declare, alsFilename, intervalSplits, vacuity, negativeTraces, start, duration);
            log.addAll(log2);
        }

        return log;
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
