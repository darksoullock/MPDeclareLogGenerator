package core;

import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyLogExtractor;
import core.helpers.IOHelper;
import core.helpers.StatisticsHelper;
import core.interfaces.Function2;
import core.interfaces.Function3;
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

    static int reuse = 1;

    public static void main(String[] args) throws Exception {
        //setting default parameters
        /*
        should be 1 if 'same' or 'different' constraints
        not used or used at most once for any task.
        should be <=N if 'same'/'different' constraint
        used more than once and solution not found (or found few)
         */
        int intervalSplits = 1;
        int minLength = 5;
        int maxLength = 5;
        int nTraces = 1000;
        int maxSameInstances = 2;
        int shuffleConstraintsIterations = 0;
        boolean vacuity = false;
        boolean negativeTraces = false;
        boolean evenLengthsDistribution = false;

        //String inFilename = "./data/bt_for_test_smv_data.decl";
        String inFilename = "./data/loanApplication.decl";
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
        StatisticsHelper.time.add(start);
        String declare = GetDeclare(inFilename);

        XLog plog = getLog(
                minLength,
                maxLength,
                !(vacuity || negativeTraces) ? nTraces : 0, //positive non-vacuity traces
                vacuity ? nTraces : 0,
                negativeTraces ? nTraces : 0,
                shuffleConstraintsIterations,
                evenLengthsDistribution,
                maxSameInstances,
                intervalSplits,
                declare,
                alsFilename,
                LocalDateTime.now(),
                Duration.ofHours(4));

        Global.log.accept("Writing XES for: " + outFilename + plog.size() + ".xes");
        FileOutputStream fileOS = new FileOutputStream(outFilename + plog.size() + ".xes");
        new XesXmlSerializer().serialize(plog, fileOS);
        fileOS.close();

        long end = System.nanoTime();
        Global.log.accept(((end - start) / 1_000_000) + "");

        StatisticsHelper.print();

        System.out.println();
        //StatisticsHelper.printTime();
    }

    public static XLog getLog(int minTraceLength,
                              int maxTraceLength,
                              int numberOfPositiveTracesWithoutVacuity,
                              int numberOfPositiveTracesWithVacuity,
                              int numberOfNegativeTraces,
                              int shuffleConstraintsIterations, // If some constraints are rarely activated, different order (different priority) may fix this problem. value 0 means that order is as it is in input .decl file
                              boolean evenLengthsDistribution,
                              int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                              int intervalSplits,
                              String declare,
                              String alsFilename,
                              LocalDateTime start,
                              Duration duration)
            throws Exception {

        Function3<Boolean, Boolean, Integer, XLog> getLogNow;

        if (evenLengthsDistribution)
            getLogNow =
                    (vacuity2, negative, nTraces) -> getLogEvenTraceLengthDistribution(
                            minTraceLength,
                            maxTraceLength,
                            nTraces,
                            (length, amount) -> getLogFairConstraintsPriority(
                                    amount,
                                    shuffleConstraintsIterations,
                                    (amount2, shuffle) -> getLogSingleRun(
                                            length,
                                            length,
                                            amount2,
                                            maxSameInstances,
                                            declare,
                                            alsFilename,
                                            intervalSplits,
                                            vacuity2,
                                            negative,
                                            shuffle,
                                            start,
                                            duration)));
        else
            getLogNow =
                    (vacuity2, negative, nTraces) -> getLogFairConstraintsPriority(
                            nTraces,
                            shuffleConstraintsIterations,
                            (amount2, shuffle) -> getLogSingleRun(
                                    minTraceLength,
                                    maxTraceLength,
                                    amount2,
                                    maxSameInstances,
                                    declare,
                                    alsFilename,
                                    intervalSplits,
                                    vacuity2,
                                    negative,
                                    shuffle,
                                    start,
                                    duration));

        XLog positive = getLogNow.invoke(false, false, numberOfPositiveTracesWithoutVacuity);
        XLog positiveV = getLogNow.invoke(true, false, numberOfPositiveTracesWithVacuity);
        XLog negative = getLogNow.invoke(false, true, numberOfNegativeTraces);
        return merge(positive, positiveV, negative);
    }

    public static XLog merge(XLog positive, XLog positiveV, XLog negative) {
        if (!positive.isEmpty() && positiveV.isEmpty() && negative.isEmpty())
            return positive;

        if (positive.isEmpty() && !positiveV.isEmpty() && negative.isEmpty())
            return positiveV;

        if (positive.isEmpty() && positiveV.isEmpty() && !negative.isEmpty())
            return negative;

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

    public static XLog getLogEvenTraceLengthDistribution(int minTraceLength,
                                                         int maxTraceLength,
                                                         int numberOfTraces,
                                                         Function2<Integer, Integer, XLog> getLogForN)
            throws Exception {
        int n = numberOfTraces / (maxTraceLength - minTraceLength + 1);
        XLog log = getLogForN.invoke(maxTraceLength, n);
        StatisticsHelper.time.add(System.nanoTime());
        for (int i = minTraceLength; i < maxTraceLength; ++i) {
            Global.log.accept("\ngeneration for length " + i);
            XLog log2 = getLogForN.invoke(i, n);
            log.addAll(log2);
        }

        return log;
    }

    public static XLog getLogFairConstraintsPriority(
            int numberOfTraces,
            int shuffleConstraintsIterations,
            Function2<Integer, Boolean, XLog> getLog) // int N, bool shuffle
            throws Exception {

        if (numberOfTraces == 0)
            return new XLogImpl(null);

        int n = numberOfTraces;
        if (shuffleConstraintsIterations > 0)
            n /= shuffleConstraintsIterations;

        XLog log = getLog.invoke(n, shuffleConstraintsIterations > 0);
        for (int i = 1; i < shuffleConstraintsIterations; ++i) {
            Global.log.accept("\ngeneration step " + i);
            XLog log2 = getLog.invoke(n, true);
            log.addAll(log2);
        }

        return log;
    }

    public static XLog getLogSingleRun(int minTraceLength,
                                       int maxTraceLength,
                                       int numberOfTraces,
                                       int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                                       String declare,
                                       String alsFilename,
                                       int intervalSplits,
                                       boolean vacuity,
                                       boolean negativeTraces,
                                       boolean shuffleConstraints,
                                       LocalDateTime start,
                                       Duration duration)
            throws Err, IOException, DeclareParserException, BadSolutionException {

        if (numberOfTraces == 0)
            return new XLogImpl(null);

        Global.log.accept("Maximum no of traces: " + numberOfTraces);

        int bitwidth = 5;
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth, maxSameInstances, intervalSplits, vacuity, shuffleConstraints);
        gen.Run(declare, negativeTraces);

        String alloyCode = gen.getAlloyCode();
        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        Global.log.accept("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyLogExtractor ale = new AlloyLogExtractor(world, gen.generateNumericMap(), gen.getTraceAttr(), gen.getNamesEncoding(), start, duration);
        return ale.extract(solution, numberOfTraces, maxTraceLength, reuse);
    }

    private static String GetDeclare(String file) throws FileNotFoundException {
        return IOHelper.readAllText(file);
    }
}
