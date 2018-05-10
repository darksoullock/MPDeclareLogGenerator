package core;

import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.Exceptions.GenerationException;
import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyLogExtractor;
import core.helpers.IOHelper;
import core.helpers.StatisticsHelper;
import core.interfaces.Function2;
import core.interfaces.Function3;
import core.models.AlloyRunConfiguration;
import declare.DeclareModel;
import declare.DeclareParser;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.model.impl.XAttributeMapImpl;
import org.deckfour.xes.model.impl.XLogImpl;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.IOException;
import java.time.Duration;
import java.time.LocalDate;
import java.time.LocalDateTime;

public class Evaluator {

    static int reuse = 1;

    private static AlloyRunConfiguration debugConf() {
        AlloyRunConfiguration conf = new AlloyRunConfiguration();
        conf.minLength = 7;
        conf.maxLength = 26;
        conf.nPositiveTraces = 5000;
        //conf.nNegativeVacuousTraces = 10;
        conf.inFilename = "./data/bt_nodata.decl";
        //conf.inFilename = "./data/loanApplication.decl";
        conf.shuffleStatementsIterations = 0;
        conf.evenLengthsDistribution = false;
        conf.intervalSplits = 1;
        conf.alsFilename = "./../data/temp.als";
        conf.outFilename = "./data/" + LocalDate.now() + "-L" + conf.minLength + "-" + conf.maxLength + ".xes";
        conf.saveSmv = false;
        if (conf.saveSmv)
            conf.outFilename = "./data/testSMV";
        return conf;
    }

    public static void main(String[] args) throws Exception {
        AlloyRunConfiguration config;
        config = debugConf();
        //config = CLI.getConfigFromArgs(args);

        if (config == null)
            return;

        if (config.saveSmv) {
            saveSmv(config);
            return;
        }

        long start = System.nanoTime();
        StatisticsHelper.time.add(start);
        String declare = GetDeclare(config.inFilename);

        XLog plog = getLog(
                config.minLength,
                config.maxLength,
                config.nPositiveTraces,
                config.nVacuousTraces,
                config.nNegativeTraces,
                config.nNegativeVacuousTraces,
                config.shuffleStatementsIterations,
                config.evenLengthsDistribution,
                config.maxSameInstances,
                config.intervalSplits,
                declare,
                config.alsFilename,
                LocalDateTime.now(),
                Duration.ofHours(4));

        for (int i = 0; i < plog.size(); ++i)
            plog.get(i).getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Case No. " + (i + 1)));


        Global.log.accept("Writing XES for: " + config.outFilename);
        Global.log.accept(plog.size() + "traces generated");
        FileOutputStream fileOS = new FileOutputStream(config.outFilename);
        new XesXmlSerializer().serialize(plog, fileOS);
        fileOS.close();

        long end = System.nanoTime();
        Global.log.accept(((end - start) / 1_000_000) + "");
        StatisticsHelper.print();
        System.out.println();
        //StatisticsHelper.printTime();
    }

    private static void saveSmv(AlloyRunConfiguration config) throws GenerationException, DeclareParserException, declare.DeclareParserException {
        DeclareModel model = new DeclareParser().Parse(IOHelper.readAllText(config.inFilename));
        SmvCodeGenerator a = new SmvCodeGenerator();
        a.run(model, config.minLength, config.shuffleStatementsIterations > 0);
        IOHelper.writeAllText(config.outFilename, a.getSmv());
        IOHelper.writeAllText(config.outFilename + ".db.json", a.getDataBindingJson());
    }

    public static XLog getLog(int minTraceLength,
                              int maxTraceLength,
                              int numberOfPositiveTracesWithoutVacuity,
                              int numberOfPositiveTracesWithVacuity,
                              int numberOfNegativeTracesWithoutVacuity,
                              int numberOfNegativeTracesWithVacuity,
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

        XLog log = createLog();
        log.addAll(getLogNow.invoke(false, false, numberOfPositiveTracesWithoutVacuity));
        log.addAll(getLogNow.invoke(true, false, numberOfPositiveTracesWithVacuity));
        log.addAll(getLogNow.invoke(false, true, numberOfNegativeTracesWithoutVacuity));
        log.addAll(getLogNow.invoke(true, true, numberOfNegativeTracesWithVacuity));
        return log;
    }

    private static XLog createLog() {
        return new XLogImpl(new XAttributeMapImpl());
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
            return createLog();

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
            throws Err, IOException, DeclareParserException, BadSolutionException, GenerationException {

        if (numberOfTraces == 0)
            return new XLogImpl(null);

        Global.log.accept("Maximum no of traces: " + numberOfTraces);

        int bitwidth = 5;

        DeclareParser parser = new DeclareParser(intervalSplits);
        DeclareModel model = parser.Parse(declare);
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth, maxSameInstances, vacuity, shuffleConstraints);
        gen.Run(model, negativeTraces);

        String alloyCode = gen.getAlloyCode();
        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        Global.log.accept("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyLogExtractor ale = new AlloyLogExtractor(world, gen.generateNumericMap(), model.getTraceAttributes(), parser.getNamesEncoding(), start, duration);
        return ale.extract(solution, numberOfTraces, maxTraceLength, reuse);
    }

    private static String GetDeclare(String file) throws FileNotFoundException {
        return IOHelper.readAllText(file);
    }
}
