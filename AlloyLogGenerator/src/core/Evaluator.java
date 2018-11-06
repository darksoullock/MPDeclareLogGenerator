package core;

import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.codegen.NameEncoder;
import core.alloy.integration.AlloyComponent;
import core.alloy.serialization.AlloyLogExtractor;
import core.exceptions.BadSolutionException;
import core.exceptions.GenerationException;
import core.helpers.IOHelper;
import core.helpers.StatisticsHelper;
import core.interfaces.Function2;
import core.interfaces.Function3;
import core.models.AlloyRunConfiguration;
import core.models.serialization.trace.AbstractTraceAttribute;
import core.models.serialization.trace.EnumTraceAttributeImpl;
import core.models.serialization.trace.FloatTraceAttributeImpl;
import core.models.serialization.trace.IntTraceAttributeImpl;
import declare.DeclareModel;
import declare.DeclareParser;
import declare.DeclareParserException;
import declare.lang.trace.EnumTraceAttribute;
import declare.lang.trace.FloatTraceAttribute;
import declare.lang.trace.IntTraceAttribute;
import declare.validators.FunctionValidator;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.extension.XExtensionParser;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.model.impl.XAttributeMapImpl;
import org.deckfour.xes.model.impl.XLogImpl;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URI;
import java.time.Duration;
import java.time.LocalDate;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;

public class Evaluator {

    static int reuse = 1;

    private static AlloyRunConfiguration debugConf() {
        AlloyRunConfiguration conf = new AlloyRunConfiguration();
        conf.waitInputBeforeExit = false;
        conf.minLength = 40;
        conf.maxLength = 40;
        conf.nPositiveTraces = 10;
        //conf.nNegativeVacuousTraces = 10;
        conf.inFilename = "../data/bt_for_test_smv_data.decl";
        //conf.inFilename = "./data/loanApplication.decl";
        conf.shuffleStatementsIterations = 0;
        conf.evenLengthsDistribution = false;
        conf.intervalSplits = 1;
        conf.alsFilename = "../data/temp.als";
        conf.outFilename = "../data/" + LocalDate.now() + "-L" + conf.minLength + "-" + conf.maxLength + ".xes";
        return conf;
    }

    public static void main(String[] args) throws Exception {
        AlloyRunConfiguration config;
//        config = debugConf();
        config = CLI.getConfigFromArgs(args);

        if (config == null)
            return;

        if (config.function != null) {
            Global.log.accept(FunctionValidator.validate(config.function));
            return;
        }

        Global.underscore_spaces = config.underscore_spaces;

        try {
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

            addExtensions(plog);

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
            Global.log.accept("SUCCESS");
        } catch (Throwable e) {
            System.err.println(e);
        }

        if (config.waitInputBeforeExit) {
            Global.log.accept("press enter to close");
            System.in.read();
        }
    }

    private static void addExtensions(XLog log) {
        if (Global.noExtensions)
            return;

        try {
            log.getExtensions().add(XExtensionParser.instance().parse(new URI("http://www.xes-standard.org/lifecycle.xesext")));
            log.getExtensions().add(XExtensionParser.instance().parse(new URI("http://www.xes-standard.org/org.xesext")));
            log.getExtensions().add(XExtensionParser.instance().parse(new URI("http://www.xes-standard.org/time.xesext")));
            log.getExtensions().add(XExtensionParser.instance().parse(new URI("http://www.xes-standard.org/concept.xesext")));
            log.getExtensions().add(XExtensionParser.instance().parse(new URI("http://www.xes-standard.org/semantic.xesext")));
            log.getGlobalTraceAttributes().add(new XAttributeLiteralImpl("concept:name", "__INVALID__"));
            log.getGlobalEventAttributes().add(new XAttributeLiteralImpl("concept:name", "__INVALID__"));
            log.getAttributes().put("source", new XAttributeLiteralImpl("source", "DAlloy"));
            log.getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Artificial Log"));
            log.getAttributes().put("lifecycle:model", new XAttributeLiteralImpl("lifecycle:model", "standard"));
        } catch (Exception ex) {
            Global.log.accept("O-o-ops. Something happened, no log extensions will be written. Log itself is untouched");
            ex.printStackTrace();
        }
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

        DeclareParser parser = new DeclareParser();
        NameEncoder encoder = new NameEncoder(parser);
        if (Global.encodeNames)
            declare = encoder.encode(declare);
        DeclareModel model = parser.Parse(declare);
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth, maxSameInstances, vacuity, shuffleConstraints);
        gen.Run(model, negativeTraces, intervalSplits);

        String alloyCode = gen.getAlloyCode();
        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        Global.log.accept("Found Solution: " + (solution != null && solution.satisfiable()));

        AlloyLogExtractor ale = new AlloyLogExtractor(world, gen.generateNumericMap(), getTraceAttributesImpl(model),
                encoder.getEncoding(), start, duration);
        return ale.extract(solution, numberOfTraces, maxTraceLength, reuse);
    }

    private static List<AbstractTraceAttribute> getTraceAttributesImpl(DeclareModel model) {
        List<AbstractTraceAttribute> attributes = new ArrayList<>(model.getEnumTraceAttributes().size() + model.getIntTraceAttributes().size() + model.getFloatTraceAttributes().size());

        for (EnumTraceAttribute i : model.getEnumTraceAttributes()) {
            attributes.add(new EnumTraceAttributeImpl(i.getName(), i.getParams()));
        }

        for (IntTraceAttribute i : model.getIntTraceAttributes()) {
            attributes.add(new IntTraceAttributeImpl(i.getName(), i.getLow(), i.getHigh()));
        }

        for (FloatTraceAttribute i : model.getFloatTraceAttributes()) {
            attributes.add(new FloatTraceAttributeImpl(i.getName(), i.getLow(), i.getHigh()));
        }

        return attributes;
    }

    private static String GetDeclare(String file) {
        return IOHelper.readAllText(file);
    }
}
