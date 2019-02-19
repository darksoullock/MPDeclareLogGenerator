package core;

import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.codegen.NameEncoder;
import core.alloy.integration.AlloyComponent;
import core.alloy.integration.QueryExtractor;
import core.alloy.serialization.AlloyLogExtractor;
import core.exceptions.BadSolutionException;
import core.exceptions.GenerationException;
import core.helpers.IOHelper;
import core.helpers.StatisticsHelper;
import core.models.AlloyRunConfiguration;
import core.models.query.AggregationState;
import core.models.query.QueryEvent;
import core.models.query.QueryState;
import core.models.query.TraceQueryResults;
import core.models.serialization.trace.AbstractTraceAttribute;
import core.models.serialization.trace.EnumTraceAttributeImpl;
import core.models.serialization.trace.FloatTraceAttributeImpl;
import core.models.serialization.trace.IntTraceAttributeImpl;
import declare.DeclareModel;
import declare.DeclareParser;
import declare.DeclareParserException;
import declare.lang.Statement;
import declare.lang.trace.EnumTraceAttribute;
import declare.lang.trace.FloatTraceAttribute;
import declare.lang.trace.IntTraceAttribute;
import declare.validators.FunctionValidator;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.apache.commons.lang3.tuple.Pair;
import org.deckfour.xes.extension.XExtensionParser;
import org.deckfour.xes.in.XesXmlParser;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.model.impl.XLogImpl;
import org.deckfour.xes.out.XesXmlSerializer;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URI;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.*;
import java.util.stream.Collectors;

import static core.models.AlloyRunConfiguration.ExecutionMode;

public class Evaluator {

    private static int reuse = 1;

    private static final boolean testMode = true;

    private static AlloyRunConfiguration debugConf() {
        AlloyRunConfiguration conf = new AlloyRunConfiguration();
        conf.waitInputBeforeExit = false;
        conf.minLength = 10;
        conf.maxLength = 10;
        conf.nPositiveTraces = 10;
        //conf.nNegativeVacuousTraces = 10;
        conf.modelFilename = "../data/query.decl";
        //conf.modelFilename = "./data/loanApplication.decl";
        conf.shuffleStatementsIterations = 0;
        conf.evenLengthsDistribution = false;
        conf.intervalSplits = 1;
        conf.alsFilename = "../data/temp.als";
        conf.logFilename = "../data/Sepsis Cases - Event Log.xes";
//        conf.logFilename = "../data/" + LocalDate.now() + "-L" + conf.minLength + "-" + conf.maxLength + ".xes";
        conf.mode = ExecutionMode.QUERY;
        return conf;
    }

    public static void main(String[] args) throws Exception {
        AlloyRunConfiguration config = resolveConfig(args);
        if (config == null) return;

        if (config.mode == ExecutionMode.GENERATION) {
            try {
                long start = System.nanoTime();
                StatisticsHelper.time.add(start);
                String declare = GetDeclare(config.modelFilename);

                XLog plog = AssemblyGenerationModes.getLog(
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
                        Duration.ofHours(4),
                        Evaluator::getLogSingleRun);

                writeTracesAsLogFile(config, plog);

                long end = System.nanoTime();
                Global.log.accept("total time (ms): " + ((end - start) / 1_000_000));

            } catch (Throwable e) {
                e.printStackTrace();
            }

            if (config.waitInputBeforeExit) {
                Global.log.accept("press enter to close");
                System.in.read();
            }

        } else if (config.mode == ExecutionMode.FUNCTION_VALIDATION) {
            Global.log.accept(FunctionValidator.validate(config.function));
        } else if (config.mode == ExecutionMode.COMPLIANCE_CHECK) {
            XLog log = readTracesFromLogFile(config.logFilename);
            String declare = GetDeclare(config.modelFilename);

            List<Statement>[] results = new List[log.size()];
            int i = 0;
            for (XTrace trace : log) {
                results[i] = Evaluator.checkCompliace(
                        config.maxLength,
                        declare,
                        config.alsFilename,
                        false,
                        trace);
                ++i;
            }

            i = 0;
            Global.log.accept("\n------------------");
            for (List<Statement> violations : results) {
                ++i;
                if (violations.isEmpty()) {
                    Global.log.accept(i + ": ok");
                } else {
                    Global.log.accept(i + ": violated\n" + String.join("\n", violations.stream().map(x -> " at line " + x.getLine() + ": " + x.getCode()).collect(Collectors.toList())));
                }

                Global.log.accept("");
            }


        } else if (config.mode == ExecutionMode.QUERY) {
            XLog log = readTracesFromLogFile(config.logFilename);
            String declare = GetDeclare(config.modelFilename);

            List<TraceQueryResults> allStates = queryLog(declare, config.alsFilename, false, log);
            Map<QueryState, AggregationState> aggregatedData = aggregate(allStates, 0, 0);

            double traceCount = allStates.size();
            Global.log.accept("Found: " + aggregatedData.size());
            for (Map.Entry<QueryState, AggregationState> state : aggregatedData.entrySet()) {
                Global.log.accept("\n accuracy: " + state.getValue().count / traceCount + "; vacuous: " + state.getValue().vacuousCount / traceCount);
                for (QueryEvent r : state.getKey().getTemplateValuesMap().values()) {
                    Global.log.accept(r.toString());
                }
            }


        } else {
            Global.log.accept("Unknown execution mode");
        }
    }

    private static Map<QueryState, AggregationState> aggregate(List<TraceQueryResults> allStates, double threshold, double vacuousThreshold) {
        Map<QueryState, AggregationState> a = new HashMap<>();
        for (TraceQueryResults traceState : allStates) {
            for (QueryState state : traceState.getStates()) {
                a.computeIfAbsent(state, i -> new AggregationState());
                AggregationState current = a.get(state);
                ++current.count;
                current.vacuousCount += state.getTemplateValuesMap().values().stream().anyMatch(QueryEvent::isVacuous) ? 1 : 0;
            }
        }

        double count = allStates.size();
        Set<QueryState> removeQ = new HashSet<>();
        for (Map.Entry<QueryState, AggregationState> entry : a.entrySet()) {
            if (entry.getValue().count / count < threshold || entry.getValue().vacuousCount / count < vacuousThreshold) {
                removeQ.add(entry.getKey());
            }
        }

        removeQ.forEach(a::remove);

        return a;
    }

    private static void writeTracesAsLogFile(AlloyRunConfiguration config, XLog plog) throws IOException {
        for (int i = 0; i < plog.size(); ++i)
            plog.get(i).getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Case No. " + (i + 1)));

        addExtensions(plog);

        Global.log.accept("Writing XES for: " + config.logFilename);
        Global.log.accept(plog.size() + "traces generated");
        FileOutputStream fileOS = new FileOutputStream(config.logFilename);
        new XesXmlSerializer().serialize(plog, fileOS);
        fileOS.close();

        StatisticsHelper.print();
        //StatisticsHelper.printTime();
        Global.log.accept("SUCCESS");
    }

    private static XLog readTracesFromLogFile(String filename) throws Exception {
        Global.log.accept("Reading XES from " + filename);
        FileInputStream fileIS = new FileInputStream(filename);
        List<XLog> log = new XesXmlParser().parse(fileIS);
        fileIS.close();
        return log.get(0);
    }

    private static AlloyRunConfiguration resolveConfig(String[] args) {
        AlloyRunConfiguration config;
        if (testMode)
            config = debugConf();
        else
            config = CLI.getConfigFromArgs(args);

        if (config == null)
            return null;

        Global.underscore_spaces = config.underscore_spaces;
        return config;
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


    public static XLog getLogSingleRun(int minTraceLength,
                                       int maxTraceLength,
                                       int numberOfTraces,
                                       int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                                       String declare,
                                       String alsFilename,
                                       int intervalSplits,  // minimum 1
                                       boolean vacuity,
                                       boolean negativeTraces,
                                       boolean shuffleConstraints,
                                       LocalDateTime start,
                                       Duration duration,
                                       XTrace trace)
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
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, minTraceLength, bitwidth, maxSameInstances, vacuity, shuffleConstraints, true);
        gen.Run(model, negativeTraces, intervalSplits, trace);

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

    // returns List of violated statements
    public static List<Statement> checkCompliace(int maxTraceLength,
                                                 String declare,
                                                 String alsFilename,
                                                 boolean vacuity,
                                                 XTrace trace)
            throws Err, IOException, DeclareParserException, GenerationException {

        int bitwidth = 5;
        DeclareParser parser = new DeclareParser();
        DeclareModel model = parser.Parse(declare);
        AlloyCodeGenerator gen = new AlloyCodeGenerator(maxTraceLength, 0, bitwidth, 1, vacuity, false, false);
        gen.Run(model, false, 1, trace);

        String alloyCode = gen.getAlloyCode();
        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(maxTraceLength, bitwidth);

        List<Statement> violations = new ArrayList<>();
        if (solution != null && solution.satisfiable()) {
            for (Pair<Statement, String> constraint : gen.getAlloyConstraints()) {
                Object ok = solution.eval(world.parseOneExpressionFromString(constraint.getValue()));
                if (ok instanceof Boolean && !(Boolean) ok) {
                    violations.add(constraint.getKey());
                }
            }
        } else {
            Global.log.accept("Solution not found");
        }

        return violations;
    }

    public static List<TraceQueryResults> queryLog(String queryDeclare,
                                                 String alsFilename,
                                                 boolean vacuity,
                                                 XLog log)
            throws Err, DeclareParserException, GenerationException, IOException {

        LogToModel logToModel = new LogToModel();
        DeclareModel model = logToModel.parse(log);

        List<TraceQueryResults> allStates = new ArrayList<>();
        for (XTrace trace : log) {
            TraceQueryResults traceStates = Evaluator.queryTrace(
                    queryDeclare,
                    alsFilename,
                    vacuity,
                    trace,
                    model,
                    logToModel.getActivityNameToCode());

            allStates.add(traceStates);
        }

        allStates.stream().flatMap(i->i.getStates().stream()).flatMap(i -> i.getTemplateValuesMap().values().stream())
                .forEach(i -> i.decode(logToModel.getCodeToName()));

        return allStates;
    }

    public static TraceQueryResults queryTrace(String queryDeclare,
                                             String alsFilename,
                                             boolean vacuity,
                                             XTrace trace,
                                             DeclareModel model,
                                             Map<String, String> nameToCode)
            throws Err, DeclareParserException, GenerationException, IOException {

        int bitwidth = 5;
        DeclareParser parser = new DeclareParser();
        DeclareModel qModel = parser.Parse(queryDeclare);
        if (!(qModel.getActivities().isEmpty() && qModel.getEnumeratedData().isEmpty() &&
                qModel.getIntegerData().isEmpty() && qModel.getFloatData().isEmpty())) {
            Global.log.accept("Warning: Activity and data definitions in query templates will be ignored");
        }

        QueryBuider qb = new QueryBuider(nameToCode);
        model.setConstraints(qModel.getConstraints());
        model.setDataConstraints(qModel.getDataConstraints());
        qb.extractQueryParams(model.getConstraints());
        qb.extractQueryParams(model.getDataConstraints());


        AlloyCodeGenerator gen = new AlloyCodeGenerator(trace.size(), 0, bitwidth, 0, vacuity, false, true);
        gen.Run(model, false, 1, trace);
        gen.generateQueryPlaceholder(qb.getParamEncoding(), qb.getDataParams());
        gen.generateDataBindingForQuerying(model.getActivityToData(), model.getDataToActivity());

        String alloyCode = gen.getAlloyCode();
        IOHelper.writeAllText(alsFilename, alloyCode);

        AlloyComponent alloy = new AlloyComponent();
        Module world = alloy.parse(alsFilename);
        A4Solution solution = alloy.executeFromFile(trace.size(), bitwidth);

        QueryExtractor extractor = new QueryExtractor();
        Set<QueryState> qlist = extractor.get(solution, world, qb.getParamEncoding(), qb.getDataParams(), 1000);

        Global.log.accept("\n");

        String name = ((XAttributeLiteralImpl)trace.getAttributes().get("concept:name")).getValue();
        return new TraceQueryResults(name, qlist);
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
