package core.alloy.serialization;

import core.exceptions.BadSolutionException;
import core.Global;
import core.TimestampGenerator;
import core.alloy.integration.AlloyPMSolutionBrowser;
import core.exceptions.GenerationException;
import core.helpers.StatisticsHelper;
import core.models.declare.data.NumericToken;
import core.models.intervals.FloatInterval;
import core.models.intervals.IntegerInterval;
import core.models.intervals.Interval;
import core.models.serialization.EventAdapter;
import core.models.serialization.Payload;
import core.models.serialization.trace.AbstractTraceAttribute;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.extension.XExtensionParser;
import org.deckfour.xes.model.XAttribute;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.deckfour.xes.model.impl.*;

import java.io.IOException;
import java.net.URI;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.stream.Collectors;

public class AlloyLogExtractor {
    private Module module;
    private Map<String, Interval> numericMap;
    private List<AbstractTraceAttribute> traceAttributes;
    private Map<String, String> nameEncoding;
    private TimestampGenerator timeGen;

    public AlloyLogExtractor(Module module,
                             Map<String, Interval> numericMap,
                             List<AbstractTraceAttribute> traceAttributes,
                             Map<String, String> nameEncoding,
                             LocalDateTime start,
                             Duration duration) {
        this.module = module;
        this.numericMap = numericMap;
        this.traceAttributes = traceAttributes;
        this.nameEncoding = nameEncoding;
        this.timeGen = new TimestampGenerator(start, duration);
    }

    public XLog extract(A4Solution alloySolution, int nTraces, int length, int reuseSolutionCount) throws IOException, Err, BadSolutionException {
        Global.log.accept("Serialization..");
        List<XTrace> plog = new ArrayList<>(nTraces * reuseSolutionCount);
        int t;
        for (t = 0; t < nTraces && alloySolution.satisfiable(); ++t) {
            AlloyPMSolutionBrowser browser = new AlloyPMSolutionBrowser(alloySolution, module, length);
            for (int i = 0; i < reuseSolutionCount; ++i) {
                resetIntervalCaches();
                plog.add(composeTrace(browser, t));
            }

            alloySolution = alloySolution.next();
            if (nTraces % (t + 1) == 0 || t % 100 == 0) {
                System.out.print("... " + (nTraces - t));
            }
        }

        XLog xlog = new XLogImpl(new XAttributeMapImpl());
        xlog.addAll(plog);
        return xlog;
    }

    private void resetIntervalCaches() {
        for (Interval i : numericMap.values()) {
            i.resetCaches();
        }
    }

    private XTrace composeTrace(AlloyPMSolutionBrowser browser, int number) throws Err, IOException, BadSolutionException {
        List<EventAdapter> orderedStateEvents = browser.orderPEvents();
        XTraceImpl oneTrace = new XTraceImpl(new XAttributeMapImpl());
        oneTrace.getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Case No. " + ++number));
        handleTraceAttributes(oneTrace);
        StatisticsHelper.addLength((int) orderedStateEvents.stream().filter(Objects::nonNull).count());
        StatisticsHelper.trace = number;
        equalizeSameTokens(orderedStateEvents);
        timeGen.setForTrace(orderedStateEvents);
        for (EventAdapter oneStateEvent : orderedStateEvents) {
            if (oneStateEvent == null)
                break;

            XAttributeMapImpl attributes = new XAttributeMapImpl();
            String name = unqualifyLabel(oneStateEvent.getActivityName());
            if (Global.encodeNames)
                name = nameEncoding.get(name);
            if (Global.underscore_spaces)
                name = name.replace("_", " ");
            attributes.put("concept:name", new XAttributeLiteralImpl("concept:name", name));
            attributes.put("lifecycle:transition", new XAttributeLiteralImpl("lifecycle:transition", "complete"));
            attributes.put("time:timestamp", new XAttributeTimestampImpl("time:timestamp", oneStateEvent.getTimestamp()));
            handlePayload(oneStateEvent.getPayload(), attributes);
            XEventImpl oneEvent = new XEventImpl();
            oneEvent.setAttributes(attributes);
            oneTrace.add(oneEvent);
        }

        return oneTrace;
    }

    /*
     * this function goes over all tasks and fill missing 'same' tokens
     * if we have A==B and B==C and C==D then
     * this function will also add A==C and A==D and B==D (in terms of matching pairs of tokens)
     */
    public void equalizeSameTokens(List<EventAdapter> orderedStateEvents) {
        for (EventAdapter oneStateEvent : orderedStateEvents)
            for (Payload p : oneStateEvent.getPayload())
                if (numericMap.containsKey(unqualifyLabel(p.getValue())) &&
                        p.getTokens().stream().filter(i -> i.getType() == NumericToken.Type.Same).count() > 1)
                    addSameSame(orderedStateEvents, p);
    }

    private void addSameSame(List<EventAdapter> orderedStateEvents, Payload p) {
        for (EventAdapter ite : orderedStateEvents)
            for (Payload ip : ite.getPayload())
                if (ip.getName().equals(p.getName()))
                    addIfMatch(p, ip);
    }

    private void addIfMatch(Payload from, Payload to) {
        if (from.getTokens().stream().anyMatch(t -> to.getTokens().contains(t)))
            for (NumericToken i : from.getTokens())
                to.getTokens().add(i);
    }

    private void handleTraceAttributes(XTraceImpl oneTrace) {
        for (AbstractTraceAttribute i : traceAttributes) {
            String name = i.getName();
            String value = i.getValue();
            if (Global.encodeNames) {
                name = nameEncoding.get(name);
                if (nameEncoding.containsKey(value))
                    value = nameEncoding.get(value);
            }
            if (Global.underscore_spaces) {
                name = name.replace("_", " ");
                value = value.replace("_", " ");
            }

            oneTrace.getAttributes().put(name, new XAttributeLiteralImpl(name, value));
        }
    }

    private void handlePayload(List<Payload> payloads, XAttributeMapImpl attributes) throws BadSolutionException {
        for (Payload p : payloads) {
            String dataKey = unqualifyLabel(p.getName());
            String dataValue = unqualifyLabel(p.getValue());
            String type = getPayloadTypeByValue(dataValue);
            if (numericMap.containsKey(dataValue)) {
                if (p.getTokens().isEmpty())
                    dataValue = numericMap.get(dataValue).get();
                else {
                    if (p.getTokens().stream().allMatch(i -> i.getType() == NumericToken.Type.Same))
                        dataValue = numericMap.get(dataValue).getSame(p.getTokens().stream().map(NumericToken::getValue).collect(Collectors.toList()));
                    else if (p.getTokens().stream().allMatch(i -> i.getType() == NumericToken.Type.Different))
                        dataValue = numericMap.get(dataValue).getDifferent(p.getTokens().stream().map(NumericToken::getValue).collect(Collectors.toList()));
                    else throw new BadSolutionException("Different token types within one variables (" +
                                String.join(", ", p.getTokens().stream().map(NumericToken::getValue).collect(Collectors.toList())) + ");");
                }
            } else if (Global.encodeNames) {
                dataValue = nameEncoding.get(dataValue);
            }

            if (Global.encodeNames)
                dataKey = nameEncoding.get(dataKey);

            if (Global.underscore_spaces) {
                dataKey = dataKey.replace("_", " ");
                dataValue = dataValue.replace("_", " ");
            }

            if (dataValue.length() > dataKey.length() && dataValue.charAt(dataKey.length()) == '.' && dataValue.startsWith(dataKey))
                dataValue = dataValue.substring(dataKey.length() + 1);
            attributes.put(dataKey, createXAttribute(type, dataKey, dataValue));
        }
    }

    private XAttribute createXAttribute(String type, String dataKey, String dataValue) {
        if ("int".equals(type))
            return new XAttributeDiscreteImpl(dataKey, Integer.parseInt(dataValue));
        if ("float".equals(type))
            return new XAttributeContinuousImpl(dataKey, Double.parseDouble(dataValue));
        return new XAttributeLiteralImpl(dataKey, dataValue);
    }

    private String getPayloadTypeByValue(String value) {
        if (numericMap.containsKey(value)) {
            Interval interval = numericMap.get(value);
            if (interval instanceof IntegerInterval)
                return "int";

            if (interval instanceof FloatInterval)
                return "float";
        }

        return "string";
    }

    public String unqualifyLabel(String qualifiedLabel) {
        String result = qualifiedLabel;
        for (String moduleFileName : this.module.getAllReachableModulesFilenames()) {
            result = result.replace(moduleFileName + "/", "");
        }

        return result.replace("this/", "");
    }
}
