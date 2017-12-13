package core.alloy.serialization;

import core.Exceptions.BadSolutionException;
import core.Global;
import core.StatisticsHelper;
import core.TimestampGenerator;
import core.alloy.integration.AlloyPMSolutionBrowser;
import core.models.declare.data.NumericToken;
import core.models.intervals.Interval;
import core.models.serialization.EventAdapter;
import core.models.serialization.Payload;
import core.models.serialization.trace.AbstractTraceAttribute;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.extension.XExtensionParser;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.deckfour.xes.model.impl.*;

import java.io.IOException;
import java.net.URI;
import java.time.Duration;
import java.time.LocalDateTime;
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

    public XLog extract(A4Solution alloySolution, int nTraces, int l) throws IOException, Err, BadSolutionException {
        Global.log.accept("Serialization..");

        XLog plog = this.initLog();
        int t;
        for (t = 0; t < nTraces && alloySolution.satisfiable(); ++t) {
            resetIntervalCaches();
            AlloyPMSolutionBrowser browser = new AlloyPMSolutionBrowser(alloySolution, module, l);
            plog.add(composeTrace(browser, t));
            alloySolution = alloySolution.next();
            if (nTraces % (t + 1) == 0 || t % 100 == 0) {
                System.out.print("... " + (nTraces - t));
            }
        }

        return plog;
    }

    private void resetIntervalCaches() {
        for (Interval i : numericMap.values()) {
            i.resetCaches();
        }
    }

    private XLog initLog() {
        XLogImpl log = new XLogImpl(new XAttributeMapImpl());
        if (Global.noExtensions)
            return log;

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

        return log;
    }

    private XTrace composeTrace(AlloyPMSolutionBrowser browser, int number) throws Err, IOException, BadSolutionException {
        List<EventAdapter> orderedStateEvents = browser.orderPEvents();
        XTraceImpl oneTrace = new XTraceImpl(new XAttributeMapImpl());
        oneTrace.getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Case No. " + ++number));
        handleTraceAttributes(oneTrace);

        StatisticsHelper.add((int) orderedStateEvents.stream().filter(Objects::nonNull).count());
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
            attributes.put("concept:name", new XAttributeLiteralImpl("concept:name", name));
            attributes.put("lifecycle:transition", new XAttributeLiteralImpl("lifecycle:transition", "complete"));
            attributes.put("time:timestamp", new XAttributeTimestampImpl("time:timestamp", oneStateEvent.getTimestamp()));
            handlePayload(oneStateEvent.getPayload(), attributes);
            XEventImpl oneEvent = new XEventImpl();
            oneEvent.setAttributes(attributes);
            oneTrace.insertOrdered(oneEvent);
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

            oneTrace.getAttributes().put(name, new XAttributeLiteralImpl(name, value));
        }
    }

    private void handlePayload(List<Payload> payloads, XAttributeMapImpl attributes) throws BadSolutionException {
        for (Payload p : payloads) {
            String dataKey = unqualifyLabel(p.getName());
            String dataValue = unqualifyLabel(p.getValue());
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

            attributes.put(dataKey, new XAttributeLiteralImpl(dataKey, dataValue));
        }
    }

    public String unqualifyLabel(String qualifiedLabel) {
        String result = qualifiedLabel;
        for (String moduleFileName : this.module.getAllReachableModulesFilenames()) {
            result = result.replace(moduleFileName + "/", "");
        }

        return result.replace("this/", "");
    }
}
