package core.alloy.serialization;

import core.StatisticsHelper;
import core.TimestampComposer;
import core.alloy.integration.AlloyPMSolutionBrowser;
import core.models.declare.data.NumericToken;
import core.models.intervals.Interval;
import core.models.serialization.Payload;
import core.models.serialization.TaskEventAdapter;
import core.models.serialization.trace.AbstractTraceAttribute;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import org.deckfour.xes.extension.XExtensionParser;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.deckfour.xes.model.impl.*;
import org.deckfour.xes.out.XesXmlSerializer;
import sun.plugin.dom.exception.InvalidStateException;

import java.io.FileOutputStream;
import java.io.IOException;
import java.net.URI;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class AlloyXESSerializer {
    private XesXmlSerializer xesXmlSerializer;
    private Module module;
    private Map<String, Interval> numericMap;
    List<AbstractTraceAttribute> traceAttributes;

    public AlloyXESSerializer(Module module, Map<String, Interval> numericMap, List<AbstractTraceAttribute> traceAttributes) {
        xesXmlSerializer = new XesXmlSerializer();
        this.module = module;
        this.numericMap = numericMap;
        this.traceAttributes = traceAttributes;
    }

    public void serialize(A4Solution alloySolution, int nTraces, String fileName, int l) throws IOException, Err, IllegalAccessException {
        System.out.println("Serialization..");

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

        System.out.println();
        System.out.println("Writing XES for: " + fileName + t + ".xes");
        FileOutputStream fileOS = new FileOutputStream(fileName + t + ".xes");
        xesXmlSerializer.serialize(plog, fileOS);
    }

    private void resetIntervalCaches() {
        for (Interval i : numericMap.values()) {
            i.resetCaches();
        }
    }

    private XLog initLog() {
        XLogImpl log = new XLogImpl(new XAttributeMapImpl());

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
            System.out.println("O-o-ops. Something happened, no log extensions will be written. Log itself is untouched");
            ex.printStackTrace();
        }

        return log;
    }

    private XTrace composeTrace(AlloyPMSolutionBrowser browser, int number) throws Err, IOException {
        List<TaskEventAdapter> orderedStateEvents = browser.orderPEvents();
        XTraceImpl oneTrace = new XTraceImpl(new XAttributeMapImpl());
        oneTrace.getAttributes().put("concept:name", new XAttributeLiteralImpl("concept:name", "Case No. " + ++number));
        handleTraceAttributes(oneTrace);

        StatisticsHelper.add((int) orderedStateEvents.stream().filter(i -> i != null).count());
        StatisticsHelper.trace = number;

        equalizeSameTokens(orderedStateEvents);
        for (TaskEventAdapter oneStateEvent : orderedStateEvents) {
            if (oneStateEvent == null)
                break;

            XAttributeMapImpl attributes = new XAttributeMapImpl();
            attributes.put("concept:name", new XAttributeLiteralImpl("concept:name", unqualifyLabel(oneStateEvent.getTaskName())));
            attributes.put("lifecycle:transition", new XAttributeLiteralImpl("lifecycle:transition", "complete"));
            attributes.put("time:timestamp", new XAttributeTimestampImpl("time:timestamp", TimestampComposer.composeForEvent(oneStateEvent.getPosition())));
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
    public void equalizeSameTokens(List<TaskEventAdapter> orderedStateEvents) {
        for (TaskEventAdapter oneStateEvent : orderedStateEvents)
            for (Payload p : oneStateEvent.getPayload())
                if (numericMap.containsKey(unqualifyLabel(p.getValue())) &&
                        p.getTokens().stream().filter(i -> i.getType() == NumericToken.Type.Same).count() > 1)
                    addSameSame(orderedStateEvents, p);
    }

    private void addSameSame(List<TaskEventAdapter> orderedStateEvents, Payload p) {
        for (TaskEventAdapter ite : orderedStateEvents)
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
            oneTrace.getAttributes().put(i.getName(), new XAttributeLiteralImpl(i.getName(), i.getValue()));
        }
    }

    private void handlePayload(List<Payload> payloads, XAttributeMapImpl attributes) {
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
                    else throw new InvalidStateException("Different token types within one variables (" +
                                String.join(", ", p.getTokens().stream().map(NumericToken::getValue).collect(Collectors.toList())) + ");");
                    //dataValue = dataValue + String.join(", ", p.getTokens().stream().map(NumericToken::getValue).collect(Collectors.toList()));
                }
            }

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
