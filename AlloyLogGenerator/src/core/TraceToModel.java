package core;

import core.helpers.RandomHelper;
import declare.DeclareModel;
import declare.lang.Activity;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;
import org.apache.commons.lang3.tuple.Pair;
import org.deckfour.xes.model.*;
import org.deckfour.xes.model.impl.XAttributeContinuousImpl;
import org.deckfour.xes.model.impl.XAttributeDiscreteImpl;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.model.impl.XAttributeMapImpl;

import java.util.*;
import java.util.stream.Collectors;

public class TraceToModel {

    private Map<String, String> nameToCode = new HashMap<>();
    private Map<String, String> codeToName = new HashMap<>();

    public Map<String, String> getNameToCode() {
        return nameToCode;
    }

    public Map<String, String> getCodeToName() {
        return codeToName;
    }

    public DeclareModel parseLog(XLog log) {

        encodeNames(log);

        DeclareModel model = new DeclareModel();
        Map<String, Set<String>> edata = new HashMap<>();
        Map<String, Pair<Integer, Integer>> idata = new HashMap<>();
        Map<String, Pair<Float, Float>> fdata = new HashMap<>();

        for (XTrace trace : log) {
            for (XEvent event : trace) {
                String name = ((XAttributeLiteralImpl) event.getAttributes().get("concept:name")).getValue();

                model.getActivities().add(new Activity(name));

                for (XAttribute attribute : event.getAttributes().values()) {
                    String attributeName = attribute.getKey();
                    if (standardAttribute(attributeName)) {
                        continue;
                    }

                    model.getActivityToData().computeIfAbsent(name, k -> new HashSet<>());
                    model.getActivityToData().get(name).add(attributeName);
                    model.getDataToActivity().computeIfAbsent(attributeName, k -> new HashSet<>());
                    model.getDataToActivity().get(attributeName).add(name);

                    if (attribute instanceof XAttributeLiteralImpl) {
                        edata.computeIfAbsent(attributeName, k -> new HashSet<>());
                        String attributeValue = ((XAttributeLiteralImpl) attribute).getValue();
                        edata.get(attributeName).add(attributeValue);
                    }

                    if (attribute instanceof XAttributeDiscreteImpl) {
                        updateNumericData(idata, attributeName, (int) ((XAttributeDiscreteImpl) attribute).getValue());
                    }

                    if (attribute instanceof XAttributeContinuousImpl) {
                        updateNumericData(fdata, attributeName, (float) ((XAttributeContinuousImpl) attribute).getValue());
                    }
                }
            }
        }

        model.getEnumeratedData().addAll(edata.entrySet().stream().map(i -> new EnumeratedData(i.getKey(), new ArrayList<>(i.getValue()))).collect(Collectors.toList()));
        model.getIntegerData().addAll(idata.entrySet().stream().map(i -> new IntegerData(i.getKey(), i.getValue().getLeft() - 1, i.getValue().getRight() + 1)).collect(Collectors.toList()));
        model.getFloatData().addAll(fdata.entrySet().stream().map(i -> new FloatData(i.getKey(), i.getValue().getLeft() - 1, i.getValue().getRight() + 1)).collect(Collectors.toList()));

        return model;
    }

    private void encodeNames(XLog log) {
        for (XTrace trace : log) {
            for (XEvent event : trace) {
                XAttributeMap encAtt = new XAttributeMapImpl();

                String name = ((XAttributeLiteralImpl) event.getAttributes().get("concept:name")).getValue();
                codeToName.put(nameToCode.computeIfAbsent(name, i -> RandomHelper.getName()), name);
                XAttributeLiteralImpl nameAttribute = (XAttributeLiteralImpl) event.getAttributes().get("concept:name");
                nameAttribute.setValue(nameToCode.get(name));
                encAtt.put("concept:name", nameAttribute);

                for (XAttribute attribute : event.getAttributes().values()) {
                    if (standardAttribute(attribute.getKey()))
                        continue;

                    codeToName.put(nameToCode.computeIfAbsent(attribute.getKey(), i -> RandomHelper.getName()), attribute.getKey());
                    if (attribute instanceof XAttributeLiteralImpl) {
                        String value = ((XAttributeLiteralImpl) attribute).getValue();
                        codeToName.put(nameToCode.computeIfAbsent(value, i -> RandomHelper.getName()), value);
                        ((XAttributeLiteralImpl) attribute).setValue(nameToCode.get(value));
                    }

                    String aname = nameToCode.get(attribute.getKey());
                    if (attribute instanceof XAttributeLiteralImpl) {
                        encAtt.put(aname, new XAttributeLiteralImpl(aname, ((XAttributeLiteralImpl) attribute).getValue()));
                    }
                    if (attribute instanceof XAttributeLiteralImpl) {
                        encAtt.put(aname, new XAttributeLiteralImpl(aname, ((XAttributeLiteralImpl) attribute).getValue()));
                    }
                    if (attribute instanceof XAttributeDiscreteImpl) {
                        encAtt.put(aname, new XAttributeDiscreteImpl(aname, ((XAttributeDiscreteImpl) attribute).getValue()));
                    }
                }

                event.setAttributes(encAtt);
            }
        }
    }

    private <T extends Comparable> void updateNumericData(Map<String, Pair<T, T>> data, String key, T value) {
        Pair<T, T> minmax = data.get(key);
        if (minmax == null) {
            minmax = Pair.of(value, value);
            data.put(key, minmax);
        } else if (value.compareTo(minmax.getLeft()) < 0) {
            minmax = Pair.of(value, minmax.getRight());
            data.put(key, minmax);
        } else if (value.compareTo(minmax.getRight()) > 0) {
            minmax = Pair.of(minmax.getLeft(), value);
            data.put(key, minmax);
        }
    }

    private boolean standardAttribute(String key) {
        return "concept:name".equals(key) || "lifecycle:transition".equals(key) || "time:timestamp".equals(key);
    }
}
