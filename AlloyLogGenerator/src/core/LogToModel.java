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

public class LogToModel {

    private Map<String, String> activityNameToCode = new HashMap<>();
    private Map<String, String> dataNameToCode = new HashMap<>();
    private Map<String, String> valueNameToCode = new HashMap<>();
    private Map<String, String> codeToName = new HashMap<>();

    public Map<String, String> getActivityNameToCode() {
        return activityNameToCode;
    }

    public Map<String, String> getCodeToName() {
        return codeToName;
    }

    public DeclareModel parse(XLog log) {

        encodeNames(log);

        DeclareModel model = new DeclareModel();
        Map<String, Set<String>> edata = new HashMap<>();
        Map<String, Pair<Integer, Integer>> idata = new HashMap<>();
        Map<String, Pair<Float, Float>> fdata = new HashMap<>();
        Map<String, Map<String, Boolean>> requiredMap = new HashMap<>();

        for (XTrace trace : log) {
            for (XEvent event : trace) {
                String name = ((XAttributeLiteralImpl) event.getAttributes().get("concept:name")).getValue();

                model.getActivities().add(new Activity(name));
                updateRequired(requiredMap, name, event.getAttributes().values());

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

        // whether data attribute is optional or required should be determined for each activity (in activity-data mapping)
        // because the same attribute can be bound to multiple activities
        // currently "required" property is temporarily in data attributes
        Map<String, Boolean> simpleRequiredMap = requiredMap.values().stream().flatMap(i -> i.entrySet().stream()).collect(Collectors.toMap(Map.Entry::getKey, Map.Entry::getValue, (i, j) -> i && j));
        model.getEnumeratedData().addAll(edata.entrySet().stream().map(i -> new EnumeratedData(i.getKey(), new ArrayList<>(i.getValue()), simpleRequiredMap.get(i.getKey()))).collect(Collectors.toList()));
        model.getIntegerData().addAll(idata.entrySet().stream().map(i -> new IntegerData(i.getKey(), i.getValue().getLeft() - 1, i.getValue().getRight() + 1, simpleRequiredMap.get(i.getKey()))).collect(Collectors.toList()));
        model.getFloatData().addAll(fdata.entrySet().stream().map(i -> new FloatData(i.getKey(), i.getValue().getLeft() - 1, i.getValue().getRight() + 1, simpleRequiredMap.get(i.getKey()))).collect(Collectors.toList()));

        return model;
    }

    private void updateRequired(Map<String, Map<String, Boolean>> requiredMap, String activity, Collection<XAttribute> attributes) {
        Set<String> attributeNames = attributes.stream().map(XAttribute::getKey).collect(Collectors.toSet());
        if (requiredMap.containsKey(activity)) {
            Map<String, Boolean> attributeMap = requiredMap.get(activity);

            for (String i : attributeNames)
                if (!attributeMap.containsKey(i))
                    attributeMap.put(i, false);

            for (String i : attributeMap.keySet())
                if (!attributeNames.contains(i))
                    attributeMap.put(i, false);

        } else {
            Map<String, Boolean> keys = new HashMap<>();
            attributeNames.forEach(i -> keys.put(i, true));
            requiredMap.put(activity, keys);
        }
    }

    private void encodeNames(XLog log) {
        for (XTrace trace : log) {
            for (XEvent event : trace) {
                XAttributeMap encAtt = new XAttributeMapImpl();

                String name = ((XAttributeLiteralImpl) event.getAttributes().get("concept:name")).getValue();
                codeToName.put(activityNameToCode.computeIfAbsent(name, i -> RandomHelper.getValidNameFor("activity", name)), name);
                XAttributeLiteralImpl nameAttribute = (XAttributeLiteralImpl) event.getAttributes().get("concept:name");
                nameAttribute.setValue(activityNameToCode.get(name));
                encAtt.put("concept:name", nameAttribute);

                for (XAttribute attribute : event.getAttributes().values()) {
                    if (standardAttribute(attribute.getKey()))
                        continue;

                    codeToName.put(dataNameToCode.computeIfAbsent(attribute.getKey(), i -> RandomHelper.getValidNameFor("data", attribute.getKey())), attribute.getKey());
                    if (attribute instanceof XAttributeLiteralImpl) {
                        String value = ((XAttributeLiteralImpl) attribute).getValue();
                        String key_value = attribute.getKey() + "_" + value;
                        codeToName.put(valueNameToCode.computeIfAbsent(key_value, i -> RandomHelper.getValidNameFor("val", key_value)), key_value);
                        ((XAttributeLiteralImpl) attribute).setValue(valueNameToCode.get(key_value));
                    }

                    String aname = dataNameToCode.get(attribute.getKey());
                    if (attribute instanceof XAttributeLiteralImpl) {
                        encAtt.put(aname, new XAttributeLiteralImpl(aname, ((XAttributeLiteralImpl) attribute).getValue()));
                    }
                    if (attribute instanceof XAttributeDiscreteImpl) {
                        encAtt.put(aname, new XAttributeDiscreteImpl(aname, ((XAttributeDiscreteImpl) attribute).getValue()));
                    }
                    if (attribute instanceof XAttributeContinuousImpl) {
                        encAtt.put(aname, new XAttributeContinuousImpl(aname, ((XAttributeContinuousImpl) attribute).getValue()));
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
        return "concept:name".equals(key) || "lifecycle:transition".equals(key) || "time:timestamp".equals(key) || "org:group".equals(key);
    }
}
