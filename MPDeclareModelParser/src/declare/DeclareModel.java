package declare;

import declare.lang.Activity;
import declare.lang.Constraint;
import declare.lang.DataConstraint;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;
import declare.lang.trace.EnumTraceAttribute;
import declare.lang.trace.FloatTraceAttribute;
import declare.lang.trace.IntTraceAttribute;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2018-03-24.
 */
public class DeclareModel {

    List<Activity> activities;
    List<EnumeratedData> enumeratedData;
    List<IntegerData> integerData;
    List<FloatData> floatData;
    List<Constraint> constraints;
    List<DataConstraint> dataConstraints;

    Map<String, List<String>> activityToData;
    Map<String, List<String>> dataToActivity;

    List<EnumTraceAttribute> enumTraceAttributes;
    List<IntTraceAttribute> intTraceAttributes;
    List<FloatTraceAttribute> floatTraceAttributes;

    public DeclareModel() {
        activities = new ArrayList<>();
        enumeratedData = new ArrayList<>();
        constraints = new ArrayList<>();
        dataConstraints = new ArrayList<>();

        activityToData = new HashMap<>();
        dataToActivity = new HashMap<>();

        integerData = new ArrayList<>();
        floatData = new ArrayList<>();
        enumeratedData = new ArrayList<>();

        intTraceAttributes = new ArrayList<>();
        floatTraceAttributes = new ArrayList<>();
        enumTraceAttributes = new ArrayList<>();
    }

    public List<Activity> getActivities() {
        return activities;
    }

    public List<EnumeratedData> getEnumeratedData() {
        return enumeratedData;
    }

    public void setEnumeratedData(List<EnumeratedData> enumeratedData) {
        this.enumeratedData = enumeratedData;
    }

    public List<IntegerData> getIntegerData() {
        return integerData;
    }

    public void setIntegerData(List<IntegerData> integerData) {
        this.integerData = integerData;
    }

    public List<FloatData> getFloatData() {
        return floatData;
    }

    public void setFloatData(List<FloatData> floatData) {
        this.floatData = floatData;
    }

    public List<Constraint> getConstraints() {
        return constraints;
    }

    public void setConstraints(List<Constraint> constraints) {
        this.constraints = constraints;
    }

    public List<DataConstraint> getDataConstraints() {
        return dataConstraints;
    }

    public void setDataConstraints(List<DataConstraint> dataConstraints) {
        this.dataConstraints = dataConstraints;
    }

    public Map<String, List<String>> getActivityToData() {
        return activityToData;
    }

    public void setActivityToData(Map<String, List<String>> activityToData) {
        this.activityToData = activityToData;
    }

    public Map<String, List<String>> getDataToActivity() {
        return dataToActivity;
    }

    public void setDataToActivity(Map<String, List<String>> dataToActivity) {
        this.dataToActivity = dataToActivity;
    }

    public void setActivities(List<Activity> activities) {
        this.activities = activities;
    }

    public List<EnumTraceAttribute> getEnumTraceAttributes() {
        return enumTraceAttributes;
    }

    public void setEnumTraceAttributes(List<EnumTraceAttribute> enumTraceAttributes) {
        this.enumTraceAttributes = enumTraceAttributes;
    }

    public List<IntTraceAttribute> getIntTraceAttributes() {
        return intTraceAttributes;
    }

    public void setIntTraceAttributes(List<IntTraceAttribute> intTraceAttributes) {
        this.intTraceAttributes = intTraceAttributes;
    }

    public List<FloatTraceAttribute> getFloatTraceAttributes() {
        return floatTraceAttributes;
    }

    public void setFloatTraceAttributes(List<FloatTraceAttribute> floatTraceAttributes) {
        this.floatTraceAttributes = floatTraceAttributes;
    }
}
