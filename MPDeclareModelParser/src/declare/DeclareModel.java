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

import java.util.*;

/**
 * Created by Vasiliy on 2018-03-24.
 */
public class DeclareModel {

    Set<Activity> activities;
    Set<EnumeratedData> enumeratedData;
    Set<IntegerData> integerData;
    Set<FloatData> floatData;
    List<Constraint> constraints;
    List<DataConstraint> dataConstraints;

    Map<String, Set<String>> activityToData;
    Map<String, Set<String>> dataToActivity;

    List<EnumTraceAttribute> enumTraceAttributes;
    List<IntTraceAttribute> intTraceAttributes;
    List<FloatTraceAttribute> floatTraceAttributes;

    public DeclareModel() {
        activities = new HashSet<>();
        constraints = new ArrayList<>();
        dataConstraints = new ArrayList<>();

        activityToData = new HashMap<>();
        dataToActivity = new HashMap<>();

        integerData = new HashSet<>();
        floatData = new HashSet<>();
        enumeratedData = new HashSet<>();

        intTraceAttributes = new ArrayList<>();
        floatTraceAttributes = new ArrayList<>();
        enumTraceAttributes = new ArrayList<>();
    }

    public Set<Activity> getActivities() {
        return activities;
    }

    public Set<EnumeratedData> getEnumeratedData() {
        return enumeratedData;
    }

    public void setEnumeratedData(Set<EnumeratedData> enumeratedData) {
        this.enumeratedData = enumeratedData;
    }

    public Set<IntegerData> getIntegerData() {
        return integerData;
    }

    public void setIntegerData(Set<IntegerData> integerData) {
        this.integerData = integerData;
    }

    public Set<FloatData> getFloatData() {
        return floatData;
    }

    public void setFloatData(Set<FloatData> floatData) {
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

    public Map<String, Set<String>> getActivityToData() {
        return activityToData;
    }

    public void setActivityToData(Map<String, Set<String>> activityToData) {
        this.activityToData = activityToData;
    }

    public Map<String, Set<String>> getDataToActivity() {
        return dataToActivity;
    }

    public void setDataToActivity(Map<String, Set<String>> dataToActivity) {
        this.dataToActivity = dataToActivity;
    }

    public void setActivities(Set<Activity> activities) {
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
