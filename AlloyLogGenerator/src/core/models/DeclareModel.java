package core.models;

import core.models.declare.Activity;
import core.models.declare.Constraint;
import core.models.declare.DataConstraint;
import core.models.declare.data.EnumeratedData;
import core.models.serialization.trace.AbstractTraceAttribute;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2018-03-24.
 */
public class DeclareModel {

    List<Activity> activities;
    List<EnumeratedData> data;
    List<Constraint> constraints;
    List<DataConstraint> dataConstraints;

    Map<String, List<String>> activityToData;
    Map<String, List<String>> dataToActivity;

    List<AbstractTraceAttribute> traceAttributes;

    public DeclareModel() {
        activities = new ArrayList<>();
        data = new ArrayList<>();
        constraints = new ArrayList<>();
        dataConstraints = new ArrayList<>();

        activityToData = new HashMap<>();
        dataToActivity = new HashMap<>();
    }

    public List<Activity> getActivities() {
        return activities;
    }

    public List<EnumeratedData> getData() {
        return data;
    }

    public void setData(List<EnumeratedData> data) {
        this.data = data;
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

    public List<AbstractTraceAttribute> getTraceAttributes() {
        return traceAttributes;
    }

    public void setTraceAttributes(List<AbstractTraceAttribute> traceAttributes) {
        this.traceAttributes = traceAttributes;
    }
}
