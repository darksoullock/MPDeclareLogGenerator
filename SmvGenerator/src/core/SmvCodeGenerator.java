package core;

import com.google.gson.Gson;
import declare.DeclareModel;
import declare.lang.Activity;
import declare.lang.Constraint;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2018-03-25.
 */
public class SmvCodeGenerator {
    StringBuilder smv;
    private String dataBindingJson;

    public void run(DeclareModel model, int minLength) throws GenerationException {
        smv = new StringBuilder("MODULE main\n");
        generateVariables(model.getActivities(), getData(model));
        generateAssign(minLength);
        generateDataBinding(model.getActivityToData(), model.getDataToActivity());
        new LtlGen(smv).generateConstraints(getAllConstraints(model));
    }

    private ArrayList<Constraint> getAllConstraints(DeclareModel model) throws GenerationException {
        ArrayList<Constraint> ac = new ArrayList<>();
        ac.addAll(model.getConstraints());
        ac.addAll(model.getDataConstraints());
        return ac;
    }

    private void generateVariables(List<Activity> activities, List data) throws GenerationException {
        smv.append("FROZENVAR\n" +
                "minlength:integer;\n" +
                "VAR\n" +
                "first: boolean;\n" +
                "length: integer;\n");
        generateActivities(activities);
        generateData(data);
    }

    private List getData(DeclareModel model) {
        List<Object> data = new ArrayList<>();
        data.addAll(model.getEnumeratedData());
        data.addAll(model.getIntegerData());
        data.addAll(model.getFloatData());
        return data;
    }

    private void generateData(List data) throws GenerationException {
        for (Object item : data) {
            if (item instanceof IntegerData)
                smv.append(((IntegerData) item).getType()).append(":integer;\n");
            else if (item instanceof FloatData)
                smv.append(((FloatData) item).getType()).append(":real;\n");
            else if (item instanceof EnumeratedData)
                smv.append(((EnumeratedData) item).getType()).append(":{")
                        .append(String.join(", ", ((EnumeratedData) item).getValues())).append("};\n");
            else throw new GenerationException("unknown data type");
        }
    }

    private void generateActivities(List<Activity> activities) {
        smv.append("state : {")
                .append(String.join(", ", activities.stream().map(Activity::getName).collect(Collectors.toList())))
                .append(", _tail};\n");
    }

    private void generateAssign(int minLength) {
        smv.append("ASSIGN\n" +
                "init(first):=TRUE;\n" +
                "next(first):=FALSE;\n" +
                "init(length):=0;\n" +
                "next(length):=\n" +
                "case\n" +
                "length>=minlength:length;\n" +
                "TRUE:length+1;\n" +
                "esac;\n" +
                "init(minlength):=").append(minLength).append(";\n");
    }

    public String getSmv() {
        return smv.toString();
    }

    private void generateDataBinding(Map<String, List<String>> activityToData, Map<String, List<String>> dataToActivity) {
        dataBindingJson = new Gson().toJson(activityToData);
    }

    public String getDataBindingJson() {
        return dataBindingJson;
    }
}
