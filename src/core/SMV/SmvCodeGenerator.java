package core.SMV;

import com.google.gson.Gson;
import core.Exceptions.DeclareParserException;
import core.Exceptions.GenerationException;
import core.models.DeclareModel;
import core.models.declare.Activity;
import core.models.declare.Constraint;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.FloatData;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;

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

    public void run(DeclareModel model, int minLength) throws DeclareParserException, GenerationException {
        smv = new StringBuilder("MODULE main\n");
        generateVariables(model);
        generateAssign(minLength);
        generateDataBinding(model.getActivityToData(), model.getDataToActivity());
        generateLtl(model);
    }

    private void generateLtl(DeclareModel model) throws DeclareParserException, GenerationException {
        LtlGen l = new LtlGen(smv);
        List<Constraint> ac = new ArrayList<>();
        ac.addAll(model.getConstraints());
        ac.addAll(model.getDataConstraints());
        l.generateConstraints(ac);
    }

    private void generateVariables(DeclareModel model) {
        smv.append("FROZENVAR\n" +
                "minlength:integer;\n" +
                "VAR\n" +
                "first: boolean;\n" +
                "length: integer;\n");
        generateActivities(model.getActivities());
        generateData(model.getData());
    }

    private void generateData(List<EnumeratedData> data) {
        for (EnumeratedData item : data) {
            if (item instanceof NumericData) {
                if (item instanceof IntegerData)
                    smv.append((item).getType()).append(":integer;\n");
                if (item instanceof FloatData)
                    smv.append((item).getType()).append(":real;\n");
            } else {
                smv.append((item).getType()).append(":{").append(String.join(", ", item.getValues())).append("};\n");
            }
        }
    }

    private void generateActivities(List<Activity> activities) {
        smv.append("state : {")
                .append(String.join(", ", activities.stream().map(i -> i.getName()).collect(Collectors.toList())))
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
