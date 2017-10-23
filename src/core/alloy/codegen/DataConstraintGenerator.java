package core.alloy.codegen;

import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.DataFunction;
import core.alloy.codegen.fnparser.ValueExpression;
import core.models.declare.DataConstraint;

import java.util.Random;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class DataConstraintGenerator {

    Random rnd = new Random();
    StringBuilder alloy = new StringBuilder();

    public String Generate(DataConstraint i) {
        if (i.getName().equals("Absence"))
            AddAbsenceDataConstraint(i);

        return alloy.toString();
    }

    private void AddAbsenceDataConstraint(DataConstraint one) {
        String fn = getRandomFunctionName();
        alloy.append("fact { no te: TaskEvent | te.task = ").append(one.getFirstArg()).append(" and ").append(fn).append("[te.data] }\n");
        generateFunction(alloy, fn, one.getFirstFunction());
    }

    private void generateFunction(StringBuilder alloy, String name, DataFunction function) {
        alloy.append("pred ").append(name).append("(").append(String.join(", ", function.getArgs())).append(": set Payload) { { ");
        alloy.append(function.getExpression().toAlloy());
        alloy.append(" } }\n");
    }

    private String getRandomFunctionName() {
        return "p" + Math.abs(rnd.nextInt());   //TODO: change
    }
}
