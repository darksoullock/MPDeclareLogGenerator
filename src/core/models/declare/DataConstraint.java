package core.models.declare;

import core.alloy.codegen.fnparser.DataFunction;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class DataConstraint extends Constraint {
    List<DataFunction> functions;

    public DataConstraint(String name, List<String> args, List<DataFunction> functions) {
        super(name, args);
        this.functions = functions;
    }

    public List<DataFunction> getFunctions() {
        return functions;
    }

    public DataFunction getFirstFunction() {
        return functions.get(0);
    }

    public DataFunction getSecondFunction() {
        return functions.get(1);
    }
}
