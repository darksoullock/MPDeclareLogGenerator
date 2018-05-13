package declare.lang;

import declare.fnparser.DataFunction;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class DataConstraint extends Constraint {
    List<DataFunction> functions;

    public DataConstraint(String name, List<String> args, List<DataFunction> functions, Statement statement) {
        super(name, args, statement);
        this.functions = functions;
    }

    public boolean hasSecondFunction() {
        return functions.size() > 1;
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
