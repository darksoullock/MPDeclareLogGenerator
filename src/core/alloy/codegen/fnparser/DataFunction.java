package core.alloy.codegen.fnparser;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class DataFunction {
    List<String> args;
    DataExpression expression;

    public DataFunction(List<String> args, DataExpression expression) {
        this.args = args;
        this.expression = expression;
    }

    public List<String> getArgs() {
        return args;
    }

    public void setArgs(List<String> args) {
        this.args = args;
    }

    public DataExpression getExpression() {
        return expression;
    }

    public void setExpression(DataExpression expression) {
        this.expression = expression;
    }
}
