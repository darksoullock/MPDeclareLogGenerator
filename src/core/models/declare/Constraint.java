package core.models.declare;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class Constraint {
    String name;
    List<String> args;
    Statement statement;

    public Constraint(String name, List<String> args, Statement statement) {
        this.name = name;
        this.args = args;
        this.statement = statement;
    }

    public String getName() {
        return name;
    }

    public List<String> getArgs() {
        return args;
    }

    public String taskA() {
        return args.get(0);
    }

    public String taskB() {
        return args.get(1);
    }

    public Statement getStatement() {
        return statement;
    }

    public boolean isBinary() {
        return args.size() == 2;
    }

    public boolean supportsVacuity() {
        return isBinary() && (getName().equals("RespondedExistence") ||
                getName().equals("Response") ||
                getName().equals("AlternateResponse") ||
                getName().equals("ChainResponse") ||
                getName().equals("Precedence") ||
                getName().equals("AlternatePrecedence") ||
                getName().equals("ChainPrecedence") ||
                getName().equals("NotRespondedExistence") ||
                getName().equals("NotResponse") ||
                getName().equals("NotPrecedence") ||
                getName().equals("NotChainResponse") ||
                getName().equals("NotChainPrecedence"));
    }
}
