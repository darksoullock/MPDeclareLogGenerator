package core.models.declare;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class Constraint {
    String name;
    List<String> args;

    public Constraint(String name, List<String> args) {
        this.name = name;
        this.args = args;
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
