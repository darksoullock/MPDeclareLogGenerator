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

    public void setName(String name) {
        this.name = name;
    }

    public List<String> getArgs() {
        return args;
    }

    public void setArgs(List<String> args) {
        this.args = args;
    }
}
