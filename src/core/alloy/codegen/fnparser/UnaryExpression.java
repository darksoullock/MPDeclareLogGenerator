package core.alloy.codegen.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class UnaryExpression extends DataExpression {
    DataExpression value;

    public UnaryExpression(Token op, DataExpression value) {
        this.node = op;
        this.value = value;
    }

    @Override
    public String toAlloyInt() {    // TODO: fix sme/different -- variable name
        if (node.getValue().equals("same"))
            return "(A&"+value.toAlloy()+"=B&"+value.toAlloy()+")";

        if (node.getValue().equals("different"))
            return "(not A&"+value.toAlloy()+"=B&"+value.toAlloy()+")";

        return node.getValue() + " (" + value.toAlloy() + ')';
    }

    public DataExpression getValue() {
        return value;
    }

    public void setValue(DataExpression value) {
        this.value = value;
    }
}
