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
    public String toAlloyInt() {
        return null;
    }

    public DataExpression getValue() {
        return value;
    }

    public void setValue(DataExpression value) {
        this.value = value;
    }
}
