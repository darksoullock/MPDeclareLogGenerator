package declare.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class UnaryExpression extends DataExpression {
    DataExpression value;

    public UnaryExpression(Token op, DataExpression value) {
        this.node = op;
        this.value = value;
    }

    public DataExpression getValue() {
        return value;
    }

    @Override
    public String toString() {
        return node.getValue() + "(" + value + ")";
    }
}
