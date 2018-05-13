package declare.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class ValueExpression extends DataExpression {
    public ValueExpression(Token value) {
        this.node = value;
    }

    @Override
    public String toString() {
        return node.getValue();
    }
}
