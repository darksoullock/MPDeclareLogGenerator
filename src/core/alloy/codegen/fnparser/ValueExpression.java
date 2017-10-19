package core.alloy.codegen.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class ValueExpression extends DataExpression {
    public ValueExpression(Token value) {
        this.node = value;
    }

    @Override
    public String toAlloyInt() {
        return null;
    }
}
