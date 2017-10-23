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
        if (node.getType() == Token.Type.Set)
            return node.getValue().replace(',','+');

        if (node.getType() == Token.Type.Variable)
            return node.getValue().replace('.','&');


        return node.getValue();
    }
}
