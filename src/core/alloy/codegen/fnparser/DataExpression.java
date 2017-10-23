package core.alloy.codegen.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public abstract class DataExpression {
    protected Token node;
    String alloy;

    public String toAlloy() {
        if (alloy == null)
            alloy = toAlloyInt();
        return alloy;
    }

    protected abstract String toAlloyInt();

    public Token getNode() {
        return node;
    }
}
