package core.alloy.codegen.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class BinaryExpression extends DataExpression {
    DataExpression left;
    DataExpression right;

    public BinaryExpression(Token op, DataExpression left, DataExpression right) {
        this.node = op;
        this.left = left;
        this.right = right;
    }

    @Override
    public String toAlloyInt() {
        return null;
    }

    public DataExpression getLeft() {
        return left;
    }

    public void setLeft(DataExpression left) {
        this.left = left;
    }

    public DataExpression getRight() {
        return right;
    }

    public void setRight(DataExpression right) {
        this.right = right;
    }
}
