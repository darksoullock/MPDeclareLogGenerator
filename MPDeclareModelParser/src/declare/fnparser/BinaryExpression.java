package declare.fnparser;

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

    public DataExpression getLeft() {
        return left;
    }

    public DataExpression getRight() {
        return right;
    }

    @Override
    public String toString() {
        return node.getValue() + '(' + left + ',' + right + ')';
    }
}
