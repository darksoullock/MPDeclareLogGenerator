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
        if (node.getValue().equals("is"))
            return "("+left.toAlloy()+"="+right.toAlloy()+")";

        if (node.getValue().equals("is not"))
            return "(not "+left.toAlloy()+"="+right.toAlloy()+")";

        if (node.getValue().equals("in"))
            return "(#{"+left.toAlloy()+"&"+right.toAlloy()+"} = 1)";

        if (node.getValue().equals("not in"))
            return "(#{"+left.toAlloy()+"&"+right.toAlloy()+"} = 0)";

        return "("+left.toAlloy()+node.getValue()+right.toAlloy()+")";
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
