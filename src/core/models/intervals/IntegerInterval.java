package core.models.intervals;

import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import sun.plugin.dom.exception.InvalidStateException;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class IntegerInterval extends Interval {

    int min;
    int max;

    public IntegerInterval(int min, int max) {
        ++min;
        this.min = min;
        this.max = max;
    }

    @Override
    public String get() {
        return String.valueOf(rnd.nextInt(max - min) + min);
    }

    @Override
    public boolean isCompliant(DataExpression expr) {
        if (expr.getNode().getType() != Token.Type.Comparator)
            throw new InvalidStateException("Interval compliancy can be check only for numeric comparison operations");

        BinaryExpression bex = rot((BinaryExpression) expr);
        int number = Integer.parseInt(bex.getRight().getNode().getValue());
        String op = expr.getNode().getValue();
        if (op.equals(">="))
            return min >= number;
        if (op.equals(">"))
            return min >= number && max > number;
        if (op.equals("<="))
            return max <= number;
        if (op.equals("<"))
            return max < number && min < number;
        if (op.equals("="))
            return min == number && max == number;

        throw new InvalidStateException("Unknown operation: " + expr.toString());
    }

    private BinaryExpression rot(BinaryExpression expr) {   // move number to the right part of expression
        if (expr.getRight().getNode().getType() == Token.Type.Number)
            return expr;

        Token t = expr.getNode();
        return new BinaryExpression(new Token(t.getPosition(), t.getType(), t.getValue().replace('>', '<').replace('<', '>')), expr.getRight(), expr.getLeft());
    }
}