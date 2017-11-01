package core.models.intervals;

import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;

import java.util.Random;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class Interval {
    protected Random rnd = new Random();

    public abstract String get(String hash);

    //public abstract void resetHashCache();

    public abstract boolean isCompliant(DataExpression expr);

    protected BinaryExpression rot(BinaryExpression expr) {   // move number to the right part of expression
        if (expr.getRight().getNode().getType() == Token.Type.Number)
            return expr;

        Token t = expr.getNode();
        return new BinaryExpression(new Token(t.getPosition(), t.getType(), t.getValue().replace('>', '<').replace('<', '>')), expr.getRight(), expr.getLeft());
    }
}
