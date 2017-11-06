package core.models.intervals;

import core.Global;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.*;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class Interval {
    protected Random rnd = new Random();

    public abstract String get();

    Map<String, String> sameCache;

    public String getSame(String key) {
        if (sameCache.containsKey(key)) {
            return sameCache.get(key);
        } else {
            String value = get();
            sameCache.put(key, value);
            return value;
        }
    }

    public void resetCaches(){
        sameCache = new HashMap<>();
    }

    public abstract String getDifferent(String hash);

    public abstract boolean isCompliant(DataExpression expr);

    protected BinaryExpression rot(BinaryExpression expr) {   // move number to the right part of expression
        if (expr.getRight().getNode().getType() == Token.Type.Number)
            return expr;

        Token t = expr.getNode();
        return new BinaryExpression(new Token(t.getPosition(), t.getType(), t.getValue().replace('>', '<').replace('<', '>')), expr.getRight(), expr.getLeft());
    }

    public abstract int getValueCount(int limit);
}
