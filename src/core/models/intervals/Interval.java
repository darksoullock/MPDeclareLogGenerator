package core.models.intervals;

import core.Global;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;

import java.util.*;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class Interval {
    protected Random rnd = new Random();

    public abstract String get();

    Map<String, List<String>> sameCache;

    public String getSame(String key) {
        String alt1 = "this/" + Global.constants.getSamePrefix1();
        String alt2 = "this/" + Global.constants.getSamePrefix2();
        String op;
        if (key.startsWith(alt1))
            op = alt2 + key.substring(alt1.length());
        else
            op = alt1 + key.substring(alt2.length());
        if (sameCache.containsKey(op) && !sameCache.get(op).isEmpty()) {
            List<String> values = sameCache.get(op);
            String value = values.get(values.size() - 1);
            values.remove(values.size() - 1);
            return value;
        } else {
            if (!sameCache.containsKey(key))
                sameCache.put(key, new ArrayList<>());
            List<String> values = sameCache.get(key);
            String value = get();
            values.add(value);
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
