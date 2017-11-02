package core.models.intervals;

import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class IntegerInterval extends Interval {

    int min;
    int max;
    Map<String, List<String>> hashCache = new HashMap<>();

    public IntegerInterval(int min, int max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String get(String hash) {
        if (hash != null)
            return getOppositeOrCreate(hash, "this/Get", "this/Set");

        return String.valueOf(rnd.nextInt(max - min - 1) + min + 1);
    }

    private String getOppositeOrCreate(String hash, String alt1, String alt2) {
        String op;
        if (hash.startsWith(alt1))
            op = alt2 + hash.substring(8);
        else
            op = alt1 + hash.substring(8);
        if (hashCache.containsKey(op) && !hashCache.get(op).isEmpty()) {
            List<String> values = hashCache.get(op);
            String value = values.get(values.size() - 1);
            values.remove(values.size() - 1);
            return value;
        } else {
            if (!hashCache.containsKey(hash))
                hashCache.put(hash, new ArrayList<>());
            List<String> values = hashCache.get(hash);
            String value = String.valueOf(rnd.nextInt(max - min - 1) + min + 1);
            values.add(value);
            return value;
        }

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
            return max <= number && min < number;
        if (op.equals("="))
            return min == number && max == number;

        throw new InvalidStateException("Unknown operation: " + expr.toString());
    }
}