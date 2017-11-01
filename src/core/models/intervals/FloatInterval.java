package core.models.intervals;

import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.HashMap;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class FloatInterval extends Interval {

    float min;
    float max;

    Map<String, String> hashCache = new HashMap<>();

    public FloatInterval(float min, float max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String get(String hash) {
        if (hashCache.containsKey(hash))
            return hashCache.get(hash);
        String value = String.valueOf(rnd.nextFloat() * (max - min) + min);
        hashCache.put(hash, value);
        return value;
    }

    @Override
    public boolean isCompliant(DataExpression expr) {
        if (expr.getNode().getType() != Token.Type.Comparator)
            throw new InvalidStateException("Interval compliancy can be check only for numeric comparison operations");

        BinaryExpression bex = rot((BinaryExpression) expr);
        float number = Float.parseFloat(bex.getRight().getNode().getValue());
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
}
