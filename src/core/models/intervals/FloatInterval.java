package core.models.intervals;

import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;

import java.util.*;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class FloatInterval extends Interval {

    float min;
    float max;

    public FloatInterval(float min, float max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String get() {
        return String.valueOf(rnd.nextFloat() * (max - min) + min);
    }

    Map<String, Set<String>> differentCache;

    @Override
    public String getDifferent(List<String> keys) throws BadSolutionException {
        Set<String> values = new HashSet<>();

        for (String key : keys)
            if (differentCache.containsKey(key))
                values.addAll(differentCache.get(key));
            else
                differentCache.put(key, new HashSet<>());

        String value = get();

        while (values.contains(value)) {
            value = get();
        }

        for (String key : keys)
            differentCache.get(key).add(value);

        return String.valueOf(value);
    }

    @Override
    public void resetCaches() {
        super.resetCaches();
        if (differentCache == null || differentCache.size() > 0)
            differentCache = new HashMap<>();
    }

    @Override
    public boolean isCompliant(DataExpression expr) throws DeclareParserException {
        if (expr.getNode().getType() != Token.Type.Comparator)
            throw new DeclareParserException("Interval compliancy can be check only for numeric comparison operations");

        BinaryExpression bex = rot((BinaryExpression) expr);
        float number = Float.parseFloat(bex.getRight().getNode().getValue());
        String op = bex.getNode().getValue();
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

        throw new DeclareParserException("Unknown operation: " + expr.toString());
    }

    @Override
    public int getValueCount(int limit) {
        return -1;
    }
}
