package core.models.intervals;

import core.Exceptions.BadSolutionException;
import core.Exceptions.GenerationException;
import core.interfaces.SafeFunction2;
import declare.fnparser.BinaryExpression;
import declare.fnparser.DataExpression;
import declare.fnparser.Token;

import java.util.*;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class FloatInterval extends Interval {

    float min;
    float max;
    SafeFunction2<Float, Float, Float> getValueBetween;

    public FloatInterval(float min, float max, SafeFunction2 valueGenerator) {
        this.min = min;
        this.max = max;
        this.getValueBetween = valueGenerator;
        if (valueGenerator == null)
            this.getValueBetween = (amin, amax) -> rnd.nextFloat() * (max - min) + min;
    }

    @Override
    public String get() {
        return String.valueOf(getValueBetween.invoke(min, max));
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
    public boolean isCompliant(DataExpression expr) throws GenerationException {
        if (expr.getNode().getType() != Token.Type.Comparator)
            throw new GenerationException("Interval compliancy can be check only for numeric comparison operations");

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

        throw new GenerationException("Unknown operation: " + expr.toString());
    }

    @Override
    public int getValueCount(int limit) {
        return -1;
    }
}
