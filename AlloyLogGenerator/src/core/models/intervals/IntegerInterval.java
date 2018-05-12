package core.models.intervals;

import core.Exceptions.BadSolutionException;
import core.Global;
import core.interfaces.SafeFunction2;
import declare.DeclareParserException;
import declare.fnparser.BinaryExpression;
import declare.fnparser.DataExpression;
import declare.fnparser.Token;

import java.util.*;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class IntegerInterval extends Interval { //does not include min and max values

    int min;
    int max;
    SafeFunction2<Integer, Integer, Integer> getValueBetween;

    public IntegerInterval(int min, int max, SafeFunction2 valueGenerator) {
        this.min = min;
        this.max = max;
        this.getValueBetween = valueGenerator;
        if (valueGenerator == null)
            this.getValueBetween = (amin, amax) -> rnd.nextInt(amax - amin - 1) + amin + 1;
    }

    @Override
    public String get() {
        return String.valueOf(getValueBetween.invoke(min, max));
    }

    Map<String, Set<Integer>> differentCache;

    @Override
    public String getDifferent(List<String> keys) throws BadSolutionException {
        Set<Integer> values = new HashSet<>();

        for (String key : keys)
            if (differentCache.containsKey(key))
                values.addAll(differentCache.get(key));
            else
                differentCache.put(key, new HashSet<>());

        int value = getValueBetween.invoke(min, max);

        int iters = 0;
        int maxIter = getValueCount(max - min);
        while (values.contains(value)) {
            if (++iters > maxIter)
                break;

            value = ++value;
            if (value == max)
                value = min + 1;
        }

        for (String key : keys)
            differentCache.get(key).add(value);

        if (iters > maxIter) {
            Global.log.accept("different values exhausted; trace is invalid");
            return "No value";
        }

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
        int number = Integer.parseInt(bex.getRight().getNode().getValue());
        String op = bex.getNode().getValue();
        if (op.equals(">="))
            return min + 1 >= number;
        if (op.equals(">"))
            return min >= number && max > number;
        if (op.equals("<="))
            return max - 1 <= number;
        if (op.equals("<"))
            return max <= number && min < number;
        if (op.equals("="))
            return min == number && max == number;

        throw new DeclareParserException("Unknown operation: " + expr.toString());
    }

    @Override
    public int getValueCount(int limit) {
        int values = max - min - 1;
        return values < limit ? values : -1;
    }

    public int getMin() {
        return min;
    }

    public int getMax() {
        return max;
    }
}