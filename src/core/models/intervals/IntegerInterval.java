package core.models.intervals;

import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.*;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class IntegerInterval extends Interval {

    int min;
    int max;

    public IntegerInterval(int min, int max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String get() {
        return String.valueOf(rnd.nextInt(max - min - 1) + min + 1);
    }

    Map<String, Set<Integer>> differentCache;

    @Override
    public String getDifferent(List<String> keys) {
        Set<Integer> values = new HashSet<>();

        for (String key : keys)
            if (differentCache.containsKey(key))
                values.addAll(differentCache.get(key));
            else
                differentCache.put(key, new HashSet<>());

        int value = rnd.nextInt(max - min - 1) + min + 1;

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
            System.out.println("different values exhausted; trace is invalid");
            return "No value";
        }

        return String.valueOf(value);
    }

    @Override
    public void resetCaches() {
        super.resetCaches();
        differentCache = new HashMap<>();
    }

    @Override
    public boolean isCompliant(DataExpression expr) {
        if (expr.getNode().getType() != Token.Type.Comparator)
            throw new InvalidStateException("Interval compliancy can be check only for numeric comparison operations");

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

        throw new InvalidStateException("Unknown operation: " + expr.toString());
    }

    @Override
    public int getValueCount(int limit) {
        int values = max - min - 1;
        return values < limit ? values : -1;
    }
}