package core.models.declare.data;

import core.helpers.RandomHelper;
import core.interfaces.SafeFunction2;
import core.models.intervals.IntegerInterval;
import core.models.intervals.IntegerValue;
import core.models.intervals.IntervalSplit;
import declare.DeclareParserException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class IntegerDataImpl extends NumericDataImpl {
    int min;
    int max;
    int intervalSplits;
    SafeFunction2 valueGenerator;

    public IntegerDataImpl(String type, int min, int max, int intervalSplits, SafeFunction2<Integer, Integer, Integer> valueGenerator) {
        this.min = min - 1; // as constructor parameters min and max are included in range, we move them out
        this.max = max + 1;
        this.type = type;
        this.intervalSplits = intervalSplits;
        this.valueGenerator = valueGenerator;
    }

    @Override
    protected void generate() {
        intervals = new HashMap<>();

        if (splits.size() == 0) {
            addBetweenInterval(min, max);
            return;
        }

        List<Integer> intValues = new ArrayList<>();    // this list contains splits. interval splits between value and value+1
        for (IntervalSplit i : splits) {
            int number = i.getParsedValue(Integer::parseInt);
            if (i.isRight())
                intValues.add(number);

            if (i.isLeft())
                intValues.add(--number);
        }

        intValues = intValues.stream().distinct().collect(Collectors.toList());
        intValues.sort(Integer::compareTo);

        if (intValues.get(0) > min)
            intValues.add(0, min);
        if (intValues.get(intValues.size() - 1) < max)
            intValues.add(intValues.size(), max - 1);   // -1 as max is out of range, and intValues contains right=side splits

        for (int i = 1; i < intValues.size(); ++i) {
            int a = intValues.get(i - 1);
            int b = intValues.get(i);
            if (b - a > 1) {
                ++b;
                addBetweenInterval(a, b);
            } else {
                intervals.put(formatEquals(b), new IntegerValue(b));
            }
        }
    }

    private void addBetweenInterval(int a, int b) { // a and b are not included
        float step = (b - a) / intervalSplits;
        if (step < 1) { // to avoid empty intervals -- doesn't split small intervals. can be done other way splitting it by less fractions
            intervals.put(formatBetween(a, b), new IntegerInterval(a, b, valueGenerator));
            return;
        }

        for (int j = 0; j < intervalSplits; ++j) {
            int start = a + round((step * j) - (j == 0 ? 0 : 1));
            int end = a + round(step * (j + 1));
            if (end - start > 1)
                intervals.put(formatBetween(start, end), new IntegerInterval(start, end, valueGenerator));
        }
    }

    private int round(double v) {
        int sign = v < 0 ? -1 : 1;
        int value = (int) ((v + 0.1) * sign);
        return value * sign;
    }

    @Override
    public void addSplit(IntervalSplit s) throws DeclareParserException {
        int val = s.getParsedValue(Integer::parseInt);
        if (val <= min || val >= max)
            throw new DeclareParserException(val + " is out of defined interval of " + type);
        this.splits.add(s);
    }

    private String formatBetween(int a, int b) {
        return ("intBetween" + a + "and" + b + 'r' + RandomHelper.getNext()).replace('-', 'm');
    }

    private String formatEquals(int a) {
        return ("intEqualsTo" + a + 'r' + RandomHelper.getNext()).replace('-', 'm');
    }
}
