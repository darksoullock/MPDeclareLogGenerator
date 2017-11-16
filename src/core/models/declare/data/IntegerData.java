package core.models.declare.data;

import core.RandomHelper;
import core.models.intervals.FloatInterval;
import core.models.intervals.IntegerInterval;
import core.models.intervals.IntegerValue;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class IntegerData extends NumericData {
    int min;
    int max;
    int intervalSplits;

    public IntegerData(String type, int min, int max, int intervalSplits) {
        this.min = min - 1;
        this.max = max + 1;
        this.type = type;
        this.intervalSplits = intervalSplits;
    }

    @Override
    protected void generate() {
        intervals = new HashMap<>();

        if (values.size() == 0) {
            addBetweenInterval(min, max);
            return;
        }

        List<Integer> intValues = values.stream().map(Integer::parseInt).distinct().collect(Collectors.toList());
        intValues.sort(Integer::compareTo);

        if (intValues.get(0) > min)
            intValues.add(0, min);
        if (intValues.get(intValues.size() - 1) < max)
            intValues.add(intValues.size(), max);

        for (int i = 1; i < intValues.size(); ++i) {
            int a = intValues.get(i - 1);
            int b = intValues.get(i);
            if (b - a > 1)  // otherwise no possible values
                addBetweenInterval(a, b);
            if (i != intValues.size() - 1)
                intervals.put(formatEquals(b), new IntegerValue(b));
        }
    }

    private void addBetweenInterval(int a, int b) {
        ++a;
        float step = (b - a) / intervalSplits * 1.001f;  // to ensure that a/n*n>=a
        if (step < 1) { // to avoid empty intervals -- doesn't split small intervals. can be done other way splitting it by less fractions
            intervals.put(formatBetween(a, b), new IntegerInterval(a, b));
            return;
        }

        for (int j = 0; j < intervalSplits; ++j) {
            int start = a + (int) (step * j) - 1;
            int end = a + (int) (step * (j + 1));
            intervals.put(formatBetween(start, end), new IntegerInterval(start, end));
        }
    }

    @Override
    public void addValue(String value) {
        int val = Integer.parseInt(value);
        if (val <= min || val >= max)
            throw new InvalidStateException(val + " is out of defined interval of " + type);
        this.values.add(value);
    }

    private String formatBetween(int a, int b) {
        return ("intBetween" + a + "and" + b + 'r' + RandomHelper.getNext()).replace('-', 'm');
    }

    private String formatEquals(int a) {
        return ("intEqualsTo" + a + 'r' + RandomHelper.getNext()).replace('-', 'm');
    }
}
