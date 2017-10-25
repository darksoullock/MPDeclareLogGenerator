package core.models.declare.data;

import core.RandomHelper;
import core.models.intervals.IntegerInterval;
import core.models.intervals.IntegerValue;
import core.models.intervals.Interval;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class IntegerData extends NumericData {
    int min;
    int max;

    Map<String, Interval> intervals;

    public IntegerData(String type, int min, int max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    @Override
    public List<String> getValues() {
        if (intervals == null)
            generate();
        return new ArrayList<>(intervals.keySet());
    }

    @Override
    public Map<String, Interval> getMapping() {
        if (intervals == null)
            generate();
        return intervals;
    }

    private void generate() {
        intervals = new HashMap<>();

        if (values.size() == 0) {
            intervals.put(formatEquals(min), new IntegerValue(min));
            intervals.put(formatBetween(min, max), new IntegerInterval(min, max));
            intervals.put(formatEquals(max), new IntegerValue(max));
            return;
        }

        List<Integer> intValues = values.stream().map(Integer::parseInt).distinct().collect(Collectors.toList());

        if (intValues.get(0) > min)
            intValues.add(0, min);
        if (intValues.get(intValues.size() - 1) < max)
            intValues.add(intValues.size(), max);

        intervals.put(formatEquals(intValues.get(0)), new IntegerValue(intValues.get(0)));

        for (int i = 1; i < intValues.size(); ++i) {
            int a = intValues.get(i - 1);
            int b = intValues.get(i);
            intervals.put(formatBetween(a, b), new IntegerInterval(a, b));
            intervals.put(formatEquals(b), new IntegerValue(b));
        }
    }

    private String formatBetween(int a, int b) {
        return "intBetween" + a + "and" + b + 'r' + RandomHelper.getNext();
    }

    private String formatEquals(int a) {
        return "intEqualsTo" + a + 'r' + RandomHelper.getNext();
    }
}
