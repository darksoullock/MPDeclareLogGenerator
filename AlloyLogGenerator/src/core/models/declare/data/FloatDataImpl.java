package core.models.declare.data;

import core.Exceptions.GenerationException;
import core.helpers.RandomHelper;
import core.interfaces.SafeFunction2;
import core.models.intervals.FloatInterval;
import core.models.intervals.FloatValue;
import core.models.intervals.IntervalSplit;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatDataImpl extends NumericDataImpl {
    float min;
    float max;
    boolean includeMin;
    boolean includeMax;
    int intervalSplits;
    SafeFunction2 valueGenerator;

    public FloatDataImpl(String type, float min, float max, int intervalSplits, SafeFunction2<Float, Float, Float> valueGenerator) {
        this.min = min;
        this.max = max;
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

        List<Float> floatValues = splits.stream().map(i -> i.getParsedValue(Float::parseFloat)).distinct().collect(Collectors.toList());

        if (floatValues.get(0) > min)
            floatValues.add(0, min);
        if (floatValues.get(floatValues.size() - 1) < max)
            floatValues.add(floatValues.size(), max);

        if (includeMin)
            intervals.put(formatEquals(floatValues.get(0)), new FloatValue(floatValues.get(0)));

        if (includeMax)
            intervals.put(formatEquals(floatValues.get(floatValues.size() - 1)), new FloatValue(floatValues.get(floatValues.size() - 1)));

        addValues(splits);
        addIntervals(floatValues);
    }

    private void addValues(List<IntervalSplit> splits) {
        for (IntervalSplit i : splits.stream().filter(i -> i.isLeft() && i.isRight()).collect(Collectors.toList())) {
            intervals.put(formatEquals(i.getParsedValue(Float::parseFloat)), new FloatValue(i.getParsedValue(Float::parseFloat)));
        }

        java.util.Map<Float, Boolean> a = new HashMap<>();
        for (IntervalSplit i : splits.stream().filter(i -> i.isLeft() ^ i.isRight()).collect(Collectors.toList())) {
            Float value = i.getParsedValue(Float::parseFloat);
            if (a.containsKey(value) && a.get(value) == i.isRight())
                intervals.put(formatEquals(value), new FloatValue(value));
            else
                a.put(value, i.isLeft());
        }
    }

    private void addIntervals(List<Float> floatValues) {
        for (int i = 1; i < floatValues.size(); ++i) {
            float a = floatValues.get(i - 1);
            float b = floatValues.get(i);
            addBetweenInterval(a, b);
        }
    }

    private void addBetweenInterval(float a, float b) {
        float step = (b - a) / intervalSplits;
        for (int j = 0; j < intervalSplits; ++j) {
            float start = a + step * j;
            float end = a + step * (j + 1);
            intervals.put(formatBetween(start, end), new FloatInterval(start, end, valueGenerator));
        }
    }

    @Override
    public void addSplit(IntervalSplit s) throws GenerationException {
        float val = s.getParsedValue(Float::parseFloat);
        if (val < min || val > max)
            throw new GenerationException(val + " is out of defined float interval " + min + "" + max);
        if (val == min)
            includeMin = true;
        if (val == max)
            includeMax = true;
        this.splits.add(s);
    }

    private String formatBetween(float a, float b) {
        return ("floatBetween" + String.valueOf(a).replace('.', 'p') + "and" + String.valueOf(b).replace('.', 'p') + 'r' + RandomHelper.getNext()).replace('-', 'm');
    }

    private String formatEquals(float a) {
        return ("floatEqualsTo" + String.valueOf(a).replace('.', 'p') + 'r' + RandomHelper.getNext()).replace('-', 'm');
    }
}
