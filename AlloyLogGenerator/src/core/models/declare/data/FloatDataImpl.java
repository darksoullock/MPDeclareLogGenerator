package core.models.declare.data;

import core.exceptions.GenerationException;
import core.helpers.RandomHelper;
import core.interfaces.SafeFunction2;
import core.models.intervals.FloatInterval;
import core.models.intervals.FloatValue;
import core.models.intervals.IntervalSplit;
import org.apache.commons.lang3.tuple.Pair;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatDataImpl extends NumericDataImpl {
    private float min;
    private float max;
    private boolean includeMin;
    private boolean includeMax;
    private int intervalSplits;
    private SafeFunction2<Float, Float, Float> valueGenerator;

    public FloatDataImpl(String type, float min, float max, int intervalSplits, SafeFunction2<Float, Float, Float> valueGenerator, boolean required) {
        this.min = min;
        this.max = max;
        this.type = type;
        this.intervalSplits = intervalSplits;
        this.valueGenerator = valueGenerator;
        this.required = required;
    }

    @Override
    protected void generate() {
        intervals = new HashMap<>();

        if (splits.size() == 0) {
            addBetweenInterval(Pair.of(min, false), Pair.of(max, true));
            return;
        }

        List<Pair<Float, Boolean>> floatValues = splits.stream().map(i -> Pair.of(i.getParsedValue(Float::parseFloat), i.isRight())).distinct().collect(Collectors.toList());

        if (floatValues.get(0).getKey() > min)
            floatValues.add(0, Pair.of(min, false));
        if (floatValues.get(floatValues.size() - 1).getKey() < max)
            floatValues.add(floatValues.size(), Pair.of(max, true));

        if (includeMin)
            intervals.put(formatEquals(floatValues.get(0).getKey()), new FloatValue(floatValues.get(0).getKey()));

        if (includeMax)
            intervals.put(formatEquals(floatValues.get(floatValues.size() - 1).getKey()), new FloatValue(floatValues.get(floatValues.size() - 1).getKey()));

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

    private void addIntervals(List<Pair<Float, Boolean>> floatValues) {
        for (int i = 1; i < floatValues.size(); ++i) {
            addBetweenInterval(floatValues.get(i - 1), floatValues.get(i));
        }
    }

    private void addBetweenInterval(Pair<Float, Boolean> left, Pair<Float, Boolean> right) {
        float a = left.getKey();
        float b = right.getKey();
        float step = (b - a) / intervalSplits;
        for (int j = 0; j < intervalSplits; ++j) {
            float start = a + step * j;
            float end = a + step * (j + 1);
            intervals.put(formatBetween(start, end), new FloatInterval(start, end, !left.getRight(), right.getRight(), valueGenerator));
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
