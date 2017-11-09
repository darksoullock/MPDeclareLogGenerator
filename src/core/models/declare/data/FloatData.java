package core.models.declare.data;

import core.RandomHelper;
import core.models.intervals.FloatInterval;
import core.models.intervals.FloatValue;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatData extends NumericData {
    float min;
    float max;
    boolean includeMin;
    boolean includeMax;

    public FloatData(String type, float min, float max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    @Override
    protected void generate() {
        intervals = new HashMap<>();

        if (values.size() == 0) {
            intervals.put(formatBetween(min, max), new FloatInterval(min, max));
            return;
        }

        List<Float> floatValues = values.stream().map(Float::parseFloat).distinct().collect(Collectors.toList());
        floatValues.sort(Float::compareTo);

        if (floatValues.get(0) > min)
            floatValues.add(0, min);
        if (floatValues.get(floatValues.size() - 1) < max)
            floatValues.add(floatValues.size(), max);

        if (includeMin)
            intervals.put(formatEquals(floatValues.get(0)), new FloatValue(floatValues.get(0)));

        for (int i = 1; i < floatValues.size(); ++i) {
            float a = floatValues.get(i - 1);
            float b = floatValues.get(i);
            intervals.put(formatBetween(a, b), new FloatInterval(a, b));
            if (i != floatValues.size() - 1 || includeMax)
                intervals.put(formatEquals(b), new FloatValue(b));
        }
    }

    @Override
    public void addValue(String value) {
        float val = Float.parseFloat(value);
        if (val < min || val > max)
            throw new InvalidStateException(val + " is out of defined interval of " + type);
        if (val==min)
            includeMin = true;
        if (val==max)
            includeMax = true;
        this.values.add(value);
    }

    private String formatBetween(float a, float b) {
        return ("floatBetween" + String.valueOf(a).replace('.', 'p') + "and" + String.valueOf(b).replace('.', 'p') + 'r' + RandomHelper.getNext()).replace('-','m');
    }

    private String formatEquals(float a) {
        return ("floatEqualsTo" + String.valueOf(a).replace('.', 'p') + 'r' + RandomHelper.getNext()).replace('-','m');
    }
}
