package core.models.declare.data;

import core.RandomHelper;
import core.models.intervals.FloatInterval;
import core.models.intervals.FloatValue;
import core.models.intervals.IntegerValue;

import java.util.HashMap;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatData extends NumericData {
    float min;
    float max;

    public FloatData(String type, float min, float max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    @Override
    protected void generate() {
        intervals = new HashMap<>();

        if (values.size() == 0) {
            intervals.put(formatEquals(min), new FloatValue(min));
            intervals.put(formatBetween(min, max), new FloatInterval(min, max));
            intervals.put(formatEquals(max), new FloatValue(max));
            return;
        }

        List<Float> floatValues = values.stream().map(Float::parseFloat).distinct().collect(Collectors.toList());

        if (floatValues.get(0) > min)
            floatValues.add(0, min);
        if (floatValues.get(floatValues.size() - 1) < max)
            floatValues.add(floatValues.size(), max);

        intervals.put(formatEquals(floatValues.get(0)), new FloatValue(floatValues.get(0)));

        for (int i = 1; i < floatValues.size(); ++i) {
            float a = floatValues.get(i - 1);
            float b = floatValues.get(i);
            intervals.put(formatBetween(a, b), new FloatInterval(a, b));
            intervals.put(formatEquals(b), new FloatValue(b));
        }
    }

    private String formatBetween(float a, float b) {
        return "floatBetween" + String.valueOf(a).replace('.','p') + "and" + String.valueOf(b).replace('.','p') + 'r' + RandomHelper.getNext();
    }

    private String formatEquals(float a) {
        return "floatEqualsTo" + String.valueOf(a).replace('.','p') + 'r' + RandomHelper.getNext();
    }
}
