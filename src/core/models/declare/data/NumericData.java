package core.models.declare.data;

import core.models.intervals.Interval;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class NumericData extends EnumeratedData {
    Map<String, Interval> intervals;

    @Override
    public List<String> getValues() {
        if (intervals == null)
            generate();
        return new ArrayList<>(intervals.keySet());
    }

    public Map<String, Interval> getMapping() {
        if (intervals == null)
            generate();
        return intervals;
    }

    protected abstract void generate();

}
