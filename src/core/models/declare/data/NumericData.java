package core.models.declare.data;

import core.models.intervals.Interval;

import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class NumericData extends EnumeratedData {
    public abstract Map<String, Interval> getMapping();
}
