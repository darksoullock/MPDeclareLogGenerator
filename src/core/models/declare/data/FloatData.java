package core.models.declare.data;

import core.models.intervals.Interval;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatData extends NumericData {
    float min;
    float max;

    @Override
    public List<String> getValues() {
        throw new NotImplementedException();
    }

    public FloatData(String type, float min, float max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    @Override
    public Map<String, Interval> getMapping() {
        throw new NotImplementedException();
    }
}
