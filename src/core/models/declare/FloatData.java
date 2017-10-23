package core.models.declare;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatData extends EnumeratedData {
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
}
