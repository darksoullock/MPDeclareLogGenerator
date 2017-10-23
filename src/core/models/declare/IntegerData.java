package core.models.declare;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class IntegerData extends EnumeratedData {
    int min;
    int max;

    public IntegerData(String type, int min, int max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    @Override
    public List<String> getValues() {
        throw new NotImplementedException();
    }
}
