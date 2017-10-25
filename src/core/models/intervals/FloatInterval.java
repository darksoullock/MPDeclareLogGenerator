package core.models.intervals;

import core.alloy.codegen.fnparser.DataExpression;
import core.models.intervals.Interval;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class FloatInterval extends Interval {

    float min;
    float max;

    public FloatInterval(float min, float max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String get() {
        return String.valueOf(rnd.nextFloat() * (max - min) + min);
    }

    @Override
    public boolean isCompliant(DataExpression expr) {
        throw new NotImplementedException();
    }
}
