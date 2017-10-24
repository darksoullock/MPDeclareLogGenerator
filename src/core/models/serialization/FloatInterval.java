package core.models.serialization;

import core.models.Interval;

import java.util.Random;

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
    public String get(){
        return String.valueOf(rnd.nextFloat()*(max-min)+min);
    }
}
