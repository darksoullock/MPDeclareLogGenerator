package core.models.intervals;

import sun.plugin.dom.exception.InvalidStateException;

/**
 * Created by Vasiliy on 2017-10-26.
 */
public class FloatValue extends FloatInterval {
    public FloatValue(float value) {
        super(value, value);
    }

    @Override
    public String get() {
        return String.valueOf(max);
    }

    @Override
    public String getSame(String key) {
        return get();
    }

    @Override
    public String getDifferent(String hash) {
        throw  new InvalidStateException("Impossible to get different value for this interval");
    }

    @Override
    public int getValueCount(int limit) {
        return 1;
    }
}
