package core.models.intervals;

import sun.plugin.dom.exception.InvalidStateException;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class IntegerValue extends IntegerInterval {
    public IntegerValue(int value) {
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
    public String getDifferent(String key) {
        throw new InvalidStateException("Impossible to get different value from " + get());
    }

    @Override
    public int getValueCount(int limit) {
        return 1;
    }
}
