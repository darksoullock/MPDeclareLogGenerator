package core.models.intervals;

import core.Exceptions.BadSolutionException;

import java.util.List;

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
    public String getSame(List<String> key) {
        return get();
    }

    @Override
    public String getDifferent(List<String> key) throws BadSolutionException {
        throw new BadSolutionException("Impossible to get different value from " + get());
    }

    @Override
    public int getValueCount(int limit) {
        return 1;
    }
}
