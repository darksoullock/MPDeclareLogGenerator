package core.models.intervals;

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
}
