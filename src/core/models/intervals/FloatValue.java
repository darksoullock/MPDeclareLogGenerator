package core.models.intervals;

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
}
