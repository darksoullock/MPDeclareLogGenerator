package core.models.serialization.trace;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class FloatTraceAttribute extends AbstractTraceAttribute {
    float low;
    float high;

    public FloatTraceAttribute(String name, float low, float high) {
        super(name);
        this.low = low;
        this.high = high;
    }


    @Override
    public String getValue() {
        float value = rnd.nextFloat() * (high - low) + low;
        return String.valueOf(value);
    }
}
