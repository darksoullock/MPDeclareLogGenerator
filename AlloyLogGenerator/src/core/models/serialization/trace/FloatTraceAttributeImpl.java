package core.models.serialization.trace;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class FloatTraceAttributeImpl extends AbstractTraceAttribute {
    float low;
    float high;

    public FloatTraceAttributeImpl(String name, float low, float high) {
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
