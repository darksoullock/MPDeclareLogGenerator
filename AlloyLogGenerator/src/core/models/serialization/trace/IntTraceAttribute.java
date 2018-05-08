package core.models.serialization.trace;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class IntTraceAttribute extends AbstractTraceAttribute {
    int low;
    int high;

    public IntTraceAttribute(String name, int low, int high) {
        super(name);
        this.low = low;
        this.high = high;
    }


    @Override
    public String getValue() {
        int value = rnd.nextInt(high - low) + low;
        return String.valueOf(value);
    }
}
