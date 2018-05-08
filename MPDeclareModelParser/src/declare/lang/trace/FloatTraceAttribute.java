package declare.lang.trace;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class FloatTraceAttribute {
    String name;
    float low;
    float high;

    public FloatTraceAttribute(String name, float low, float high) {
        this.name = name;
        this.low = low;
        this.high = high;
    }

    public String getName() {
        return name;
    }

    public float getLow() {
        return low;
    }

    public float getHigh() {
        return high;
    }
}
