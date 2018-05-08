package declare.lang.trace;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class IntTraceAttribute {
    String name;
    int low;
    int high;

    public IntTraceAttribute(String name, int low, int high) {
        this.name = name;
        this.low = low;
        this.high = high;
    }


    public String getName() {
        return name;
    }

    public int getLow() {
        return low;
    }

    public int getHigh() {
        return high;
    }
}
