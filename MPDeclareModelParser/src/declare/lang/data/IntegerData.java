package declare.lang.data;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class IntegerData {
    String type;
    int min;
    int max;

    public IntegerData(String type, int min, int max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    public String getType() {
        return type;
    }

    public int getMin() {
        return min;
    }

    public int getMax() {
        return max;
    }
}
