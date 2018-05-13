package declare.lang.data;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatData {
    String type;
    float min;
    float max;

    public FloatData(String type, float min, float max) {
        this.min = min;
        this.max = max;
        this.type = type;
    }

    public String getType() {
        return type;
    }

    public float getMin() {
        return min;
    }

    public float getMax() {
        return max;
    }
}
