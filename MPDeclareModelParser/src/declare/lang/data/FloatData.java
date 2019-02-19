package declare.lang.data;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class FloatData {
    private boolean required;
    private String type;
    private float min;
    private float max;

    public FloatData(String type, float min, float max, boolean required) {
        this.min = min;
        this.max = max;
        this.required = required;
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

    public boolean isRequired() {
        return required;
    }
}
