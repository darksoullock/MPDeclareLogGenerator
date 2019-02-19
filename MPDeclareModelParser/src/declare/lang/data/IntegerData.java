package declare.lang.data;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class IntegerData {
    private boolean required;
    private String type;
    private int min;
    private int max;

    public IntegerData(String type, int min, int max, boolean required) {
        this.min = min;
        this.max = max;
        this.type = type;
        this.required = required;
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

    public boolean isRequired() {
        return required;
    }
}
