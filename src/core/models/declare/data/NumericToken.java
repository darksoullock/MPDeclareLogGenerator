package core.models.declare.data;

/**
 * Created by Vasiliy on 2017-11-03.
 */
public class NumericToken {
    public enum Type {Same, Different}

    Type type;
    String value;

    public NumericToken(Type type, String value) {
        this.type = type;
        this.value = value;
    }

    public Type getType() {
        return type;
    }

    public String getValue() {
        return value;
    }
}
