package core.models.declare.data;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class EnumeratedDataImpl {
    protected boolean required;
    protected String type;
    protected List<String> values;

    public EnumeratedDataImpl() {
        values = new ArrayList<>();
    }

    public EnumeratedDataImpl(String type, List<String> values, boolean required) {
        this.type = type;
        this.values = new ArrayList<>(values);
        this.required = required;
    }

    public String getType() {
        return type;
    }

    public List<String> getValues() {
        return values;
    }

    public void addValue(String value) {
        this.values.add(value);
    }

    public boolean isRequired() {
        return required;
    }
}
