package declare.lang.data;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class EnumeratedData {
    private boolean required;
    private String type;
    private List<String> values;

    public EnumeratedData() {
        values = new ArrayList<>();
    }

    public EnumeratedData(String type, List<String> values, boolean required) {
        this.required = required;
        this.type = type;
        this.values = new ArrayList<>(values);
    }

    public String getType() {
        return type;
    }

    public List<String> getValues() {
        return values;
    }

    public boolean isRequired() {
        return required;
    }
}
