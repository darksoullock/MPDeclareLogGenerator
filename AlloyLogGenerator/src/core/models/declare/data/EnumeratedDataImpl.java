package core.models.declare.data;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class EnumeratedDataImpl {
    String type;
    List<String> values;

    public EnumeratedDataImpl() {
        values = new ArrayList<>();
    }

    public EnumeratedDataImpl(String type, List<String> values) {
        this.type = type;
        this.values = new ArrayList<>(values);
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
}
