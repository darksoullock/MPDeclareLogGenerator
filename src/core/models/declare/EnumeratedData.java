package core.models.declare;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class EnumeratedData {
    String type;
    List<String> values;

    public EnumeratedData() {
        values = new ArrayList<>();
    }

    public EnumeratedData(String type, List<String> values) {
        this.type = type;
        this.values = values;
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
