package core.models.declare.data;

import core.Exceptions.DeclareParserException;

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
        this.values = new ArrayList<>(values);
    }

    public String getType() {
        return type;
    }

    public List<String> getValues() {
        return values;
    }

    public void addValue(String value) throws DeclareParserException {
        this.values.add(value);
    }
}