package core.models.serialization;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Created by Vasiliy on 2017-10-09.
 */
public class TraceProperty {    // TODO: review
    String name;
    String type;
    List<String> params;
    Random rand = new Random();

    public TraceProperty(String name, String type, List<String> params) {
        this.name = name;
        this.type = type;
        if (params == null)
            params = new ArrayList<>();
        this.params = params;
    }

    public boolean isDatetime() {
        return type.equals("datetime");
    }

    public String getName() {
        return name;
    }

    public String getValue() {  // TODO: negative numbers
        if (isDatetime())
            return LocalDate.now().toString();

        if (type.equals("int"))
            return params.get(0);

        if (type.equals("range"))
            return (Integer.parseInt(params.get(0)) + Math.abs(rand.nextInt(Integer.parseInt(params.get(1)) - Integer.parseInt(params.get(0))))) + "";

        if (type.equals("enum"))
            return params.get(Math.abs(rand.nextInt()) % params.size());

        throw new UnsupportedOperationException("Global trace attribute type '" + type + "' is invalid");
    }
}
