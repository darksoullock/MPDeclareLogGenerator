package declare.lang.trace;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class EnumTraceAttribute {
    String name;
    List<String> params;

    public EnumTraceAttribute(String name, List<String> params) {
        this.name = name;
        this.params = params;
    }

    public String getName() {
        return name;
    }

    public List<String> getParams() {
        return params;
    }
}
