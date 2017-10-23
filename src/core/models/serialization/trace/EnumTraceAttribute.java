package core.models.serialization.trace;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class EnumTraceAttribute extends AbstractTraceAttribute {
    List<String> params;

    public EnumTraceAttribute(String name, List<String> params) {
        super(name);
        this.params = params;
    }

    @Override
    public String getValue() {
        return params.get(rnd.nextInt(params.size()));
    }
}
