package core.models.serialization.trace;

import java.time.LocalDate;
import java.util.ArrayList;
import java.util.List;
import java.util.Random;

/**
 * Created by Vasiliy on 2017-10-09.
 */
public abstract class AbstractTraceAttribute {
    String name;
    Random rnd = new Random();

    public AbstractTraceAttribute(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public abstract String getValue();
}
