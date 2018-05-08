package core.models.serialization;

import core.models.declare.data.NumericToken;

import java.util.Set;

/**
 * Created by Vasiliy on 2017-09-27.
 */
public class Payload {
    String name;
    String value;
    Set<NumericToken> tokens;

    public Payload(String name, String value, Set<NumericToken> tokens) {
        this.name = name;
        this.value = value;
        this.tokens = tokens;
    }

    public String getName() {
        return name;
    }

    public String getValue() {
        return value;
    }

    public Set<NumericToken> getTokens() {
        return tokens;
    }
}
