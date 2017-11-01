package core.models.serialization;

/**
 * Created by Vasiliy on 2017-09-27.
 */
public class Payload {
    String name;
    String value;
    String token;

    public Payload(String name, String value, String token) {
        this.name = name;
        this.value = value;
        this.token = token;
    }

    public String getName() {
        return name;
    }

    public String getValue() {
        return value;
    }

    public String getToken() {
        return token;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        Payload payload = (Payload) o;

        if (!name.equals(payload.name)) return false;
        return value.equals(payload.value);
    }

    @Override
    public int hashCode() {
        int result = name.hashCode();
        result = 31 * result + value.hashCode();
        return result;
    }
}
