package declare.lang;

import java.util.Objects;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class Activity {
    String name;

    public Activity(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Activity activity = (Activity) o;
        return Objects.equals(name, activity.name);
    }

    @Override
    public int hashCode() {
        return Objects.hash(name);
    }
}
