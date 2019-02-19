package declare.lang;

import java.util.Objects;

/**
 * Created by Vasiliy on 2017-11-30.
 */
public class Statement {
    String code;
    int line;

    public Statement(String code, int line) {
        this.code = code;
        this.line = line;
    }

    public String getCode() {
        return code;
    }

    public int getLine() {
        return line;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        Statement statement = (Statement) o;
        return line == statement.line &&
                Objects.equals(code, statement.code);
    }

    @Override
    public int hashCode() {
        return Objects.hash(code, line);
    }
}
