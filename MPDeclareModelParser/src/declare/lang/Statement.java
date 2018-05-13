package declare.lang;

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
}
