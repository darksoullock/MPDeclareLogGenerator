package core.alloy.codegen.fnparser;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class Token {
    enum Type {Task, Variable, Operator, Set, Number, Comparator, Group }
    int position;
    Type type;
    String value;

    public Token(int position, Type type, String value) {
        this.position = position;
        this.type = type;
        this.value = value;
    }

    public Type getType() {
        return type;
    }

    public void setType(Type type) {
        this.type = type;
    }

    public String getValue() {
        return value;
    }

    public void setValue(String value) {
        this.value = value;
    }

    public int getPosition() {
        return position;
    }

    public void setPosition(int position) {
        this.position = position;
    }
}
