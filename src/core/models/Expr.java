package core.models;

/**
 * Created by Vasiliy on 2017-10-03.
 */
public class Expr { // TODO: redo
    public Expr(String name, int val1, int val2) {
        this.name = name;
        this.value1 = val1;
        this.value2 = val2;
    }

    String name;
    int value1;
    int value2;

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public int getValue1() {
        return value1;
    }

    public void setValue1(int value1) {
        this.value1 = value1;
    }

    public int getValue2() {
        return value2;
    }

    public void setValue2(int value2) {
        this.value2 = value2;
    }
}
