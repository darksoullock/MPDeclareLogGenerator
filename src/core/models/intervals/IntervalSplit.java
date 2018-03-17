package core.models.intervals;

import core.interfaces.SafeFunction1;

/**
 * Created by Vasiliy on 2018-03-17.
 */
public class IntervalSplit {
    public IntervalSplit(String value) {
        this.value = value;
        left = right = true;
    }

    public IntervalSplit(String value, SplitSide side) {
        this.value = value;
        left = side == SplitSide.LEFT;
        right = side == SplitSide.RIGHT;
    }

    String value;
    boolean left;   // indicates on which side of value we want to split. When true split on 50 will produce {<50,>=50}
    boolean right;  // When true split on 50 will produce {<=50,>50}
    Object parsedValue;

    public String getValue() {
        return value;
    }

    public boolean isLeft() {
        return left;
    }

    public boolean isRight() {
        return right;
    }

    public enum SplitSide {
        LEFT, RIGHT
    }

    public <T> T getParsedValue(SafeFunction1<String, T> parser) {
        if (parsedValue == null)
            parsedValue = parser.invoke(value);

        return (T) parsedValue;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;

        IntervalSplit that = (IntervalSplit) o;

        if (left != that.left) return false;
        if (right != that.right) return false;
        return value.equals(that.value);
    }

    @Override
    public int hashCode() {
        int result = value.hashCode();
        result = 31 * result + (left ? 1 : 0);
        result = 31 * result + (right ? 1 : 0);
        return result;
    }
}
