package core.models.declare;

import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.List;

/**
 * Created by Vasiliy on 2017-10-17.
 */
public class NumericData extends EnumeratedData {
    int lowerBound;
    int higherBound;
    List<Integer> splits;
    boolean enumExpired;

    public NumericData(int lowerBound, int higherBound) {
        this.lowerBound = lowerBound;
        this.higherBound = higherBound;
        enumExpired = true;
    }

    @Override
    public List<String> getValues() {
        if (enumExpired){
            regenerate();
        }

        return values;
    }

    private void regenerate() { // TODO: implement
        throw new NotImplementedException();
    }

    @Override
    public void addValue(String value) {
        this.splits.add(Integer.parseInt(value));
    }
}
