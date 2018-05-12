package core.models.declare.data;

import core.Exceptions.GenerationException;
import core.models.intervals.Interval;
import core.models.intervals.IntervalSplit;
import declare.DeclareParserException;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class NumericDataImpl extends EnumeratedDataImpl {
    Map<String, Interval> intervals;
    List<IntervalSplit> splits = new ArrayList<>();

    @Override
    public List<String> getValues() {
        if (intervals == null)
            generate();
        return new ArrayList<>(intervals.keySet());
    }

    public Map<String, Interval> getMapping() {
        if (intervals == null)
            generate();
        return intervals;
    }

    @Override
    public final void addValue(String value) {
        throw new UnsupportedOperationException("Use 'addSplit' method for numeric data");
    }

    public abstract void addSplit(IntervalSplit s) throws GenerationException, DeclareParserException;

    protected abstract void generate();

}
