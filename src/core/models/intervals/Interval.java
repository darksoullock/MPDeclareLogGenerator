package core.models.intervals;

import core.alloy.codegen.fnparser.DataExpression;

import java.util.Random;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class Interval {
    protected Random rnd = new Random();
    public abstract String get();
    public abstract boolean isCompliant(DataExpression expr);
}
