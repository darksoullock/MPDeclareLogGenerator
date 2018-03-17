package intervals;

import core.Exceptions.DeclareParserException;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.FloatData;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;
import core.models.intervals.*;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;

/**
 * Created by Vasiliy on 2017-11-08.
 */
public class NumericDataTest {
    @Test
    public void EnumeratedDataTest() throws DeclareParserException {
        EnumeratedData data = new EnumeratedData("data", Arrays.asList("v1", "v2"));
        data.addValue("v3");
        Assert.assertEquals(data.getType(), "data");
        Assert.assertEquals(data.getValues().size(), 3);
    }

    @Test
    public void IntegerDataNoValuesTest() {
        NumericData data = new IntegerData("idata", 0, 100, 1);
        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 1);
        Assert.assertTrue(data.getMapping().containsKey(data.getValues().get(0)));
        Assert.assertTrue(data.getMapping().get(data.getValues().get(0)) instanceof IntegerInterval);
    }

    @Test
    public void IntegerDataTest() throws DeclareParserException {
        NumericData data = new IntegerData("idata", 0, 100, 1);
        data.addSplit(new IntervalSplit("30"));
        data.addSplit(new IntervalSplit("60"));
        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 5);
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof IntegerValue));
        Assert.assertTrue(data.getValues().stream().allMatch(i -> data.getMapping().get(i) instanceof IntegerInterval));
    }

    @Test
    public void IntegerDataTest2() throws DeclareParserException {
        int increment = 10_000;
        NumericData data = new IntegerData("idata", -2000000+1, 2000000-1, 1);  // -1 and +1 as min and max values in constructor are included in range
        for (int i = 0; i < 100; ++i) {
            data.addSplit(new IntervalSplit(String.valueOf(increment * i)));
            data.addSplit(new IntervalSplit(String.valueOf(-increment * i)));
        }

        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 399); // 199 (200 minus duplicate zero) values + 200 intervals
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof IntegerValue));
        Assert.assertTrue(data.getValues().stream().allMatch(i -> data.getMapping().get(i) instanceof IntegerInterval));
        for (String key : data.getMapping().keySet()) {
            Interval intl = data.getMapping().get(key);
            if (intl instanceof IntegerInterval) {
                IntegerInterval ii = (IntegerInterval) intl;
                Assert.assertEquals(ii.getMin() % increment, 0);
                Assert.assertEquals(ii.getMax() % increment, 0);
            } else {
                IntegerValue iv = (IntegerValue) intl;
                Assert.assertEquals(iv.getMin() % increment, 0);
            }
        }
    }

    @Test
    public void IntegerDataSplitsTest() throws DeclareParserException {
        NumericData data = new IntegerData("idata", -2000000 + 1, 2000000 - 1, 1000);
        for (String key : data.getMapping().keySet()) {
            Interval intl = data.getMapping().get(key);
            if (intl instanceof IntegerInterval) {
                IntegerInterval ii = (IntegerInterval) intl;
                if (ii.getMin() != -2000000)    //once, edge case
                    Assert.assertEquals((ii.getMin() + 1) % 4000, 0);
                Assert.assertEquals(ii.getMax() % 4000, 0);
            }
        }
    }

    @Test
    public void FloatDataNoValuesTest() {
        NumericData data = new FloatData("idata", 0, 100, 1);
        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 1);
        Assert.assertTrue(data.getMapping().containsKey(data.getValues().get(0)));
        Assert.assertTrue(data.getMapping().get(data.getValues().get(0)) instanceof FloatInterval);
    }

    @Test
    public void FloatDataTest() throws DeclareParserException {
        NumericData data = new FloatData("idata", 0, 100, 1);
        data.addSplit(new IntervalSplit("30"));
        data.addSplit(new IntervalSplit("60"));
        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 5);
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof FloatValue));
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof FloatInterval));
    }
}
