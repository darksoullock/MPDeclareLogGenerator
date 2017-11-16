package intervals;

import core.models.declare.data.EnumeratedData;
import core.models.declare.data.FloatData;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;
import core.models.intervals.FloatInterval;
import core.models.intervals.FloatValue;
import core.models.intervals.IntegerInterval;
import core.models.intervals.IntegerValue;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;

/**
 * Created by Vasiliy on 2017-11-08.
 */
public class NumericDataTest {
    @Test
    public void EnumeratedDataTest() {
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
    public void IntegerDataTest() {
        NumericData data = new IntegerData("idata", 0, 100, 1);
        data.addValue("30");
        data.addValue("60");
        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 5);
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof IntegerValue));
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof IntegerInterval));
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
    public void FloatDataTest() {
        NumericData data = new FloatData("idata", 0, 100, 1);
        data.addValue("30");
        data.addValue("60");
        Assert.assertEquals(data.getType(), "idata");
        Assert.assertEquals(data.getValues().size(), 5);
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof FloatValue));
        Assert.assertTrue(data.getValues().stream().anyMatch(i -> data.getMapping().get(i) instanceof FloatInterval));
    }
}
