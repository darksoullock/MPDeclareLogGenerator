package parsing;

import core.alloy.codegen.AlloyCodeGenerator;
import core.models.declare.data.EnumeratedDataImpl;
import core.models.declare.data.FloatDataImpl;
import core.models.declare.data.IntegerDataImpl;
import core.models.declare.data.NumericDataImpl;
import declare.DeclareModel;
import declare.DeclareParser;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class ParserTest {
    DeclareParser parser = new DeclareParser();
    AlloyCodeGenerator gen = new AlloyCodeGenerator(2, 2, 2, 2, false, false, true);

    @Test
    public void testData() {
        List<EnumeratedData> ed = new ArrayList<>();
        List<IntegerData> id = new ArrayList<>();
        List<FloatData> fd = new ArrayList<>();
        parser.parseData(Arrays.asList(
                "TransportType: Car, Plane, Train, Bus",
                "Price integer between 0 and 300",
                "Angle float between 0 and 180"),
                ed, id, fd);

        DeclareModel model = new DeclareModel();
        model.setEnumeratedData(ed);
        model.setIntegerData(id);
        model.setFloatData(fd);
        List<EnumeratedDataImpl> data = gen.collectData(model, 1);
        Map<String, NumericDataImpl> map = gen.fillNumericDataMap(data);

        Assert.assertEquals(data.size(), 3);
        Assert.assertEquals(map.size(), 2);

        EnumeratedDataImpl d1 = data.get(0);
        EnumeratedDataImpl d2 = data.get(1);
        EnumeratedDataImpl d3 = data.get(2);

        Assert.assertEquals(d1.getType(), "TransportType");
        Assert.assertEquals(d1.getValues().size(), 4);

        Assert.assertTrue(d2 instanceof IntegerDataImpl);
        Assert.assertEquals(d2.getType(), "Price");
        Assert.assertEquals(d2.getValues().size(), 1);

        Assert.assertTrue(d3 instanceof FloatDataImpl);
        Assert.assertEquals(d3.getType(), "Angle");
        Assert.assertEquals(d3.getValues().size(), 1);

        Assert.assertTrue(map.containsKey(d2.getType()));
        Assert.assertTrue(map.containsKey(d3.getType()));

        NumericDataImpl nd1 = map.get(d2.getType());
        NumericDataImpl nd2 = map.get(d3.getType());

        Assert.assertEquals(nd1, d2);
        Assert.assertEquals(nd2, d3);

        Assert.assertEquals(nd1.getMapping().size(), 1);
        Assert.assertEquals(nd2.getMapping().size(), 1);
    }
}
