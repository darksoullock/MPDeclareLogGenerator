package parsing;

import core.alloy.codegen.AlloyCodeGenerator;
import core.models.declare.data.EnumeratedDataImpl;
import core.models.declare.data.FloatDataImpl;
import core.models.declare.data.IntegerDataImpl;
import core.models.declare.data.NumericDataImpl;
import declare.DeclareModel;
import declare.DeclareParser;
import declare.lang.DataConstraint;
import declare.lang.Statement;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;
import declare.lang.trace.EnumTraceAttribute;
import declare.lang.trace.FloatTraceAttribute;
import declare.lang.trace.IntTraceAttribute;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class ParserTest {
    DeclareParser parser = new DeclareParser();
    AlloyCodeGenerator gen = new AlloyCodeGenerator(2, 2, 2, 2, false, false);

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

    @Test
    public void testTraceAttributes() {
        List<EnumTraceAttribute> eta = new ArrayList<>();
        List<IntTraceAttribute> ita = new ArrayList<>();
        List<FloatTraceAttribute> fta = new ArrayList<>();
        parser.parseTraceAttributes(Arrays.asList(
                "trace AttrName: value1, value2",
                "trace Age integer between 10 and 100",
                "trace Angle float between 0.01 and 179.99"),
                eta,
                ita,
                fta);

        Assert.assertEquals(eta.size(), 1);
        Assert.assertEquals(ita.size(), 1);
        Assert.assertEquals(fta.size(), 1);

        Assert.assertEquals(eta.get(0).getName(), "AttrName");
        Assert.assertTrue(eta.get(0).getParams().get(0).contains("value"));

        Assert.assertEquals(ita.get(0).getName(), "Age");

        Assert.assertEquals(fta.get(0).getName(), "Angle");

        for (int i = 0; i < 100; ++i) {
            Assert.assertEquals(ita.get(0).getLow(), 10);
            Assert.assertEquals(ita.get(0).getHigh(), 100);
            Assert.assertTrue(Math.abs(fta.get(0).getLow() - 0.01) < 0.001);
            Assert.assertTrue(Math.abs(fta.get(0).getHigh() - 179.99) < 0.001);
        }
    }

    @Test
    public void testDataConstraints() throws declare.DeclareParserException {
        List<Statement> raw = Stream.of("Absence[BookTransport A] | A.Price is High and A.Speed is Low",
                "RespondedExistence[BookTransport A, UseTransport B] | A.TransportType is Car | B.Speed is not Low")
                .map(i -> new Statement(i, 0)).collect(Collectors.toList());
        List<DataConstraint> dcs = parser.parseDataConstraints(raw);
        Assert.assertEquals(dcs.size(), 2);
        DataConstraint first = dcs.get(0);
        DataConstraint second = dcs.get(1);
        Assert.assertEquals(first.getName(), "Absence");
        Assert.assertEquals(second.getName(), "RespondedExistence");
        Assert.assertEquals(first.taskA(), "BookTransport");
        Assert.assertEquals(second.taskA(), "BookTransport");
        Assert.assertEquals(second.taskB(), "UseTransport");
        Assert.assertEquals(first.getFirstFunction().getExpression().getNode().getValue(), "and");
        Assert.assertEquals(second.getSecondFunction().getExpression().getNode().getValue(), "is not");
    }
}
