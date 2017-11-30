package parsing;

import core.Exceptions.DeclareParserException;
import core.alloy.codegen.DeclareParser;
import core.models.declare.DataConstraint;
import core.models.declare.Statement;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.FloatData;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;
import core.models.serialization.trace.AbstractTraceAttribute;
import core.models.serialization.trace.EnumTraceAttribute;
import core.models.serialization.trace.FloatTraceAttribute;
import core.models.serialization.trace.IntTraceAttribute;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class ParserTest {
    DeclareParser parser = new DeclareParser(1);

    @Test
    public void testData() {
        Map<String, NumericData> map = new HashMap<>();
        List<EnumeratedData> data = parser.parseData(Arrays.asList(
                "TransportType: Car, Plane, Train, Bus",
                "Price integer between 0 and 300",
                "Angle float between 0 and 180"), map);

        Assert.assertEquals(data.size(), 3);
        Assert.assertEquals(map.size(), 2);

        EnumeratedData d1 = data.get(0);
        EnumeratedData d2 = data.get(1);
        EnumeratedData d3 = data.get(2);

        Assert.assertEquals(d1.getType(), "TransportType");
        Assert.assertEquals(d1.getValues().size(), 4);

        Assert.assertTrue(d2 instanceof IntegerData);
        Assert.assertEquals(d2.getType(), "Price");
        Assert.assertEquals(d2.getValues().size(), 1);

        Assert.assertTrue(d3 instanceof FloatData);
        Assert.assertEquals(d3.getType(), "Angle");
        Assert.assertEquals(d3.getValues().size(), 1);

        Assert.assertTrue(map.containsKey(d2.getType()));
        Assert.assertTrue(map.containsKey(d3.getType()));

        NumericData nd1 = map.get(d2.getType());
        NumericData nd2 = map.get(d3.getType());

        Assert.assertEquals(nd1, d2);
        Assert.assertEquals(nd2, d3);

        Assert.assertEquals(nd1.getMapping().size(), 1);
        Assert.assertEquals(nd2.getMapping().size(), 1);
    }

    @Test
    public void testTraceAttributes() {
        List<AbstractTraceAttribute> ta = parser.parseTraceAttributes(Arrays.asList(
                "trace AttrName: value1, value2",
                "trace Age integer between 10 and 100",
                "trace Angle float between 0.01 and 179.99"));

        Assert.assertEquals(ta.size(), 3);
        AbstractTraceAttribute a1 = ta.get(0);
        AbstractTraceAttribute a2 = ta.get(1);
        AbstractTraceAttribute a3 = ta.get(2);

        Assert.assertTrue(a1 instanceof EnumTraceAttribute);
        Assert.assertEquals(a1.getName(), "AttrName");
        Assert.assertTrue(a1.getValue().contains("value"));

        Assert.assertTrue(a2 instanceof IntTraceAttribute);
        Assert.assertEquals(a2.getName(), "Age");

        Assert.assertTrue(a3 instanceof FloatTraceAttribute);
        Assert.assertEquals(a3.getName(), "Angle");

        for (int i = 0; i < 100; ++i) {
            int in = Integer.parseInt(a2.getValue());
            float f = Float.parseFloat(a3.getValue());
            Assert.assertTrue(in < 100 && in >= 10);
            Assert.assertTrue(f <= 179.99 && in >= 0.01);
        }
    }

    @Test
    public void testDataConstraints() throws DeclareParserException {
        List<Statement> raw = Stream.of("Absence[BookTransport A] | A.Price is High and A.Speed is Low",
                "RespondedExistence[BookTransport A, UseTransport B] | A.TransportType is Car | B.Speed is not Low")
                .map(i -> new Statement(i, 0)).collect(Collectors.toList());
        List<DataConstraint> dcs = parser.parseDataConstraints(raw, null);
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
