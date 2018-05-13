package declare;

import declare.lang.DataConstraint;
import declare.lang.Statement;
import declare.lang.trace.EnumTraceAttribute;
import declare.lang.trace.FloatTraceAttribute;
import declare.lang.trace.IntTraceAttribute;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class ParserTest {
    DeclareParser parser = new DeclareParser();

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
    public void testDataConstraints() throws DeclareParserException {
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
