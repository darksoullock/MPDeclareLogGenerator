package parsing;

import core.alloy.codegen.DeclareParser;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;
import java.util.List;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class StatementIdTest {
    DeclareParser parser = new DeclareParser(1);

    List<String> tasks = Arrays.asList(
            "activity ApplyForTrip",
            "activity BookAccomodation",
            "activity CollectTickets");

    List<String> constraints = Arrays.asList(
            "Init[ApplyForTrip]",
            "Response[CollectTickets, ArchiveDocuments]",
            "Precedence[CollectTickets, BookAccomodation]",
            "Absence[BookAccomodation, 2]");

    List<String> data = Arrays.asList(
            "TransportType: Car, Plane, Train, Bus",
            "Price: integer between 0 and 300",
            "Angle: float between 0 and 180");

    List<String> dataBinding = Arrays.asList(
            "bind BookMeansOfTransport: TransportType",
            "bind UseTransport: TransportType, Something");

    List<String> dataConstraints = Arrays.asList(
            "Absence[BookMeansOfTransport A] | A.TransportType is Plane and A.Distance is not Big",
            "Response[BookMeansOfTransport A, UseTransport B] | A.TransportType is Plane | B.TransportType is not Train",
            "Response[BookMeansOfTransport A, UseTransport B] || same TransportType");

    List<String> traceAttributes = Arrays.asList(
            "trace AlwaysSame: 42",
            "trace RandomNumber: integer between 42 and 422",
            "trace RandomFloatNumber: float between 42 and 422",
            "trace Enum: enum, values, v2, v3");

    @Test
    public void testIsTask() {
        testIsX(tasks, true, false, false, false, false, false);
    }

    @Test
    public void testIsConstraint() {
        testIsX(constraints, false, true, false, false, false, false);
    }

    @Test
    public void testIsData() {
        testIsX(data, false, false, true, false, false, false);
    }

    @Test
    public void testDataBinding() {
        testIsX(dataBinding, false, false, false, true, false, false);
    }

    @Test
    public void testIsDataConstraints() {
        testIsX(dataConstraints, false, false, false, false, true, false);
    }

    @Test
    public void testIsTraceAttributes() {
        testIsX(traceAttributes, false, false, false, false, false, true);
    }

    private void testIsX(List<String> items, boolean task, boolean constraint, boolean data, boolean dataBinding, boolean dataConstraint, boolean traceAttribute) {
        for (String item : items) {
            Assert.assertEquals(parser.isTask(item), task);
            Assert.assertEquals(parser.isConstraint(item), constraint);
            Assert.assertEquals(parser.isData(item), data);
            Assert.assertEquals(parser.isDataBinding(item), dataBinding);
            Assert.assertEquals(parser.isDataConstraint(item), dataConstraint);
            Assert.assertEquals(parser.isTraceAttribute(item), traceAttribute);
        }
    }


}
