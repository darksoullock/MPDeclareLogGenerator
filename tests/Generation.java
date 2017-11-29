import core.Evaluator;
import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.Global;
import edu.mit.csail.sdg.alloy4.Err;
import org.deckfour.xes.model.XAttribute;
import org.deckfour.xes.model.XEvent;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.function.BiFunction;

/**
 * Created by Vasiliy on 2017-11-20.
 */
public class Generation {
    String baseDeclare = "/task definition\n" +
            "activity ApplyForTrip\n" +
            "activity ApproveApplication\n" +
            "activity BookTransport\n" +
            "activity BookAccomodation\n" +
            "activity CollectTickets\n" +
            "activity ArchiveDocuments\n" +
            "activity UseTransport\n" +
            "activity DoSomething\n" +
            "\n" +
            "/constraints\n" +
            "Init[ApplyForTrip]\n" +
            "Response[CollectTickets, ArchiveDocuments]\n" +
            "Precedence[BookTransport, ApproveApplication]\n" +
            "Precedence[BookAccomodation, ApproveApplication]\n" +
            "Precedence[CollectTickets, BookTransport]\n" +
            "Precedence[CollectTickets, BookAccomodation] \n" +
            "Absence[BookAccomodation, 2]\n" +
            "Absence[BookTransport, 3]\n" +
            "/ChainResponse[UseTransport, DoSomething]\n" +
            "/Existence[DoSomething]\n" +
            "Absence[ApplyForTrip, 1]\n" +
            "Existence[CollectTickets]\n" +
            "Existence[ArchiveDocuments]\n" +
            "Absence[ArchiveDocuments, 1]\n" +
            "Absence[ApproveApplication, 1]\n" +
            "\n" +
            "/data definition\n" +
            "TransportType: Car, Plane, Train, Bus\n" +
            "Something: One, None, Another\n" +
            "Price: float between 0 and 100\n" +
            "Speed: integer between 0 and 300\n" +
            "\n" +
            "/data binding\n" +
            "bind BookTransport: TransportType, Price, Speed\n" +
            "bind UseTransport: TransportType, Something, Price\n" +
            "bind DoSomething: Something\n";

    @Test
    public void testTraceAttributes() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        Global.encodeNames = true;
        String declare = baseDeclare +
                "trace one: '42'\n" +
                "trace num: integer between -42 and 42\n" +
                "trace floatnum: float between -1 and 1\n" +
                "trace enum: val1, val2, val3\n";

        XLog log = Evaluator.getLog(
                10,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);


        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            Assert.assertEquals(trace.getAttributes().size(), 5);

            Assert.assertEquals(getAttributeValue(trace.getAttributes().get("one")), "42");
            int intv = Integer.parseInt(getAttributeValue(trace.getAttributes().get("num")));
            float floatv = Float.parseFloat(getAttributeValue(trace.getAttributes().get("floatnum")));
            String enumv = getAttributeValue(trace.getAttributes().get("enum"));

            Assert.assertTrue(intv >= -42 && intv <= 42, "integer trace attribute is out of declared range. value: " + intv);
            Assert.assertTrue(floatv >= -1 && floatv <= 1, "float trace attribute is out of declared range. value: " + floatv);
            Assert.assertTrue(enumv.equals("val1") || enumv.equals("val2") || enumv.equals("val3"),
                    "enumerated trace attribute has value different from declared ones");
        }
    }

    @Test
    public void testInit() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare;

        XLog log = Evaluator.getLog(
                10,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            XEvent event = trace.get(0);
            Assert.assertEquals(getAttributeValue(event.getAttributes().get("concept:name")), "ApplyForTrip");
        }
    }

    private String getAttributeValue(XAttribute xAttribute) throws NoSuchFieldException, IllegalAccessException {
        Field valueField = XAttributeLiteralImpl.class.getDeclaredField("value");
        valueField.setAccessible(true);
        return valueField.get(xAttribute).toString();
    }

    @Test
    public void testExactlyAndChainResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "ChainResponse[DoSomething, UseTransport]\n" +
                "Absence[UseTransport, 3]\n" +
                "Exactly[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    Assert.assertEquals(getEventAttributeValue(trace.get(j + 1), "concept:name"), "UseTransport",
                            "ChainResponse constraint violated.");
                }
            }

            Assert.assertEquals(counter, 3, "Exactly[3] violated");
        }
    }

    @Test
    public void testExactlyAndNotChainResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainResponse[DoSomething, UseTransport]\n" +
                "Absence[UseTransport, 3]\n" +
                "Exactly[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size() - 1; ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    Assert.assertNotEquals(getEventAttributeValue(trace.get(j + 1), "concept:name"), "UseTransport",
                            "NotChainResponse constraint violated.");
                }
            }

            if (getEventAttributeValue(trace.get(trace.size() - 1), "concept:name").equals("DoSomething"))
                ++counter;

            Assert.assertEquals(counter, 3, "Exactly[3] violated");
        }
    }

    @Test
    public void testExactlyAndChainPrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "ChainPrecedence[DoSomething, UseTransport]\n" +
                "Absence[UseTransport, 3]\n" +
                "Exactly[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    Assert.assertEquals(getEventAttributeValue(trace.get(j - 1), "concept:name"), "UseTransport",
                            "ChainPrecedence constraint violated.");
                }
            }

            Assert.assertEquals(counter, 3, "Exactly[3] violated");
        }
    }

    @Test
    public void testExactlyAndNotChainPrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainPrecedence[DoSomething, UseTransport]\n" +
                "Absence[UseTransport, 3]\n" +
                "Exactly[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 1; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    Assert.assertNotEquals(getEventAttributeValue(trace.get(j - 1), "concept:name"), "UseTransport",
                            "NotChainPrecedence constraint violated.");
                }
            }

            if (getEventAttributeValue(trace.get(0), "concept:name").equals("DoSomething"))
                ++counter;

            Assert.assertEquals(counter, 3, "Exactly[3] violated");
        }
    }

    private String getEventAttributeValue(XEvent event, String attr) throws NoSuchFieldException, IllegalAccessException {
        XAttribute xAttribute = event.getAttributes().get(attr);
        Field valueField = XAttributeLiteralImpl.class.getDeclaredField("value");
        valueField.setAccessible(true);
        return valueField.get(xAttribute).toString();
    }

    @Test
    public void testExistenceAndResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Response[DoSomething, UseTransport]\n" +
                "Existence[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean needResponse = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    needResponse = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    needResponse = false;
                }
            }

            Assert.assertFalse(needResponse, "Response constraint violated.");
            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testExistenceAndNotResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotResponse[DoSomething, UseTransport]\n" +
                "Existence[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean latch = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    latch = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    Assert.assertFalse(latch, "NotResponse constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testExistenceAndPrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Precedence[DoSomething, UseTransport]\n" +
                "Existence[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean precede = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    Assert.assertTrue(precede, "Precedence constraint violated");
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    precede = true;
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testExistenceAndNotPrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotPrecedence[DoSomething, UseTransport]\n" +
                "Existence[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean occurence = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++counter;
                    Assert.assertFalse(occurence, "NotPrecedence constraint violated");
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    occurence = true;
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testDataBinding() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare;

        XLog log = Evaluator.getLog(
                15,
                5,
                100,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);

                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")) {
                    String tt = getEventAttributeValue(event, "TransportType");
                    Assert.assertTrue(tt.equals("Car") || tt.equals("Plane") || tt.equals("Train") || tt.equals("Bus"),
                            "Data binding value for enum is not valid");

                    float price = Float.parseFloat(getEventAttributeValue(event, "Price"));
                    Assert.assertTrue(price >= 0 && price <= 100, "Data binding for float is not valid. value: " + price);

                    int speed = Integer.parseInt(getEventAttributeValue(event, "Speed"));
                    Assert.assertTrue(speed >= 0 && speed <= 300, "Data binding for int is not valid. value: " + speed);

                } else if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    String tt = getEventAttributeValue(event, "TransportType");
                    Assert.assertTrue(tt.equals("Car") || tt.equals("Plane") || tt.equals("Train") || tt.equals("Bus"),
                            "Data binding value for enum is not valid. value: " + tt);

                    float price = Float.parseFloat(getEventAttributeValue(event, "Price"));
                    Assert.assertTrue(price >= 0 && price <= 100, "Data binding for float is not valid. value: " + price);

                    String sth = getEventAttributeValue(event, "Something");
                    Assert.assertTrue(sth.equals("One") || sth.equals("None") || sth.equals("Another"),
                            "Data binding value for enum is not valid. value: " + sth);

                } else if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    String sth = getEventAttributeValue(event, "Something");
                    Assert.assertTrue(sth.equals("One") || sth.equals("None") || sth.equals("Another"),
                            "Data binding value for enum is not valid. value: " + sth);

                } else {
                    Assert.assertFalse(event.getAttributes().containsKey("TransportType"), "This data is not binded but present");
                    Assert.assertFalse(event.getAttributes().containsKey("Price"), "This data is not binded but present");
                    Assert.assertFalse(event.getAttributes().containsKey("Speed"), "This data is not binded but present");
                    Assert.assertFalse(event.getAttributes().containsKey("Something"), "This data is not binded but present");
                }
            }
        }
    }

    @Test
    public void testChoice() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Choice[DoSomething, UseTransport]\n";

        XLog log = Evaluator.getLog(
                8,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean x = checkOccurrence(trace, "DoSomething", "UseTransport", (a, b) -> a || b);
            Assert.assertTrue(x, "ExclusiveChoice constraint violated");
        }
    }

    @Test
    public void testExclusiveChoice() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "ExclusiveChoice[DoSomething, UseTransport]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean x = checkOccurrence(trace, "DoSomething", "UseTransport", (a, b) -> (a || b) && !(a && b));
            Assert.assertTrue(x, "ExclusiveChoice constraint violated");
        }
    }

    @Test
    public void testExistence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Existence[DoSomething]\n";

        XLog log = Evaluator.getLog(
                7,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean ok = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ok = true;
                }
            }

            Assert.assertTrue(ok, "Existence constraint violated");
        }
    }

    @Test
    public void testAbsenceN() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Absence[DoSomething, 3]\n" +
                "Existence[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int count = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ++count;
                }
            }

            Assert.assertTrue(count <= 3, "Absence[3] constraint violated. count = " + count);
        }
    }

    @Test
    public void testAbsence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Absence[DoSomething]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        boolean ok = true;
        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    ok = false;
                }
            }

            Assert.assertTrue(ok, "Absence constraint violated.");
        }
    }

    @Test
    public void testRespondedExistence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "RespondedExistence[DoSomething, UseTransport]\n";

        XLog log = Evaluator.getLog(
                8,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean x = checkOccurrence(trace, "DoSomething", "UseTransport", (a, b) -> !a || b);
            Assert.assertTrue(x, "RespondedExistence constraint violated");

        }
    }

    @Test
    public void testNotRespondedExistence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotRespondedExistence[DoSomething, UseTransport]\n";

        XLog log = Evaluator.getLog(
                8,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean x = checkOccurrence(trace, "DoSomething", "UseTransport", (a, b) -> !a || !b);
            Assert.assertTrue(x, "NotRespondedExistence constraint violated");

        }
    }

    private boolean checkOccurrence(XTrace trace, String taskA, String taskB, BiFunction<Boolean, Boolean, Boolean> predicate) throws NoSuchFieldException, IllegalAccessException {
        boolean a = false;
        boolean b = false;
        for (int j = 0; j < trace.size(); ++j) {
            XEvent event = trace.get(j);
            if (getEventAttributeValue(event, "concept:name").equals(taskA)) {
                a = true;
            }
            if (getEventAttributeValue(event, "concept:name").equals(taskB)) {
                b = true;
            }
        }

        return predicate.apply(a, b);
    }

    @Test
    public void testAlternateResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "AlternateResponse[DoSomething, UseTransport]\n" +
                "Exactly[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean awaiting = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    Assert.assertFalse(awaiting, "AlternateResponse constraint violated: two parallel activation");
                    awaiting = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    awaiting = false;
                }
            }

            Assert.assertFalse(awaiting, "AlternateResponse violated");
        }
    }

    @Test
    public void testAlternatePrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "AlternatePrecedence[DoSomething, UseTransport]\n" +
                "Exactly[DoSomething, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false);

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int preceded = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")) {
                    Assert.assertTrue(preceded > 0, "AlternatePrecedence constraint violated");
                    preceded = 0;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")) {
                    ++preceded;
                }
            }
        }
    }
}




