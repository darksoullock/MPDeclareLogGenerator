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
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.HashSet;
import java.util.Set;

/**
 * Created by Vasiliy on 2017-11-20.
 */
public class GenerationWithData {
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
    public void testInit() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare
                + "Init[ApplyForTrip A]|A.Something is One\n"
                + "bind ApplyForTrip: Something\n";

        XLog log = Evaluator.getLog(
                6,
                5,
                100,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            XEvent event = trace.get(0);
            Assert.assertEquals(getAttributeValue(event.getAttributes().get("concept:name")), "ApplyForTrip");
            Assert.assertEquals(getAttributeValue(event.getAttributes().get("Something")), "One");
        }
    }

    private String getAttributeValue(XAttribute xAttribute) throws NoSuchFieldException, IllegalAccessException {
        Field valueField = XAttributeLiteralImpl.class.getDeclaredField("value");
        valueField.setAccessible(true);
        return valueField.get(xAttribute).toString();
    }

    @Test
    public void testExactlyAndChainResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "ChainResponse[BookTransport A, UseTransport B]|A.TransportType is Train|same Price\n" +
                "Exactly[BookTransport A, 3]|A.TransportType is Train\n";

        XLog log = Evaluator.getLog(
                18,
                5,
                50,
                3,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Train")) {
                    ++counter;
                    Assert.assertEquals(getEventAttributeValue(event, "Price"),
                            getEventAttributeValue(trace.get(j + 1), "Price"),
                            "ChainResponse constraint violated.");
                }
            }

            Assert.assertEquals(counter, 3, "Exactly[3] violated");
        }
    }

    @Test
    public void testExistenceAndNotChainResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainResponse[BookTransport A, UseTransport B]|A.TransportType is Train|B.TransportType in (Car, Bus, Plane)\n" +
                "Existence[BookTransport A, 3]|A.TransportType is Train\n" +
                "ChainResponse[BookTransport, UseTransport]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Train")) {
                    ++counter;
                    Assert.assertTrue(j == trace.size() - 1
                                    || !getEventAttributeValue(event, "concept:name").equals("UseTransport")
                                    || getEventAttributeValue(event, "TransportType").equals("Train"),
                            "NotChainResponse constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated");
        }
    }

    @Test
    public void testExistenceAndNotChainResponse2() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainResponse[BookTransport A, UseTransport B]|A.TransportType is Train|\n" +
                "Existence[BookTransport A, 3]|A.TransportType is Train\n" +
                "Existence[UseTransport, 10]\n";

        XLog log = Evaluator.getLog(
                25,
                5,
                250,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Train")) {
                    ++counter;
                    Assert.assertTrue(j == trace.size() - 1
                                    || !getEventAttributeValue(event, "concept:name").equals("UseTransport"),
                            "NotChainResponse constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated");
        }
    }

    @Test
    public void testExistenceAndNotChainResponseWithDifferent() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainResponse[BookTransport A, UseTransport B]|A.TransportType is Train|different Price\n" +
                "Existence[BookTransport A, 3]|A.TransportType is Train\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Train")) {
                    ++counter;
                    Assert.assertTrue(j == trace.size() - 1
                                    || !getEventAttributeValue(event, "concept:name").equals("UseTransport")
                                    || getEventAttributeValue(event, "Price") == getEventAttributeValue(trace.get(j + 1), "Price"),
                            "NotChainResponse constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated");
        }
    }

    @Test
    public void testChainPrecedence() throws
            IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "ChainPrecedence[UseTransport A, BookTransport B]|A.TransportType is Car|different TransportType\n" +
                "Existence[UseTransport U, 3]|U.TransportType is Car\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Car")) {
                    ++counter;
                    Assert.assertEquals(getEventAttributeValue(trace.get(j - 1), "concept:name"), "BookTransport",
                            "ChainPrecedence constraint violated.");
                    Assert.assertNotEquals(getEventAttributeValue(trace.get(j - 1), "TransportType"), "Car",
                            "ChainPrecedence constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated");
        }
    }

    @Test
    public void testExactlyAndNotChainPrecedence() throws
            IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainPrecedence[UseTransport A, BookTransport B]|A.TransportType is Car|different TransportType\n" +
                "Existence[UseTransport U, 3]|U.TransportType is Car\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Car")
                        && j > 0) {
                    ++counter;
                    Assert.assertTrue(!getEventAttributeValue(trace.get(j - 1), "concept:name").equals("BookTransport")
                                    || getEventAttributeValue(trace.get(j - 1), "TransportType").equals("Car"),
                            "NotChainPrecedence constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated");
        }
    }

    @Test
    public void testExactlyAndNotChainPrecedence2() throws
            IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotChainPrecedence[UseTransport A, BookTransport B]|A.TransportType is Car|\n" +
                "Existence[UseTransport U, 3]|U.TransportType is Car\n" +
                "Existence[BookTransport, 3]\n";

        XLog log = Evaluator.getLog(
                24,
                2,
                250,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Car")
                        && j > 0) {
                    ++counter;
                    Assert.assertTrue(!getEventAttributeValue(trace.get(j - 1), "concept:name").equals("BookTransport"),
                            "NotChainPrecedence constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated");
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
        String declare = baseDeclare + "Response[BookTransport A, UseTransport B]|A.Price<10|10<B.Price\n" +
                "Existence[BookTransport A, 3]|A.Price<10\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean needResponse = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) < 10) {
                    ++counter;
                    needResponse = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) > 10) {
                    needResponse = false;
                }
            }

            Assert.assertFalse(needResponse, "Response constraint violated.");
            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testExistenceAndNotResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotResponse[BookTransport A, UseTransport B]|A.Price<10|B.Price>10\n" +
                "Existence[BookTransport A, 3]|A.Price<10\n" +
                "Existence[UseTransport A]|A.Price>10\n";

        XLog log;
        log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean latch = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) < 10) {
                    ++counter;
                    latch = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) > 10) {
                    Assert.assertFalse(latch, "NotResponse constraint violated.");
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testExistenceAndPrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Precedence[UseTransport A, BookTransport B]|A.Price>10|same Price\n" +
                "Existence[UseTransport A, 3]|A.Price>10\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                3,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            Set<Float> values = new HashSet<>();
            boolean precede = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) > 10) {
                    ++counter;
                    Assert.assertTrue(precede, "Precedence constraint violated");
                    Assert.assertTrue(values.contains(Float.parseFloat(getEventAttributeValue(event, "Price"))), "'same' data constraint violated");
                }
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) > 10) {
                    precede = true;
                    values.add(Float.parseFloat(getEventAttributeValue(event, "Price")));
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testExistenceAndNotPrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotPrecedence[UseTransport A, BookTransport B]|A.Price>10|B.Price>10\n" +
                "Existence[UseTransport A, 3]|A.Price>10\n" +
                "Existence[BookTransport, 3]\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int counter = 0;
            boolean precede = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) > 10) {
                    ++counter;
                    Assert.assertFalse(precede, "NotPrecedence constraint violated");
                }
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && Float.parseFloat(getEventAttributeValue(event, "Price")) > 10) {
                    precede = true;
                }
            }

            Assert.assertTrue(counter >= 3, "Existence[3] violated; actual value: " + counter);
        }
    }

    @Test
    public void testChoice() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Choice[DoSomething A, UseTransport B]|A.Something is One|B.Something is One\n";

        XLog log;
        log = Evaluator.getLog(
                8,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");
        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean ok = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if ((getEventAttributeValue(event, "concept:name").equals("DoSomething")
                        || getEventAttributeValue(event, "concept:name").equals("UseTransport"))
                        && getAttributeValue(event.getAttributes().get("Something")).equals("One")) {
                    ok = true;
                }
            }

            Assert.assertTrue(ok, "Choice constraint violated");
        }
    }

    @Test
    public void testExclusiveChoice() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "ExclusiveChoice[DoSomething A, UseTransport B]|A.Something is One|B.Something is One\n";

        XLog log = Evaluator.getLog(
                18,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean a = false;
            boolean b = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")
                        && getAttributeValue(event.getAttributes().get("Something")).equals("One")) {
                    a = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getAttributeValue(event.getAttributes().get("Something")).equals("One")) {
                    b = true;
                }
            }

            Assert.assertTrue((a || b) && !(a && b), "ExclusiveChoice constraint violated");
        }
    }

    @Test
    public void testExistence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Existence[DoSomething A]|A.Something is not One\n";

        XLog log = Evaluator.getLog(
                7,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean ok = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")
                        && !getEventAttributeValue(event, "Something").equals("One")) {
                    ok = true;
                }
            }

            Assert.assertTrue(ok, "Existence constraint violated");
        }
    }

    @Test
    public void testAbsenceN() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Absence[DoSomething A, 3]|A.Something is not One\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int count = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")
                        && !getEventAttributeValue(event, "Something").equals("One")) {
                    ++count;
                }
            }

            Assert.assertTrue(count <= 3, "Absence[3] constraint violated. count = " + count);
        }
    }

    @Test
    public void testAbsence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "Absence[DoSomething A]|A.Something is not One\n";

        XLog log = Evaluator.getLog(
                15,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        boolean ok = true;
        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("DoSomething")
                        && !getEventAttributeValue(event, "Something").equals("One")) {
                    ok = false;
                }
            }
        }

        Assert.assertTrue(ok, "Absence[3] constraint violated.");
    }

    @Test
    public void testRespondedExistence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "RespondedExistence[BookTransport A, UseTransport B]|A.TransportType is Plane|different TransportType\n" +
                "Existence[BookTransport A]|A.TransportType is Plane\n";

        XLog log = Evaluator.getLog(
                8,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean a = false;
            boolean b = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    a = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && !getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    b = true;
                }
            }

            Assert.assertTrue(!a || b, "RespondedExistence constraint violated");
        }
    }

    @Test
    public void testNotRespondedExistence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotRespondedExistence[BookTransport A, UseTransport B]|A.TransportType is Plane|same TransportType\n" +
                "Existence[BookTransport A]|A.TransportType is Plane\n";

        XLog log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean a = false;
            boolean b = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    a = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    b = true;
                }
            }

            Assert.assertTrue(!a || !b, "NotRespondedExistence constraint violated");
        }
    }

    @Test
    public void testNotRespondedExistenceWithNumericSame() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "NotRespondedExistence[BookTransport A, UseTransport B]|A.TransportType is Plane|same Price\n" +
                "Existence[BookTransport A]|A.TransportType is Plane\n";

        XLog log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean a = false;
            boolean b = false;
            Set<Float> values = new HashSet<>();
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    a = true;
                    values.add(Float.parseFloat(getEventAttributeValue(event, "Price")));
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && values.contains(Float.parseFloat(getEventAttributeValue(event, "Price")))) {
                    b = true;
                }
            }

            Assert.assertTrue(!a || !b, "NotRespondedExistence constraint violated");
        }
    }

    @Test
    public void testAlternateResponse() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "AlternateResponse[BookTransport A, UseTransport B]|A.TransportType is Plane|B.TransportType is Plane\n" +
                "Existence[BookTransport A, 3]|A.TransportType is Plane\n";

        XLog log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean awaiting = false;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    Assert.assertFalse(awaiting, "AlternateResponse constraint violated: two parallel activation");
                    awaiting = true;
                }
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    awaiting = false;
                }
            }

            Assert.assertFalse(awaiting, "AlternateResponse violated");
        }
    }

    @Test
    public void testAlternatePrecedence() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = baseDeclare + "AlternatePrecedence[UseTransport A, BookTransport B]|A.TransportType is Plane|B.TransportType is Plane\n" +
                "Existence[UseTransport A, 3]|A.TransportType is Plane\n";

        XLog log = Evaluator.getLog(
                20,
                5,
                50,
                2,
                declare,
                "./data/temp.als",
                2, false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            int preceded = 0;
            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                if (getEventAttributeValue(event, "concept:name").equals("UseTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    Assert.assertTrue(preceded > 0, "AlternatePrecedence constraint violated");
                    preceded = 0;
                }
                if (getEventAttributeValue(event, "concept:name").equals("BookTransport")
                        && getEventAttributeValue(event, "TransportType").equals("Plane")) {
                    ++preceded;
                }
            }
        }
    }

    @Test
    public void testSameDifferentForOneEvent() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = "activity A\n" +
                "activity B\n" +
                "C: integer between 0 and 100\n" +
                "bind A: C\n" +
                "bind B: C\n" +
                "Init[A]\n" +
                "Response[A A,B B]||different C \n" +
                "ChainResponse[A A,B B]||same C \n";

        Global.encodeNames = false;
        XLog log = Evaluator.getLog(
                3,
                3,
                50,
                2,
                declare,
                "./data/temp.als",
                2,
                false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        log = Evaluator.getLog(
                3,
                3,
                50,
                2,
                declare,
                "./data/temp.als",
                1,
                false,
                false, LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() == 0, "Solution found, but it shouldn't exist");
    }

    @Test
    public void testNegativeTracesOrJoined() throws IllegalAccessException, Err, IOException, NoSuchFieldException, DeclareParserException, BadSolutionException {
        String declare = "activity A\n" +
                "activity B\n" +
                "activity C\n" +
                "D: val1, val2\n" +
                "bind C: D\n" +
                "Init[A]\n" +
                "Response[A,B]\n" +
                "ChainResponse[C c1,C c2]| c1.D is val1 | c2.D is val2\n" +
                "Existence[C]\n";

        Global.encodeNames = false;
        XLog log = Evaluator.getLog(
                5,
                3,
                250,
                1,
                declare,
                "./data/temp.als",
                1,
                false,
                true,
                LocalDateTime.now(),
                Duration.ofHours(4));

        Assert.assertTrue(log.size() > 0, "No solution found");

        for (int i = 0; i < log.size(); ++i) {
            XTrace trace = log.get(i);
            boolean initViolated = !getEventAttributeValue(trace.get(0), "concept:name").equals("A");
            boolean responseViolated = false;
            boolean chainResponseViolated = false;
            boolean existenceViolated = true;

            for (int j = 0; j < trace.size(); ++j) {
                XEvent event = trace.get(j);
                responseViolated = (responseViolated || getEventAttributeValue(event, "concept:name").equals("A"))
                        && !getEventAttributeValue(event, "concept:name").equals("B");
                chainResponseViolated = chainResponseViolated
                        || getEventAttributeValue(event, "concept:name").equals("C") && getEventAttributeValue(event, "D").equals("val1")
                        && (j == trace.size() - 1 || !(getEventAttributeValue(trace.get(j + 1), "concept:name").equals("C") && getEventAttributeValue(trace.get(j + 1), "D").equals("val1")));
                existenceViolated = existenceViolated && !getEventAttributeValue(event, "concept:name").equals("C");
            }

            Assert.assertTrue(initViolated || responseViolated || chainResponseViolated || existenceViolated,
                    "positive trace found, trace #" + (i + 1) + "\n");
        }
    }
}



