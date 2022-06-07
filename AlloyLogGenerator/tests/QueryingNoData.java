import core.Evaluator;
import core.models.query.QueryEvent;
import core.models.query.QueryState;
import core.models.query.TraceQueryResults;
import org.deckfour.xes.in.XesXmlParser;
import org.deckfour.xes.model.XLog;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.io.ByteArrayInputStream;
import java.nio.file.Files;
import java.nio.file.Paths;
import java.util.List;

public class QueryingNoData {

    @Test
    public void testResponse() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Response[B,?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 2);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertTrue(queryEvent.getActivity().equals("C") || queryEvent.getActivity().equals("END"),
                    queryEvent.toString() + " is invalid");
            Assert.assertTrue(queryEvent.isVacuous());
        }
    }

    @Test
    public void testNonVacuousResponse() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Response[?X, A]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 2);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertTrue(!queryEvent.isVacuous() || queryEvent.getActivity().equals("START"), queryEvent.toString() + " is invalid");
            Assert.assertTrue(queryEvent.isVacuous() || queryEvent.getActivity().equals("D"), queryEvent.toString() + " is invalid");
        }
    }

    @Test
    public void testNotResponse() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "NotResponse[A,?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 3);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertTrue(queryEvent.getActivity().equals("A")
                            || queryEvent.getActivity().equals("D")
                            || queryEvent.getActivity().equals("START"),
                    queryEvent.toString() + " is invalid");
        }
    }

    @Test
    public void testRespondedExistence() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "RespondedExistence[D,?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(1);
        Assert.assertEquals(result.getName(), "Case No. 2");
        Assert.assertEquals(result.getStates().size(), 3);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertTrue(queryEvent.getActivity().equals("START") || queryEvent.getActivity().equals("D")  || queryEvent.getActivity().equals("END"),
                    queryEvent.toString() + " is invalid");
        }
    }

    @Test
    public void testExistence() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Existence[?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(1);
        Assert.assertEquals(result.getName(), "Case No. 2");
        Assert.assertEquals(result.getStates().size(), 3);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertTrue(queryEvent.getActivity().equals("START") || queryEvent.getActivity().equals("END")
                    || queryEvent.getActivity().equals("D"), queryEvent.toString() + " is invalid");
        }
    }

    @Test
    public void testAbsence() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Absence[?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 1);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertEquals(queryEvent.getActivity(), "D");
        }
    }

    @Test
    public void testExclusiveChoice() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "ExclusiveChoice[START, ?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 1);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getData().isEmpty());
            Assert.assertEquals(queryEvent.getActivity(), "D");
        }
    }

    @Test
    public void testChoice() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Choice[START, ?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 6);
    }

    @Test
    public void testChainPrecedence() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "ChainPrecedence[A, ?X]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().iterator().next().getTemplateValuesMap().get("?X").getActivity(), "START");
        Assert.assertEquals(all.get(1).getStates().size(), 6);
    }

    @Test
    public void testTwoQueries() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Precedence[?X, START]\nResponse[?X, END]\nNotChainResponse[?X, B]";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log, 1);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 3);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertTrue(queryEvent.getActivity().equals("B") || queryEvent.getActivity().equals("C")
                    || queryEvent.getActivity().equals("D"));
        }
    }

//    @Test
//    public void testResponse() throws Exception {
//
//        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
//        String declare = "Response[B,?X]";
//
//        LogToModel logToModel = new LogToModel();
//        DeclareModel model = logToModel.parse(log);
//
//        Set<QueryState> traceStates = Evaluator.queryTrace(
//                declare,
//                "./../data/temp.als",
//                false,
//                log.get(0),
//                model,
//                logToModel.getActivityNameToCode());
//
//        Assert.assertNotNull(traceStates);
//
//    }
}
