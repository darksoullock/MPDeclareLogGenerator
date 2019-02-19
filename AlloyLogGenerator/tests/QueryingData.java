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
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.stream.Collectors;

public class QueryingData {

    @Test
    public void testResponse() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog1.xml")))).get(0);
        String declare = "Response[B,?X]||?";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 2);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 2);
        for (QueryState i : result.getStates()) {
            Assert.assertTrue(i.getTemplateValuesMap().containsKey("?X"));
            QueryEvent queryEvent = i.getTemplateValuesMap().get("?X");
            Assert.assertEquals(!queryEvent.getData().isEmpty(), queryEvent.getActivity().equals("C"), queryEvent.toString());
            Assert.assertTrue(queryEvent.getActivity().equals("C") || queryEvent.getActivity().equals("END"),
                    queryEvent.toString() + " is invalid");
            Assert.assertTrue(queryEvent.isVacuous());
        }
    }

    @Test
    public void testNonVacuousResponse() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog2.xml")))).get(0);
        String declare = "Response[?X, B]|?|";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 3);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 4);
        List<QueryEvent> a = getByActivity(result, "?X", "A");
        Assert.assertEquals(a.size(), 2);
        Assert.assertEquals(a.stream().flatMap(i -> i.getData().values().stream()).collect(Collectors.toSet()), new HashSet<>(Arrays.asList("X", "Y")));
    }

    private List<QueryEvent> getByActivity(TraceQueryResults result, String template, String activity) {
        return result.getStates().stream()
                .filter(i -> i.getTemplateValuesMap().get(template).getActivity().equals(activity))
                .map(i -> i.getTemplateValuesMap().get(template))
                .collect(Collectors.toList());
    }

    @Test
    public void testNotResponse() throws Exception {
        XLog log = new XesXmlParser().parse(new ByteArrayInputStream(Files.readAllBytes(Paths.get("tests/testdata/testlog2.xml")))).get(0);
        String declare = "NotResponse[START,?Y]||?";

        List<TraceQueryResults> all = Evaluator.queryLog(
                declare,
                "./../data/temp.als",
                false,
                log);

        Assert.assertNotNull(all);
        Assert.assertEquals(all.size(), 3);
        TraceQueryResults result = all.get(0);
        Assert.assertEquals(result.getName(), "Case No. 1");
        Assert.assertEquals(result.getStates().size(), 3);
        Assert.assertEquals(result.getStates().stream().flatMap(i -> i.getTemplateValuesMap().values().stream()).map(QueryEvent::getActivity).collect(Collectors.toSet()), new HashSet<>(Arrays.asList("A", "D", "START")));
        Assert.assertEquals(getByActivity(result, "?Y", "A").get(0).getData().values().iterator().next(), "Y", "Activity 'A' expected with ENUM = Y");
    }
}
