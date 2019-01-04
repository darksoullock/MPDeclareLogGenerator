import core.Evaluator;
import org.deckfour.xes.in.XesXmlParser;
import org.deckfour.xes.model.XLog;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.io.ByteArrayInputStream;
import java.time.Duration;
import java.time.LocalDateTime;

/**
 * Created by Vasiliy on 2017-11-20.
 */
public class ComplianceChecker {
    private String baseDeclare = "/task definition\n" +
            "activity START\n" +
            "activity A\n" +
            "activity B\n" +
            "activity C\n" +
            "activity END\n" +
            "\n" +
            "/constraints\n" +
            "Init[START]\n" +
            "Response[START, B]\n" +
            "Precedence[END, A]\n" +
            "Precedence[END, B]\n" +
            "Precedence[END, C]\n" +
            "Absence[END, 1]\n" +
            "Absence[B, 3]\n" +
            "ChainResponse[A, B]\n" +
            "Existence[C]\n" +
            "\n" +
            "/data definition\n" +
            "ENUM: X, Y, Z\n" +
            "INT: integer between 0 and 100\n" +
            "FLOAT: float between 0 and 100\n" +
            "\n" +
            "/data binding\n" +
            "bind A: ENUM\n" +
            "bind B: INT\n" +
            "bind C: FLOAT\n";

    @Test
    public void testCompliant() throws Exception {
        String declare = baseDeclare +
                "Existence[A]|A.ENUM is X\n" +
                "Existence[B]|A.INT > 50\n" +
                "Existence[C]|A.FLOAT < 50\n" +
                "Absence[A]|A.ENUM is Y\n";

        ByteArrayInputStream is = new ByteArrayInputStream(("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n" +
                "<log xes.version=\"1.0\" xes.features=\"nested-attributes\" openxes.version=\"1.0RC7\" xmlns=\"http://www.xes-standard.org/\">\n" +
                "\t<string key=\"concept:name\" value=\"Artificial Log\"/>\n" +
                "\t<string key=\"lifecycle:model\" value=\"standard\"/>\n" +
                "\t<string key=\"source\" value=\"DAlloy\"/>\n" +
                "\t<trace>\n" +
                "\t\t<string key=\"concept:name\" value=\"Case No. 1\"/>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"START\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T21:27:25.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"A\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:33:05.405+02:00\"/>\n" +
                "\t\t\t<string key=\"ENUM\" value=\"X\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"B\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<int key=\"INT\" value=\"54\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:54:45.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"C\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:22:16.405+02:00\"/>\n" +
                "\t\t\t<float key=\"FLOAT\" value=\"45.2\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"END\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:58:30.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t</trace>\n" +
                "</log>\n").getBytes());

        boolean compliant = Evaluator.checkCompliace(
                0,
                declare,
                "./../data/temp.als",
                false,
                new XesXmlParser().parse(is).get(0).get(0)).isEmpty();

        Assert.assertTrue(compliant, "Given trace expected to be compliant");
    }

    @Test
    public void testViolatedFlow() throws Exception {
        String declare = baseDeclare;

        ByteArrayInputStream is = new ByteArrayInputStream(("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n" +
                "<log xes.version=\"1.0\" xes.features=\"nested-attributes\" openxes.version=\"1.0RC7\" xmlns=\"http://www.xes-standard.org/\">\n" +
                "\t<string key=\"concept:name\" value=\"Artificial Log\"/>\n" +
                "\t<string key=\"lifecycle:model\" value=\"standard\"/>\n" +
                "\t<string key=\"source\" value=\"DAlloy\"/>\n" +
                "\t<trace>\n" +
                "\t\t<string key=\"concept:name\" value=\"Case No. 1\"/>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"END\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:58:30.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"START\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T21:27:25.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t</trace>\n" +
                "</log>\n").getBytes());

        boolean compliant = Evaluator.checkCompliace(
                0,
                declare,
                "./../data/temp.als",
                false,
                new XesXmlParser().parse(is).get(0).get(0)).isEmpty();

        Assert.assertFalse(compliant, "Given trace expected to be non-compliant");
    }

    @Test
    public void testEnumDataViolation() throws Exception {
        String declare = baseDeclare +
                "Existence[A]|A.ENUM is Y\n";

        ByteArrayInputStream is = new ByteArrayInputStream(("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n" +
                "<log xes.version=\"1.0\" xes.features=\"nested-attributes\" openxes.version=\"1.0RC7\" xmlns=\"http://www.xes-standard.org/\">\n" +
                "\t<string key=\"concept:name\" value=\"Artificial Log\"/>\n" +
                "\t<string key=\"lifecycle:model\" value=\"standard\"/>\n" +
                "\t<string key=\"source\" value=\"DAlloy\"/>\n" +
                "\t<trace>\n" +
                "\t\t<string key=\"concept:name\" value=\"Case No. 1\"/>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"START\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T21:27:25.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"A\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:33:05.405+02:00\"/>\n" +
                "\t\t\t<string key=\"ENUM\" value=\"X\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"B\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<int key=\"INT\" value=\"54\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:54:45.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"C\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:22:16.405+02:00\"/>\n" +
                "\t\t\t<float key=\"FLOAT\" value=\"45.2\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"END\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:58:30.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t</trace>\n" +
                "</log>\n").getBytes());

        boolean compliant = Evaluator.checkCompliace(
                0,
                declare,
                "./../data/temp.als",
                false,
                new XesXmlParser().parse(is).get(0).get(0)).isEmpty();

        Assert.assertFalse(compliant, "Given trace expected to be non-compliant");
    }

    @Test
    public void testIntDataViolation() throws Exception {
        String declare = baseDeclare +
                "Existence[B]|A.INT < 50\n";

        ByteArrayInputStream is = new ByteArrayInputStream(("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n" +
                "<log xes.version=\"1.0\" xes.features=\"nested-attributes\" openxes.version=\"1.0RC7\" xmlns=\"http://www.xes-standard.org/\">\n" +
                "\t<string key=\"concept:name\" value=\"Artificial Log\"/>\n" +
                "\t<string key=\"lifecycle:model\" value=\"standard\"/>\n" +
                "\t<string key=\"source\" value=\"DAlloy\"/>\n" +
                "\t<trace>\n" +
                "\t\t<string key=\"concept:name\" value=\"Case No. 1\"/>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"START\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T21:27:25.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"A\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:33:05.405+02:00\"/>\n" +
                "\t\t\t<string key=\"ENUM\" value=\"X\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"B\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<int key=\"INT\" value=\"54\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:54:45.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"C\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:22:16.405+02:00\"/>\n" +
                "\t\t\t<float key=\"FLOAT\" value=\"45.2\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"END\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:58:30.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t</trace>\n" +
                "</log>\n").getBytes());

        boolean compliant = Evaluator.checkCompliace(
                0,
                declare,
                "./../data/temp.als",
                false,
                new XesXmlParser().parse(is).get(0).get(0)).isEmpty();

        Assert.assertFalse(compliant, "Given trace expected to be non-compliant");
    }

    @Test
    public void testFloatDataViolation() throws Exception {
        String declare = baseDeclare +
                "Existence[C]|A.FLOAT > 50\n";

        ByteArrayInputStream is = new ByteArrayInputStream(("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n" +
                "<log xes.version=\"1.0\" xes.features=\"nested-attributes\" openxes.version=\"1.0RC7\" xmlns=\"http://www.xes-standard.org/\">\n" +
                "\t<string key=\"concept:name\" value=\"Artificial Log\"/>\n" +
                "\t<string key=\"lifecycle:model\" value=\"standard\"/>\n" +
                "\t<string key=\"source\" value=\"DAlloy\"/>\n" +
                "\t<trace>\n" +
                "\t\t<string key=\"concept:name\" value=\"Case No. 1\"/>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"START\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T21:27:25.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"A\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:33:05.405+02:00\"/>\n" +
                "\t\t\t<string key=\"ENUM\" value=\"X\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"B\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<int key=\"INT\" value=\"54\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:54:45.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"C\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:22:16.405+02:00\"/>\n" +
                "\t\t\t<float key=\"FLOAT\" value=\"45.2\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"END\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:58:30.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t</trace>\n" +
                "</log>\n").getBytes());

        boolean compliant = Evaluator.checkCompliace(
                0,
                declare,
                "./../data/temp.als",
                false,
                new XesXmlParser().parse(is).get(0).get(0)).isEmpty();

        Assert.assertFalse(compliant, "Given trace expected to be non-compliant");
    }

    @Test
    public void testExactFloatData() throws Exception {
        String declare = baseDeclare +
                "Existence[C]|A.FLOAT >= 50\n";

        ByteArrayInputStream is = new ByteArrayInputStream(("<?xml version=\"1.0\" encoding=\"UTF-8\" ?>\n" +
                "<log xes.version=\"1.0\" xes.features=\"nested-attributes\" openxes.version=\"1.0RC7\" xmlns=\"http://www.xes-standard.org/\">\n" +
                "\t<string key=\"concept:name\" value=\"Artificial Log\"/>\n" +
                "\t<string key=\"lifecycle:model\" value=\"standard\"/>\n" +
                "\t<string key=\"source\" value=\"DAlloy\"/>\n" +
                "\t<trace>\n" +
                "\t\t<string key=\"concept:name\" value=\"Case No. 1\"/>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"START\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T21:27:25.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"A\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:33:05.405+02:00\"/>\n" +
                "\t\t\t<string key=\"ENUM\" value=\"X\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"B\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<int key=\"INT\" value=\"54\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-27T23:54:45.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"C\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:22:16.405+02:00\"/>\n" +
                "\t\t\t<float key=\"FLOAT\" value=\"50\"/>\n" +
                "\t\t</event>\n" +
                "\t\t<event>\n" +
                "\t\t\t<string key=\"concept:name\" value=\"END\"/>\n" +
                "\t\t\t<string key=\"lifecycle:transition\" value=\"complete\"/>\n" +
                "\t\t\t<date key=\"time:timestamp\" value=\"2018-12-28T00:58:30.405+02:00\"/>\n" +
                "\t\t</event>\n" +
                "\t</trace>\n" +
                "</log>\n").getBytes());

        boolean compliant = Evaluator.checkCompliace(
                0,
                declare,
                "./../data/temp.als",
                false,
                new XesXmlParser().parse(is).get(0).get(0)).isEmpty();

        Assert.assertTrue(compliant, "Given trace expected to be compliant");
    }
}



