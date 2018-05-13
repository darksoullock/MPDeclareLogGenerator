import core.Evaluator;
import core.alloy.serialization.AlloyLogExtractor;
import core.helpers.XesHelper;
import core.models.declare.data.NumericToken;
import core.models.intervals.Interval;
import core.models.serialization.EventAdapter;
import core.models.serialization.Payload;
import edu.mit.csail.sdg.alloy4.*;
import edu.mit.csail.sdg.alloy4compiler.ast.*;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;
import org.deckfour.xes.model.impl.XAttributeMapImpl;
import org.deckfour.xes.model.impl.XLogImpl;
import org.deckfour.xes.model.impl.XTraceImpl;
import org.testng.Assert;
import org.testng.annotations.Test;

import javax.swing.*;
import java.io.IOException;
import java.time.Duration;
import java.time.LocalDateTime;
import java.util.*;

/**
 * Created by Vasiliy on 2017-11-09.
 */
public class Serializer {
    class ModuleStub implements Module {

        @Override
        public String getModelName() {
            return null;
        }

        @Override
        public String path() {
            return null;
        }

        @Override
        public SafeList<? extends Module> getAllReachableModules() {
            return null;
        }

        @Override
        public List<String> getAllReachableModulesFilenames() {
            return new ArrayList<>();
        }

        @Override
        public ConstList<Sig> getAllReachableSigs() {
            return null;
        }

        @Override
        public ConstList<Sig> getAllReachableUserDefinedSigs() {
            return null;
        }

        @Override
        public SafeList<Sig> getAllSigs() {
            return null;
        }

        @Override
        public SafeList<Func> getAllFunc() {
            return null;
        }

        @Override
        public ConstList<Pair<String, Expr>> getAllAssertions() {
            return null;
        }

        @Override
        public SafeList<Pair<String, Expr>> getAllFacts() {
            return null;
        }

        @Override
        public Expr getAllReachableFacts() {
            return null;
        }

        @Override
        public ConstList<Command> getAllCommands() {
            return null;
        }

        @Override
        public void addGlobal(String name, Expr value) {

        }

        @Override
        public JFrame showAsTree(Listener listener) {
            return null;
        }

        @Override
        public Expr parseOneExpressionFromString(String input) throws Err, IOException {
            return null;
        }
    }

    @Test
    public void equilizeTest() {
        List<EventAdapter> orderedStateEvents = new ArrayList<>();
        NumericToken ta = new NumericToken(NumericToken.Type.Same, "aaa");
        NumericToken tb = new NumericToken(NumericToken.Type.Same, "bbb");
        NumericToken tc = new NumericToken(NumericToken.Type.Same, "ccc");
        Set<NumericToken> abs = new HashSet<>();
        abs.add(ta);
        abs.add(tb);
        Set<NumericToken> as = new HashSet<>();
        as.add(ta);
        Set<NumericToken> bs = new HashSet<>();
        bs.add(tb);
        Set<NumericToken> cs = new HashSet<>();
        cs.add(tc);
        Payload pa = new Payload("a", "b", abs);
        EventAdapter a = new EventAdapter(0, "", Arrays.asList(pa));
        Payload pb = new Payload("a", "b", as);
        EventAdapter b = new EventAdapter(0, "", Arrays.asList(pb));
        Payload pc = new Payload("a", "b", bs);
        EventAdapter c = new EventAdapter(0, "", Arrays.asList(pc));
        Payload pd = new Payload("a", "b", cs);
        EventAdapter d = new EventAdapter(0, "", Arrays.asList(pd));
        Map<String, Interval> map = new HashMap<>();
        map.put("b", null);
        AlloyLogExtractor ser = new AlloyLogExtractor(new ModuleStub(), map, new ArrayList<>(), new HashMap<>(), LocalDateTime.now(), Duration.ofHours(5));
        orderedStateEvents.add(a);
        orderedStateEvents.add(b);
        orderedStateEvents.add(c);
        orderedStateEvents.add(d);
        ser.equalizeSameTokens(orderedStateEvents);
        Assert.assertEquals(abs.size(), 2);
        Assert.assertEquals(as.size(), 2);
        Assert.assertEquals(bs.size(), 2);
        Assert.assertEquals(cs.size(), 1);
        Assert.assertTrue(abs.contains(ta));
        Assert.assertTrue(abs.contains(tb));
        Assert.assertTrue(as.contains(ta));
        Assert.assertTrue(as.contains(tb));
        Assert.assertTrue(bs.contains(ta));
        Assert.assertTrue(bs.contains(tb));
        Assert.assertTrue(cs.contains(tc));
    }

    private void addTraceDummy(XLog log1, int i) {
        XTraceImpl trace = new XTraceImpl(new XAttributeMapImpl());
        trace.getAttributes().put("n", new XAttributeLiteralImpl("n", String.valueOf(i)));
        log1.add(trace);
    }
}
