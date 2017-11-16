import core.Global;
import core.alloy.codegen.FunctionGenerator;
import core.alloy.codegen.fnparser.*;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-26.
 */
public class FunctionGeneratorTest {
    FunctionGenerator gen = new FunctionGenerator(2, 4);

    @Test
    public void testTask() {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set TaskEvent) { { Task } }\n");
    }

    @Test
    public void testArgs() {
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A, B: set TaskEvent) { { Task } }\n");
    }

    @Test
    public void testVariable() {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set TaskEvent) { { A.data&Value } }\n");
    }

    @Test
    public void testAnd() {
        DataFunction fn = new DataFunction(Arrays.asList("A"),
                new BinaryExpression(
                        new Token(0, Token.Type.Operator, "and"),
                        new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")),
                        new ValueExpression(new Token(0, Token.Type.Variable, "B.Value"))));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set TaskEvent) { { (A.data&Value and B.data&Value) } }\n");
    }

    @Test
    public void testNor() {
        DataFunction fn = new DataFunction(Arrays.asList("A"),
                new UnaryExpression(
                        new Token(0, Token.Type.Operator, "not"),
                        new BinaryExpression(
                                new Token(0, Token.Type.Operator, "or"),
                                new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")),
                                new ValueExpression(new Token(0, Token.Type.Variable, "B.Value")))));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set TaskEvent) { { (not (A.data&Value) and not (B.data&Value)) } }\n");
    }

    @Test
    public void testNumber() {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Variable, "20")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set TaskEvent) { { 20 } }\n");
    }

    @Test
    public void testSame() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "same"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        String afn = gen.generateFunction("fn", fn, new HashMap<>(), null);
        Assert.assertEquals(afn, "pred fn(A, B: set TaskEvent) { { (A.data&Task=B.data&Task) } }\n");
    }

    @Test
    public void testDifferent() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "different"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        String afn = gen.generateFunction("fn", fn, new HashMap<>(), null);
        Assert.assertEquals(afn, "pred fn(A, B: set TaskEvent) { { not (A.data&Task=B.data&Task) } }\n");
    }

    @Test
    public void testNot() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "not"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A"), expr);
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set TaskEvent) { { not (Task) } }\n");
    }

    @Test
    public void testNumericSame() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "same"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Task", new IntegerData("Task", 0, 5, 1));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("A.data&Task=B.data&Task"));
    }

    @Test
    public void testNumericDifferent() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "different"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Task", new IntegerData("Task", 0, 5, 1));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.differentPrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.differentPrefix + "Task"));
        Assert.assertTrue(afn.contains("not A.data&Task=B.data&Task"));
    }

    @Test
    public void testNumericNotSame() {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "not"),
                        new UnaryExpression(new Token(0, Token.Type.Operator, "same"),
                                new ValueExpression(new Token(0, Token.Type.Task, "Task"))));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Task", new IntegerData("Task", 0, 5, 1));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));

        Assert.assertTrue(afn.contains("one sig " + Global.differentPrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.differentPrefix + "Task"));
        Assert.assertTrue(afn.contains("not A.data&Task=B.data&Task"));
    }

    @Test
    public void testNumericNotDifferent() {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "not"),
                        new UnaryExpression(new Token(0, Token.Type.Operator, "different"),
                                new ValueExpression(new Token(0, Token.Type.Task, "Task"))));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Task", new IntegerData("Task", 0, 5, 1));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("A.data&Task=B.data&Task"));
    }

    @Test
    public void testNotConstraintNumericSame() {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "same"),
                        new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Task", new IntegerData("Task", 0, 5, 1));
        String afn = gen.generateNotFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.differentPrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.differentPrefix + "Task"));
        Assert.assertTrue(afn.contains("A.data&Task=B.data&Task"));
    }

    @Test
    public void testNotConstraintNumericDifferent() {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "different"),
                        new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Task", new IntegerData("Task", 0, 5, 1));
        String afn = gen.generateNotFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Task"));
        Assert.assertTrue(afn.contains("not A.data&Task=B.data&Task"));
    }
}
