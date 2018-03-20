import core.Exceptions.DeclareParserException;
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
    public void testActivity() throws DeclareParserException {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: Event) { { Activity } }\n");
    }

    @Test
    public void testArgs() throws DeclareParserException {
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A, B: Event) { { Activity } }\n");
    }

    @Test
    public void testVariable() throws DeclareParserException {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: Event) { { A.data&Value } }\n");
    }

    @Test
    public void testAnd() throws DeclareParserException {
        DataFunction fn = new DataFunction(Arrays.asList("A"),
                new BinaryExpression(
                        new Token(0, Token.Type.Operator, "and"),
                        new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")),
                        new ValueExpression(new Token(0, Token.Type.Variable, "B.Value"))));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: Event) { { (A.data&Value and B.data&Value) } }\n");
    }

    @Test
    public void testNor() throws DeclareParserException {
        DataFunction fn = new DataFunction(Arrays.asList("A"),
                new UnaryExpression(
                        new Token(0, Token.Type.Operator, "not"),
                        new BinaryExpression(
                                new Token(0, Token.Type.Operator, "or"),
                                new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")),
                                new ValueExpression(new Token(0, Token.Type.Variable, "B.Value")))));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: Event) { { (not (A.data&Value) and not (B.data&Value)) } }\n");
    }

    @Test
    public void testNumber() throws DeclareParserException {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Variable, "20")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: Event) { { 20 } }\n");
    }

    @Test
    public void testSame() throws DeclareParserException {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "same"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        String afn = gen.generateFunction("fn", fn, new HashMap<>(), null);
        Assert.assertEquals(afn, "pred fn(A, B: Event) { { (A.data&Activity=B.data&Activity) } }\n");
    }

    @Test
    public void testDifferent() throws DeclareParserException {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "different"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        String afn = gen.generateFunction("fn", fn, new HashMap<>(), null);
        Assert.assertEquals(afn, "pred fn(A, B: Event) { { not (A.data&Activity=B.data&Activity) } }\n");
    }

    @Test
    public void testNot() throws DeclareParserException {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "not"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A"), expr);
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: Event) { { not (Activity) } }\n");
    }

    @Test
    public void testNumericSame() throws DeclareParserException {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "same"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Activity", new IntegerData("Activity", 0, 5, 1, null));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("A.data&Activity=B.data&Activity"));
    }

    @Test
    public void testNumericDifferent() throws DeclareParserException {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "different"), new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Activity", new IntegerData("Activity", 0, 5, 1, null));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.differentPrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.differentPrefix + "Activity"));
        Assert.assertTrue(afn.contains("not A.data&Activity=B.data&Activity"));
    }

    @Test
    public void testNumericNotSame() throws DeclareParserException {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "not"),
                        new UnaryExpression(new Token(0, Token.Type.Operator, "same"),
                                new ValueExpression(new Token(0, Token.Type.Activity, "Activity"))));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Activity", new IntegerData("Activity", 0, 5, 1, null));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));

        Assert.assertTrue(afn.contains("one sig " + Global.differentPrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.differentPrefix + "Activity"));
        Assert.assertTrue(afn.contains("not A.data&Activity=B.data&Activity"));
    }

    @Test
    public void testNumericNotDifferent() throws DeclareParserException {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "not"),
                        new UnaryExpression(new Token(0, Token.Type.Operator, "different"),
                                new ValueExpression(new Token(0, Token.Type.Activity, "Activity"))));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Activity", new IntegerData("Activity", 0, 5, 1, null));
        String afn = gen.generateFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("A.data&Activity=B.data&Activity"));
    }

    @Test
    public void testNotConstraintNumericSame() throws DeclareParserException {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "same"),
                        new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Activity", new IntegerData("Activity", 0, 5, 1, null));
        String afn = gen.generateNotFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.differentPrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.differentPrefix + "Activity"));
        Assert.assertTrue(afn.contains("A.data&Activity=B.data&Activity"));
    }

    @Test
    public void testNotConstraintNumericDifferent() throws DeclareParserException {
        UnaryExpression expr =
                new UnaryExpression(new Token(0, Token.Type.Operator, "different"),
                        new ValueExpression(new Token(0, Token.Type.Activity, "Activity")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        Map<String, NumericData> map = new HashMap<>();
        map.put("Activity", new IntegerData("Activity", 0, 5, 1, null));
        String afn = gen.generateNotFunction("fn", fn, map, Arrays.asList("T1", "T2"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("one sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("abstract sig " + Global.samePrefix + "Activity"));
        Assert.assertTrue(afn.contains("not A.data&Activity=B.data&Activity"));
    }
}
