package parsing;

import core.alloy.codegen.FunctionGenerator;
import core.alloy.codegen.fnparser.DataFunction;
import core.alloy.codegen.fnparser.Token;
import core.alloy.codegen.fnparser.UnaryExpression;
import core.alloy.codegen.fnparser.ValueExpression;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;

/**
 * Created by Vasiliy on 2017-10-26.
 */
public class FunctionGeneratorTest {
    FunctionGenerator gen = new FunctionGenerator(2, 4);

    @Test
    public void testTask() {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set Payload) { { Task } }\n");
    }

    @Test
    public void testArgs() {
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A, B: set Payload) { { Task } }\n");
    }

    @Test
    public void testVariable() {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Variable, "A.Value")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set Payload) { { A&Value } }\n");
    }

    @Test
    public void testNumber() {
        DataFunction fn = new DataFunction(Arrays.asList("A"), new ValueExpression(new Token(0, Token.Type.Variable, "20")));
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set Payload) { { 20 } }\n");
    }

    @Test
    public void testSame() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "same"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A, B: set Payload) { { (A&Task=B&Task) } }\n");
    }

    @Test
    public void testDifferent() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "different"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A", "B"), expr);
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A, B: set Payload) { { not (A&Task=B&Task) } }\n");
    }

    @Test
    public void testNot() {
        UnaryExpression expr = new UnaryExpression(new Token(0, Token.Type.Operator, "not"), new ValueExpression(new Token(0, Token.Type.Task, "Task")));
        DataFunction fn = new DataFunction(Arrays.asList("A"), expr);
        String afn = gen.generateFunction("fn", fn, null, null);
        Assert.assertEquals(afn, "pred fn(A: set Payload) { { not (Task) } }\n");
    }


}
