package intervals;

import core.Exceptions.BadSolutionException;
import core.Exceptions.DeclareParserException;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.Token;
import core.alloy.codegen.fnparser.ValueExpression;
import core.models.intervals.*;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.util.Arrays;

/**
 * Created by Vasiliy on 2017-11-08.
 */
public class IntervalTest {
    @Test
    public void IntegerValueTest() {
        Interval iv = new IntegerValue(11);
        Assert.assertEquals(iv.get(), "11");
        Assert.assertEquals(iv.getSame(Arrays.asList("1")), "11");
        Assert.assertEquals(iv.getValueCount(10), 1);
    }

    @Test
    public void NegativeIntegerTest() {
        Interval iv = new IntegerInterval(-11, -1, null);
        Assert.assertEquals(iv.get().charAt(0), '-');
        Assert.assertEquals(iv.getValueCount(10), 9);
    }

    @Test(expectedExceptions = BadSolutionException.class)
    public void IntegerValueDifferentTest() throws BadSolutionException {
        Interval iv = new IntegerValue(11);
        iv.getDifferent(Arrays.asList("1"));
    }

    @Test
    public void IntegerIntervalTest() throws BadSolutionException {
        Interval iv = new IntegerInterval(0, 10, null);
        for (int i = 0; i < 100; ++i) {
            int n = Integer.parseInt(iv.get());
            Assert.assertTrue(n < 10 && n > 0);
        }

        Assert.assertEquals(iv.getValueCount(10), 9);
        Assert.assertEquals(iv.getValueCount(5), -1);

        for (int i = 0; i < 100; ++i) {
            iv.resetCaches();
            int n = Integer.parseInt(iv.getDifferent(Arrays.asList("1", "2")));
            int n1 = Integer.parseInt(iv.getDifferent(Arrays.asList("1")));
            int n2 = Integer.parseInt(iv.getDifferent(Arrays.asList("2")));
            Assert.assertNotEquals(n, n1);
            Assert.assertNotEquals(n, n2);
            n = Integer.parseInt(iv.getSame(Arrays.asList("1", "2")));
            n1 = Integer.parseInt(iv.getSame(Arrays.asList("1")));
            n2 = Integer.parseInt(iv.getSame(Arrays.asList("2")));
            Assert.assertEquals(n, n1);
            Assert.assertEquals(n, n1);
            Assert.assertEquals(n, n2);
        }
    }

    @Test
    public void IntegerIsCompliantTest() throws DeclareParserException {
        Interval iv = new IntegerInterval(40, 60, null);
        Token moreToken = new Token(0, Token.Type.Comparator, ">");
        Token lessToken = new Token(0, Token.Type.Comparator, "<");
        Token moreEqualsToken = new Token(0, Token.Type.Comparator, ">=");
        Token lessEqualsToken = new Token(0, Token.Type.Comparator, "<=");
        ValueExpression var = new ValueExpression(new Token(0, Token.Type.Variable, "v"));

        Assert.assertTrue(iv.isCompliant(new BinaryExpression(moreToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(10))))));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(moreToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(41))))));

        Assert.assertTrue(iv.isCompliant(new BinaryExpression(moreEqualsToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(41))))));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(moreEqualsToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(42))))));

        Assert.assertTrue(iv.isCompliant(new BinaryExpression(lessToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(60))))));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(lessToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(59))))));

        Assert.assertTrue(iv.isCompliant(new BinaryExpression(lessEqualsToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(59))))));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(lessEqualsToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(58))))));

        Assert.assertTrue(iv.isCompliant(new BinaryExpression(moreEqualsToken, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(59))), var)));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(moreEqualsToken, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(58))), var)));
    }

    @Test
    public void IntegerValueIsCompliantTest() throws DeclareParserException {
        Interval iv = new IntegerValue(40);
        Token eqToken = new Token(0, Token.Type.Comparator, "=");
        ValueExpression var = new ValueExpression(new Token(0, Token.Type.Variable, "v"));

        Assert.assertTrue(iv.isCompliant(new BinaryExpression(eqToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(40))))));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(eqToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(41))))));
        Assert.assertFalse(iv.isCompliant(new BinaryExpression(eqToken, var, new ValueExpression(new Token(0, Token.Type.Number, String.valueOf(39))))));
    }

    @Test
    public void FloatValueTest() {
        Interval iv = new FloatValue(11.11f);
        Assert.assertEquals(iv.get(), "11.11");
        Assert.assertEquals(iv.getValueCount(10), 1);
    }

    @Test
    public void NegativeFloatTest() {
        Interval iv = new FloatInterval(-11, -1, null);
        Assert.assertEquals(iv.get().charAt(0), '-');
        Assert.assertEquals(iv.getValueCount(10), -1);
    }

    @Test(expectedExceptions = BadSolutionException.class)
    public void FloatValueDifferentTest() throws BadSolutionException {
        Interval iv = new FloatValue(11.11f);
        iv.getDifferent(Arrays.asList("1"));
    }

    @Test
    public void FloatIntervalTest() throws BadSolutionException {
        Interval iv = new FloatInterval(0, 10, null);
        for (int i = 0; i < 100; ++i) {
            float n = Float.parseFloat(iv.get());
            Assert.assertTrue(n < 10 && n > 0);
        }

        Assert.assertEquals(iv.getValueCount(100), -1);

        for (int i = 0; i < 100; ++i) {
            iv.resetCaches();
            float n = Float.parseFloat(iv.getDifferent(Arrays.asList("1", "2")));
            float n1 = Float.parseFloat(iv.getDifferent(Arrays.asList("1")));
            float n2 = Float.parseFloat(iv.getDifferent(Arrays.asList("2")));
            Assert.assertNotEquals(n, n1);
            Assert.assertNotEquals(n, n2);
            n = Float.parseFloat(iv.getSame(Arrays.asList("1", "2")));
            n1 = Float.parseFloat(iv.getSame(Arrays.asList("1")));
            n2 = Float.parseFloat(iv.getSame(Arrays.asList("2")));
            Assert.assertEquals(n, n1);
            Assert.assertEquals(n, n1);
            Assert.assertEquals(n, n2);
        }
    }
}
