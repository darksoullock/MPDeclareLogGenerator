package parsing;

import core.Exceptions.DeclareParserException;
import core.alloy.codegen.AlloyCodeGenerator;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.DataExpressionParser;
import org.testng.Assert;
import org.testng.annotations.Test;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class ExpressionParserTest {
    DataExpressionParser parser = new DataExpressionParser();

    @Test
    public void testGeneral() throws DeclareParserException {
        DataExpression ex = parser.parse("different TransportType and (B.TransportType is not Car or A.Price<=2) and A.TransportType in (Car, Plane,Train)");
        Assert.assertEquals(ex.toString(), "and(different(TransportType),and(or(is not(B.TransportType,Car),<=(A.Price,2)),in(A.TransportType,(Car, Plane,Train))))");
    }

    @Test
    public void testUnwrap() throws DeclareParserException {
        DataExpression ex = parser.parse("(different TransportType and (B.TransportType is not Car or A.Price<=2) and A.TransportType in (Car, Plane,Train))");
        Assert.assertEquals(ex.toString(), "and(different(TransportType),and(or(is not(B.TransportType,Car),<=(A.Price,2)),in(A.TransportType,(Car, Plane,Train))))");
    }

    @Test
    public void testIsIsNot() throws DeclareParserException {
        DataExpression ex = parser.parse("A is B or C is not B");
        Assert.assertEquals(ex.toString(), "or(is(A,B),is not(C,B))");
    }

    @Test
    public void testInNotIn() throws DeclareParserException {
        DataExpression ex = parser.parse("A in (B,D,E) or C not in (B,D,F)");
        Assert.assertEquals(ex.toString(), "or(in(A,(B,D,E)),not in(C,(B,D,F)))");
    }

    @Test
    public void testOrAnd() throws DeclareParserException {
        DataExpression ex = parser.parse("A or B and C");
        Assert.assertEquals(ex.toString(), "or(A,and(B,C))");
    }

    @Test
    public void testOrAnd2() throws DeclareParserException {
        DataExpression ex = parser.parse("A and B or C");
        Assert.assertEquals(ex.toString(), "or(and(A,B),C)");
    }

    @Test
    public void testOrAndParenthesis() throws DeclareParserException {
        DataExpression ex = parser.parse("A or (B and C)");
        Assert.assertEquals(ex.toString(), "or(A,and(B,C))");
    }

    @Test
    public void testNot() throws DeclareParserException {
        DataExpression ex = parser.parse("not A");
        Assert.assertEquals(ex.toString(), "not(A)");
    }

    @Test
    public void testNotPriority() throws DeclareParserException {
        DataExpression ex = parser.parse("not A or B and C");
        Assert.assertEquals(ex.toString(), "or(not(A),and(B,C))");
    }

    @Test
    public void testSame() throws DeclareParserException {
        DataExpression ex = parser.parse("not same A");
        Assert.assertEquals(ex.toString(), "not(same(A))");
    }

    @Test
    public void testDifferent() throws DeclareParserException {
        DataExpression ex = parser.parse("different A");
        Assert.assertEquals(ex.toString(), "different(A)");
    }

    @Test
    public void testVar() throws DeclareParserException {
        DataExpression ex = parser.parse("A.B is C");
        Assert.assertEquals(ex.toString(), "is(A.B,C)");
    }

    @Test
    public void testComp() throws DeclareParserException {
        DataExpression ex = parser.parse("A>=5 and B<2 or C<=3 and D=4 or not E>1");
        Assert.assertEquals(ex.toString(), "or(and(>=(A,5),<(B,2)),or(and(<=(C,3),=(D,4)),not(>(E,1))))");
    }

    AlloyCodeGenerator gen = new AlloyCodeGenerator(1, 1, 3, 0, 1, true);

    @Test(expectedExceptions = DeclareParserException.class)
    public void testSpellingError() throws DeclareParserException {
        gen.Run("Choiced[A,B]\n", false);
    }

    @Test(expectedExceptions = DeclareParserException.class)
    public void testSpellingErrorWithData() throws DeclareParserException {
        gen.Run("Choise[A,B]||\n", false);
    }
}
