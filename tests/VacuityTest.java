import core.Exceptions.DeclareParserException;
import core.alloy.codegen.AlloyCodeGenerator;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.io.FileNotFoundException;

/**
 * Created by Vasiliy on 2017-11-24.
 */
public class VacuityTest {
    AlloyCodeGenerator gen = new AlloyCodeGenerator(1, 1, 3, 0, 1, true);

    @Test
    public void testChoice() throws FileNotFoundException, DeclareParserException {
        gen.Run("Choice[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testExclusiveChoise() throws FileNotFoundException, DeclareParserException {
        gen.Run("ExclusiveChoise[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testAbsenceN() throws FileNotFoundException, DeclareParserException {
        gen.Run("Absence[A,3]\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testExistenceN() throws FileNotFoundException, DeclareParserException {
        gen.Run("Existence[A,3]\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testExactlyN() throws FileNotFoundException, DeclareParserException {
        gen.Run("Exactly[A,3]\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testRespondedExistence() throws FileNotFoundException, DeclareParserException {
        gen.Run("RespondedExistence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testResponse() throws FileNotFoundException, DeclareParserException {
        gen.Run("Response[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testAlternateResponse() throws FileNotFoundException, DeclareParserException {
        gen.Run("AlternateResponse[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testChainResponse() throws FileNotFoundException, DeclareParserException {
        gen.Run("ChainResponse[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testPrecedence() throws FileNotFoundException, DeclareParserException {
        gen.Run("Precedence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testAlternatePrecedence() throws FileNotFoundException, DeclareParserException {
        gen.Run("AlternatePrecedence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testChainPrecedence() throws FileNotFoundException, DeclareParserException {
        gen.Run("ChainPrecedence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotRespondedExistence() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotRespondedExistence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotResponse() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotResponse[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotPrecedence() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotPrecedence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotChainResponse() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotChainResponse[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotChainPrecedence() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotChainPrecedence[A,B]\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testChoiceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("Choice[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("//vc"));
    }

    @Test
    public void testExclusiveChoiseWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("ExclusiveChoise[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testAbsenceNWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("Absence[A,3]|\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testExistenceNWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("Existence[A,3]|\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testExactlyNWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("Exactly[A,3]|\n");
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testRespondedExistenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("RespondedExistence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testResponseWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("Response[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testAlternateResponseWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("AlternateResponse[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testChainResponseWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("ChainResponse[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testPrecedenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("Precedence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testAlternatePrecedenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("AlternatePrecedence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testChainPrecedenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("ChainPrecedence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testNotRespondedExistenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotRespondedExistence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testNotResponseWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotResponse[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testNotPrecedenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotPrecedence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testNotChainResponseWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotChainResponse[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }

    @Test
    public void testNotChainPrecedenceWithData() throws FileNotFoundException, DeclareParserException {
        gen.Run("NotChainPrecedence[A,B]||\n");
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: TaskEvent | te.task = A and "));
    }
}
