import core.Exceptions.GenerationException;
import core.alloy.codegen.AlloyCodeGenerator;
import declare.DeclareModel;
import declare.DeclareParser;
import declare.DeclareParserException;
import org.testng.Assert;
import org.testng.annotations.Test;

import java.io.FileNotFoundException;

/**
 * Created by Vasiliy on 2017-11-24.
 */
public class VacuityTest {
    AlloyCodeGenerator gen = new AlloyCodeGenerator(1, 1, 3, 0, true, false);
    DeclareParser parser = new DeclareParser();

    @Test
    public void testChoice() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Choice[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testExclusiveChoise() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("ExclusiveChoice[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testAbsenceN() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Absence[A,3]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testExistenceN() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Existence[A,3]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testExactlyN() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Exactly[A,3]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("Existence[A]"));
    }

    @Test
    public void testRespondedExistence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("RespondedExistence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testResponse() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Response[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testAlternateResponse() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("AlternateResponse[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testChainResponse() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("ChainResponse[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testPrecedence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Precedence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testAlternatePrecedence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("AlternatePrecedence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testChainPrecedence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("ChainPrecedence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotRespondedExistence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotRespondedExistence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotResponse() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotResponse[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotPrecedence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotPrecedence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotChainResponse() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotChainResponse[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testNotChainPrecedence() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotChainPrecedence[A,B]\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("Existence[A]"));
    }

    @Test
    public void testChoiceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Choice[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("//vc"));
    }

    @Test
    public void testExclusiveChoiseWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("ExclusiveChoice[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testAbsenceNWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Absence[A,3]|\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testExistenceNWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Existence[A,3]|\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testExactlyNWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Exactly[A,3]|\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertFalse(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testRespondedExistenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("RespondedExistence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testResponseWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Response[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testAlternateResponseWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("AlternateResponse[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testChainResponseWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("ChainResponse[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testPrecedenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("Precedence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testAlternatePrecedenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("AlternatePrecedence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testChainPrecedenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("ChainPrecedence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testNotRespondedExistenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotRespondedExistence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testNotResponseWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotResponse[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testNotPrecedenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotPrecedence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testNotChainResponseWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotChainResponse[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }

    @Test
    public void testNotChainPrecedenceWithData() throws FileNotFoundException, DeclareParserException, GenerationException {
        DeclareModel model = parser.Parse("NotChainPrecedence[A,B]||\n");
        gen.Run(model, false, 1);
        String result = gen.getAlloyCode();
        Assert.assertTrue(result.contains("fact { some te: Event | te.task = A and "));
    }
}
