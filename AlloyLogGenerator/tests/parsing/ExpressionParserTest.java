package parsing;

import core.exceptions.GenerationException;
import core.alloy.codegen.AlloyCodeGenerator;
import declare.DeclareModel;
import declare.DeclareParser;
import declare.DeclareParserException;
import declare.fnparser.DataExpressionParser;
import org.testng.annotations.Test;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class ExpressionParserTest {
    DataExpressionParser parser = new DataExpressionParser();
    AlloyCodeGenerator gen = new AlloyCodeGenerator(1, 1, 3, 0, true, false, true);

    @Test(expectedExceptions = DeclareParserException.class)
    public void testSpellingError() throws DeclareParserException, GenerationException {
        DeclareModel model = new DeclareParser().Parse("Choiced[A,B]\n");
        gen.Run(model, false, 1, null);
    }

    @Test(expectedExceptions = DeclareParserException.class)
    public void testSpellingErrorWithData() throws DeclareParserException, GenerationException {
        DeclareModel model = new DeclareParser().Parse("Choise[A,B]||\n");
        gen.Run(model, false, 1, null);
    }
}
