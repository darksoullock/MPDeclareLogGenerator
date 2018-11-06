package declare.validators;

import com.google.gson.Gson;
import declare.DeclareParserException;
import declare.fnparser.DataExpressionParser;

/**
 * Created by Vasiliy on 2018-06-09.
 */
public class FunctionValidator {
    public static String validate(String functionString) {
        ValidationResult result = new ValidationResult();
        try {
            new DataExpressionParser().parse(functionString);
        } catch (DeclareParserException e) {
            result.setErrorCode(1);
            result.setMessage(e.getMessage());
        }

        return new Gson().toJson(result);
    }

    public static class ValidationResult {
        int errorCode;
        String message;

        public int getErrorCode() {
            return errorCode;
        }

        public void setErrorCode(int errorCode) {
            this.errorCode = errorCode;
        }

        public String getMessage() {
            return message;
        }

        public void setMessage(String message) {
            this.message = message;
        }
    }
}
