package core.SMV;

import core.Exceptions.GenerationException;
import declare.fnparser.*;
import org.apache.commons.lang3.NotImplementedException;

/**
 * Created by Vasiliy on 2018-03-27.
 */
public class DataConstraintGenerator {

    public String getLtl(DataFunction firstFunction) throws GenerationException {
        StringBuilder sb = new StringBuilder();
        sb.append(" & (");
        sb.append(generateExpression(firstFunction.getExpression()));
        sb.append(')');
        return sb.toString();
    }

    private String generateExpression(DataExpression expression) throws GenerationException {
        if (expression instanceof ValueExpression)
            return handleValueExpression((ValueExpression) expression);

        if (expression instanceof UnaryExpression)
            return handleUnaryExpression((UnaryExpression) expression);

        if (expression instanceof BinaryExpression)
            return handleBinaryExpression((BinaryExpression) expression);

        throw new NotImplementedException(expression.getClass().getName());
    }

    private String handleValueExpression(ValueExpression expression) {
        Token node = expression.getNode();
        if (node.getType() == Token.Type.Set) {   // (Activity1, Activity2, ... ActivityN)
            throw new NotImplementedException(expression.getClass().getName());
        }

        if (node.getType() == Token.Type.Variable) { // A.Data1
            return node.getValue().substring(node.getValue().indexOf('.') + 1);
        }

        if (node.getType() == Token.Type.Activity && node.getValue().equals("True[]")) { // TODO: redo
            return "TRUE";
        }

        return node.getValue();
    }

    private String handleUnaryExpression(UnaryExpression uex) throws GenerationException {
        StringBuilder tc = new StringBuilder();
        if (uex.getNode().getValue().equals("not")) {
            tc.append(" ! (");
            tc.append(generateExpression(uex.getValue()));
            tc.append(')');
            return tc.toString();
        }

        throw new GenerationException("'" + uex.getNode().getValue() + "' not supported by SMV generator");
    }

    private String handleBinaryExpression(BinaryExpression bex) throws GenerationException {
        StringBuilder tc = new StringBuilder();
        String op = bex.getNode().getValue();
        if (op.equals("and")) {
            tc.append(" (");
            tc.append(generateExpression(bex.getLeft()));
            tc.append(" & ");
            tc.append(generateExpression(bex.getRight()));
            tc.append(')');
            return tc.toString();
        }

        if (op.equals("or")) {
            tc.append(" (");
            tc.append(generateExpression(bex.getLeft()));
            tc.append(" | ");
            tc.append(generateExpression(bex.getRight()));
            tc.append(')');
            return tc.toString();
        }

        if (op.equals("is")) {
            tc.append(" (");
            tc.append(generateExpression(bex.getLeft()));
            tc.append(" = ");
            tc.append(generateExpression(bex.getRight()));
            tc.append(')');
            return tc.toString();
        }

        if (op.equals("is not")) {
            tc.append(" (");
            tc.append(generateExpression(bex.getLeft()));
            tc.append(" != ");
            tc.append(generateExpression(bex.getRight()));
            tc.append(')');
            return tc.toString();
        }

        if (op.equals(">") ||
                op.equals(">=") ||
                op.equals("<") ||
                op.equals("<=") ||
                op.equals("=")) {
            tc.append(" (");
            tc.append(generateExpression(bex.getLeft()));
            tc.append(op);
            tc.append(generateExpression(bex.getRight()));
            tc.append(')');
            return tc.toString();
        }

        throw new GenerationException("'" + bex.getNode().getValue() + "' not supported by SMV generator");
    }

}
