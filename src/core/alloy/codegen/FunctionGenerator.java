package core.alloy.codegen;

import core.RandomHelper;
import core.alloy.codegen.fnparser.*;
import core.models.declare.data.NumericData;
import core.models.intervals.Interval;
import sun.plugin.dom.exception.InvalidStateException;
import sun.reflect.generics.reflectiveObjects.NotImplementedException;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class FunctionGenerator {
    StringBuilder alloy;
    Map<String, NumericData> map;
    List<String> args;
    List<String> argTypes;

    public String generateFunction(String name, DataFunction function, Map<String, NumericData> map, List<String> argTypes) {
        this.alloy = new StringBuilder();
        this.map = map;
        this.args = function.getArgs();
        this.argTypes = argTypes;
        alloy.append("pred ").append(name).append('(').append(String.join(", ", function.getArgs())).append(": set TaskEvent) { { ");
        String continuation = generateExpression(function.getExpression());
        alloy.append(" } }\n");
        alloy.append(continuation);
        return alloy.toString();
    }

    private String generateExpression(DataExpression expression) {
        if (expression instanceof ValueExpression)
            return handleValueExpression((ValueExpression) expression);

        if (expression instanceof UnaryExpression)
            return handleUnaryExpression((UnaryExpression) expression);

        if (expression instanceof BinaryExpression)
            return handleBinaryExpression((BinaryExpression) expression);

        throw new NotImplementedException();
    }

    private String handleValueExpression(ValueExpression expression) {
        Token node = expression.getNode();
        if (node.getType() == Token.Type.Set) {   // (Task1, Task2, ... TaskN)
            alloy.append(node.getValue().replace(',', '+'));
            return "";
        }

        if (node.getType() == Token.Type.Variable) { // A.Data1
            alloy.append(node.getValue().replace(".", ".data&"));
            return "";
        }

        alloy.append(node.getValue());
        return "";
    }

    private String handleUnaryExpression(UnaryExpression uex) {
        StringBuilder tc = new StringBuilder();
        if (uex.getNode().getValue().equals("same")) {
            if (map.containsKey(getFieldType(uex.getValue().getNode().getValue()))) {
                return handleNumericSame(uex.getValue().getNode().getValue());
            }
            alloy.append('(').append(args.get(0)).append(".data&");
            tc.append(generateExpression(uex.getValue()));
            alloy.append('=').append(args.get(1)).append(".data&");
            tc.append(generateExpression(uex.getValue()));
            alloy.append(')');
            return tc.toString();
        }

        if (uex.getNode().getValue().equals("different")) {
            alloy.append("not (").append(args.get(0)).append(".data&");
            tc.append(generateExpression(uex.getValue()));
            alloy.append('=').append(args.get(1)).append(".data&");
            tc.append(generateExpression(uex.getValue()));
            alloy.append(')');
            return tc.toString();
        }


        alloy.append(uex.getNode().getValue()).append(" (");
        tc.append(generateExpression(uex.getValue()));
        alloy.append(')');
        return tc.toString();
    }

    private String handleNumericSame(String value) {
        int token = RandomHelper.getNext();
        String aToken = "Get" + value + token;
        String bToken = "Set" + value + token;
        alloy.append('(').append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(" and ").append(aToken).append(" in ").append(args.get(0))
                .append(".tokens and ").append(bToken).append(" in ").append(args.get(1)).append(".tokens)");

        StringBuilder tc = new StringBuilder();
        tc.append("one sig ").append(aToken).append(" extends Token {}\none sig ").append(bToken)
                .append(" extends Token {}\nfact {\nall te: TaskEvent | (te.task = ").append(argTypes.get(0))
                .append(" or not ").append(aToken).append(" in te.tokens) and (te.task = ").append(argTypes.get(1))
                .append(" or not ").append(bToken).append(" in te.tokens )\nsome te: TaskEvent | ").append(aToken)
                .append(" in te.tokens implies (all ote: TaskEvent| ").append(aToken).append(" in ote.tokens or ")
                .append(bToken).append(" in ote.tokens implies ote.data&").append(value).append(" = te.data&")
                .append(value).append(")\n#{te: TaskEvent | ").append(aToken).append(" in te.tokens } = #{te: TaskEvent | ")
                .append(bToken).append(" in te.tokens }\n}\n");
        return tc.toString();
    }

    private String handleBinaryExpression(BinaryExpression bex) {
        if (bex.getNode().getType() == Token.Type.Comparator) {
            handleNumeric(bex);
            return "";
        }

        StringBuilder tc = new StringBuilder();

        if (bex.getNode().getValue().equals("is")) {
            alloy.append('(');
            tc.append(generateExpression(bex.getLeft()));
            alloy.append('=');
            tc.append(generateExpression(bex.getRight()));
            alloy.append(')');
            return tc.toString();
        }

        if (bex.getNode().getValue().equals("is not")) {
            alloy.append("(not ");
            tc.append(generateExpression(bex.getLeft()));
            alloy.append('=');
            tc.append(generateExpression(bex.getRight()));
            alloy.append(')');
            return tc.toString();
        }

        if (bex.getNode().getValue().equals("in")) {
            alloy.append("(#{");
            tc.append(generateExpression(bex.getLeft()));
            alloy.append('&');
            tc.append(generateExpression(bex.getRight()));
            alloy.append("} = 1)");
            return tc.toString();
        }

        if (bex.getNode().getValue().equals("not in")) {
            alloy.append("(#{");
            tc.append(generateExpression(bex.getLeft()));
            alloy.append('&');
            tc.append(generateExpression(bex.getRight()));
            alloy.append("} = 0)");
            return tc.toString();
        }

        alloy.append('(');
        tc.append(generateExpression(bex.getLeft()));
        alloy.append(' ').append(bex.getNode().getValue()).append(' ');
        tc.append(generateExpression(bex.getRight()));
        alloy.append(')');
        return tc.toString();
    }

    private void handleNumeric(BinaryExpression bex) {
        String var = getVariable(bex);
        String field = getFieldType(var);
        Map<String, Interval> intervalsMap = map.get(field).getMapping();
        List<String> intervalsNames = new ArrayList<>();
        for (String i : intervalsMap.keySet())
            if (intervalsMap.get(i).isCompliant(bex))
                intervalsNames.add(i);

        alloy.append(var.replace(".", ".data&")).append(" in ").append('(').append(String.join(" + ", intervalsNames)).append(')');
    }

    private String getFieldType(String var) {
        return var.substring(var.indexOf('.') + 1);
    }

    private String getVariable(BinaryExpression bex) {
        if (bex.getLeft().getNode().getType() == Token.Type.Variable)
            return bex.getLeft().getNode().getValue();

        if (bex.getRight().getNode().getType() == Token.Type.Variable)
            return bex.getRight().getNode().getValue();

        throw new InvalidStateException("No variable in " + bex.toString());
    }
}
