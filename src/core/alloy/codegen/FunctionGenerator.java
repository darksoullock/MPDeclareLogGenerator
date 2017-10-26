package core.alloy.codegen;

import core.alloy.codegen.fnparser.*;
import core.models.declare.data.NumericData;
import core.models.intervals.Interval;
import sun.plugin.dom.exception.InvalidStateException;

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

    public String generateFunction(String name, DataFunction function, Map<String, NumericData> map) {
        this.alloy = new StringBuilder();
        this.map = map;
        this.args = function.getArgs();
        alloy.append("pred ").append(name).append('(').append(String.join(", ", function.getArgs())).append(": set Payload) { { ");
        generateExpression(function.getExpression());
        alloy.append(" } }\n");
        return alloy.toString();
    }

    private void generateExpression(DataExpression expression) {
        if (expression instanceof ValueExpression)
            handleValueExpression((ValueExpression) expression);

        if (expression instanceof UnaryExpression)
            handleUnaryExpression((UnaryExpression) expression);

        if (expression instanceof BinaryExpression)
            handleBinaryExpression((BinaryExpression) expression);
    }

    private void handleValueExpression(ValueExpression expression) {
        Token node = expression.getNode();
        if (node.getType() == Token.Type.Set) {   // (Task1, Task2, ... TaskN)
            alloy.append(node.getValue().replace(',', '+'));
            return;
        }

        if (node.getType() == Token.Type.Variable) { // A.Data1
            alloy.append(node.getValue().replace('.', '&'));
            return;
        }

        alloy.append(node.getValue());
    }

    private void handleUnaryExpression(UnaryExpression uex) {
        if (uex.getNode().getValue().equals("same")) {
            alloy.append('(').append(args.get(0)).append('&');
            generateExpression(uex.getValue());
            alloy.append('=').append(args.get(1)).append('&');
            generateExpression(uex.getValue());
            alloy.append(')');
            return;
        }

        if (uex.getNode().getValue().equals("different")) {
            alloy.append("not (").append(args.get(0)).append('&');
            generateExpression(uex.getValue());
            alloy.append('=').append(args.get(1)).append('&');
            generateExpression(uex.getValue());
            alloy.append(')');
            return;
        }


        alloy.append(uex.getNode().getValue()).append(" (");
        generateExpression(uex.getValue());
        alloy.append(')');
    }

    private void handleBinaryExpression(BinaryExpression bex) {
        if (bex.getNode().getType() == Token.Type.Comparator) {
            handleNumeric(bex);
            return;
        }

        if (bex.getNode().getValue().equals("is")) {
            alloy.append('(');
            generateExpression(bex.getLeft());
            alloy.append('=');
            generateExpression(bex.getRight());
            alloy.append(')');
            return;
        }

        if (bex.getNode().getValue().equals("is not")) {
            alloy.append("(not ");
            generateExpression(bex.getLeft());
            alloy.append('=');
            generateExpression(bex.getRight());
            alloy.append(')');
            return;
        }

        if (bex.getNode().getValue().equals("in")) {
            alloy.append("(#{");
            generateExpression(bex.getLeft());
            alloy.append('&');
            generateExpression(bex.getRight());
            alloy.append("} = 1)");
            return;
        }

        if (bex.getNode().getValue().equals("not in")) {
            alloy.append("(#{");
            generateExpression(bex.getLeft());
            alloy.append('&');
            generateExpression(bex.getRight());
            alloy.append("} = 0)");
            return;
        }

        alloy.append('(');
        generateExpression(bex.getLeft());
        alloy.append(' ').append(bex.getNode().getValue()).append(' ');
        generateExpression(bex.getRight());
        alloy.append(')');
    }

    private void handleNumeric(BinaryExpression bex) {
        String var = getVariable(bex);
        String field = var.substring(var.indexOf('.') + 1);
        Map<String, Interval> intervalsMap = map.get(field).getMapping();
        List<String> intervalsNames = new ArrayList<>();
        for (String i : intervalsMap.keySet())
            if (intervalsMap.get(i).isCompliant(bex))
                intervalsNames.add(i);

        alloy.append(var.replace('.', '&')).append(" in ").append('(').append(String.join(" + ", intervalsNames)).append(')');
    }

    private String getVariable(BinaryExpression bex) {
        if (bex.getLeft().getNode().getType() == Token.Type.Variable)
            return bex.getLeft().getNode().getValue();

        if (bex.getRight().getNode().getType() == Token.Type.Variable)
            return bex.getRight().getNode().getValue();

        throw new InvalidStateException("No variable in " + bex.toString());
    }
}
