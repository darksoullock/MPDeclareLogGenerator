package core.alloy.codegen;

import core.alloy.codegen.fnparser.*;
import core.models.intervals.Interval;
import core.models.declare.DataConstraint;
import core.models.declare.data.NumericData;
import sun.plugin.dom.exception.InvalidStateException;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class DataConstraintGenerator {

    DataConstraint constraint;
    Map<String, NumericData> map;
    StringBuilder alloy = new StringBuilder();

    public String Generate(DataConstraint c, String name, Map<String, NumericData> map) {
        constraint = c;
        this.map = map;
        if (c.getName().equals("Absence"))
            AddAbsenceDataConstraint(c, name);

        return alloy.toString();
    }

    private void AddAbsenceDataConstraint(DataConstraint one, String name) {
        alloy.append("fact { no te: TaskEvent | te.task = ").append(one.getFirstArg()).append(" and ").append(name).append("[te.data] }\n");
        generateFunction(name, one.getFirstFunction());
    }

    private void generateFunction(String name, DataFunction function) {
        alloy.append("pred ").append(name).append('(').append(String.join(", ", function.getArgs())).append(": set Payload) { { ");
        generateExpression(function.getExpression());
        alloy.append(" } }\n");
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
            alloy.append('(').append(getFstFnArg()).append('&');
            generateExpression(uex.getValue());
            alloy.append('=').append(getSndFnArg()).append('&');
            generateExpression(uex.getValue());
            alloy.append(')');
            return;
        }

        if (uex.getNode().getValue().equals("different")) {
            alloy.append("not (").append(getFstFnArg()).append('&');
            generateExpression(uex.getValue());
            alloy.append('=').append(getSndFnArg()).append('&');
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

    private String getFstFnArg() {
        return constraint.getFirstFunction().getArgs().get(0);
    }

    private String getSndFnArg() {
        return constraint.getSecondFunction().getArgs().get(1);
    }
}
