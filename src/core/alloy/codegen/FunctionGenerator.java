package core.alloy.codegen;

import core.Global;
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
    int maxSameInstances;
    int minInt;

    public FunctionGenerator(int maxSameInstances, int bitwidth) {
        this.maxSameInstances = maxSameInstances;
        this.minInt = -(int) Math.pow(2, bitwidth - 1);
    }

    public String generateFunction(String name, DataFunction function, Map<String, NumericData> map, List<String> argTypes) {
        init(function, map, argTypes);
        alloy.append("pred ").append(name).append('(').append(String.join(", ", function.getArgs())).append(": set TaskEvent) { { ");
        String continuation = generateExpression(handleNegativeNumericComparison(function.getExpression()));
        alloy.append(" } }\n");
        alloy.append(continuation);
        return alloy.toString();
    }

    public String generateNotFunction(String name, DataFunction function, Map<String, NumericData> map, List<String> argTypes) {
        init(function, map, argTypes);
        alloy.append("pred ").append(name).append('(').append(String.join(", ", function.getArgs())).append(": set TaskEvent) { { ");
        DataExpression expr = handleNegativeNumericComparison(function.getExpression());
        expr = inverseNotConstraintNumericComparison(expr);
        String continuation = generateExpression(expr);
        alloy.append(" } }\n");
        alloy.append(continuation);
        return alloy.toString();
    }

    private DataExpression inverseNotConstraintNumericComparison(DataExpression expression) {
        if (expression.getNode().getValue().equals("same") && isNumeric((UnaryExpression) expression))
            return new UnaryExpression(
                    new Token(0, Token.Type.Operator, "nsame"),
                    ((UnaryExpression) expression).getValue());

        if (expression.getNode().getValue().equals("different") && isNumeric((UnaryExpression) expression))
            return new UnaryExpression(
                    new Token(0, Token.Type.Operator, "ndifferent"),
                    ((UnaryExpression) expression).getValue());

        if (expression instanceof BinaryExpression)
            return new BinaryExpression(expression.getNode(),
                    inverseNotConstraintNumericComparison(((BinaryExpression) expression).getLeft()),
                    inverseNotConstraintNumericComparison(((BinaryExpression) expression).getRight()));

        if (expression instanceof UnaryExpression)
            return new UnaryExpression(expression.getNode(),
                    inverseNotConstraintNumericComparison(((UnaryExpression) expression).getValue()));

        return expression;
    }

    private boolean isNumeric(UnaryExpression expression) {
        return map.containsKey(expression.getValue().getNode().getValue());
    }

    private void init(DataFunction function, Map<String, NumericData> map, List<String> argTypes) {
        this.alloy = new StringBuilder();
        this.map = map;
        this.args = function.getArgs();
        this.argTypes = argTypes;
    }

    private DataExpression handleNegativeNumericComparison(DataExpression expression) {
        if (expression instanceof BinaryExpression) {
            DataExpression l = ((BinaryExpression) expression).getLeft();
            if (isNot(l))
                l = not((UnaryExpression) l);
            DataExpression r = ((BinaryExpression) expression).getRight();
            if (isNot(r))
                r = not((UnaryExpression) r);
            l = handleNegativeNumericComparison(l);
            r = handleNegativeNumericComparison(r);
            return new BinaryExpression(expression.getNode(), l, r);
        }

        if (isNot(expression)) {
            DataExpression negated = not((UnaryExpression) expression);
            if (isNot(negated))
                return negated;
            return handleNegativeNumericComparison(negated);
        }

        return expression;
    }

    private DataExpression not(UnaryExpression expression) {
        DataExpression sub = expression.getValue();
        if (sub instanceof BinaryExpression) {
            if (sub.getNode().getValue().equals("and") || sub.getNode().getValue().equals("or")) {
                Token token = new Token(sub.getNode().getPosition(), sub.getNode().getType(), sub.getNode().getValue().equals("and") ? "or" : "and");
                Token notToken = new Token(-1, Token.Type.Operator, "not");
                return new BinaryExpression(token,
                        new UnaryExpression(notToken, ((BinaryExpression) sub).getLeft()),
                        new UnaryExpression(notToken, ((BinaryExpression) sub).getRight()));
            }
        }

        if (sub instanceof UnaryExpression) {
            if (sub.getNode().getValue().equals("same") ||
                    sub.getNode().getValue().equals("different")) {
                return new UnaryExpression(
                        new Token(0, Token.Type.Operator, sub.getNode().getValue().equals("same") ? "different" : "same"),
                        ((UnaryExpression) sub).getValue());
            }
        }

        return expression;
    }

    private boolean isNot(DataExpression expression) {
        return expression.getNode().getValue().equals("not");
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
            if (map.containsKey(getFieldType(uex.getValue().getNode().getValue()))) {
                return handleNumericDifferent(uex.getValue().getNode().getValue());
            }
            alloy.append("not (").append(args.get(0)).append(".data&");
            tc.append(generateExpression(uex.getValue()));
            alloy.append('=').append(args.get(1)).append(".data&");
            tc.append(generateExpression(uex.getValue()));
            alloy.append(')');
            return tc.toString();
        }

        if (uex.getNode().getValue().equals("nsame")) {
            return handleInverseNumericSame(uex.getValue().getNode().getValue());
        }

        if (uex.getNode().getValue().equals("ndifferent")) {
            return handleInverseNumericDifferent(uex.getValue().getNode().getValue());
        }


        alloy.append(uex.getNode().getValue()).append(" (");
        tc.append(generateExpression(uex.getValue()));
        alloy.append(')');
        return tc.toString();
    }

    private String handleNumericSame(String value) {
        String token = Global.samePrefix + value + RandomHelper.getNext();
        alloy.append('(').append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(" and ((one (").append(token).append(" & ").append(args.get(0))
                .append(".tokens)  and (").append(token).append(" & ").append(args.get(0)).append(".tokens) = (")
                .append(token).append(" & ").append(args.get(1)).append(".tokens)) ");
        if (Global.singleFirstForSame)
            alloy.append("or Single[").append(args.get(0)).append(".data&").append(value).append("]");
        alloy.append("))");

        return generateSameTokens(value, token);
    }

    private String handleNumericDifferent(String value) {
        String token = Global.differentPrefix + value + RandomHelper.getNext();
        alloy.append("(not ").append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(") or (").append(args.get(0)).append(".data&").append(value)
                .append('=').append(args.get(1)).append(".data&").append(value).append(" and one (").append(token)
                .append(" & ").append(args.get(1)).append(".tokens) and (").append(token).append(" & ")
                .append(args.get(0)).append(".tokens) = (").append(token).append(" & ").append(args.get(1))
                .append(".tokens)) ");

        return generateDifferentTokens(value, token);
    }

    private String handleInverseNumericSame(String value) {
        String token = Global.differentPrefix + value + RandomHelper.getNext();
        alloy.append('(').append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(" and (not ( one (").append(token).append(" & ").append(args.get(0))
                .append(".tokens & ").append(args.get(1)).append(".tokens))))");

        return generateDifferentTokens(value, token);
    }

    private String handleInverseNumericDifferent(String value) {
        String token = Global.samePrefix + value + RandomHelper.getNext();
        alloy.append("(not ").append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(") or ((not ");
        if (Global.singleFirstForSame)
            alloy.append(" Single[").append(args.get(0)).append(".data&").append(value).append("] and not ");
        alloy.append("(some((").append(token)
                .append(" & ").append(args.get(1)).append(".tokens)) and one (").append(token).append(" & ")
                .append(args.get(0)).append(".tokens & ").append(token).append(" & ").append(args.get(1))
                .append(".tokens)))) ");

        return generateSameTokens(value, token);
    }

    private String generateSameTokens(String value, String token) {
        StringBuilder tc = new StringBuilder();
        tc.append("abstract sig ").append(token).append(" extends SameToken {}\n");

        for (int i = 0; i < maxSameInstances; ++i) {
            String ast = token + 'i' + i;
            tc.append("one sig ").append(ast).append(" extends ").append(token).append(" {}\n").append("fact {\nall te: TaskEvent | ")
                    .append(ast).append(" in te.tokens implies (one ote: TaskEvent | not ote = te and ").append(ast).append(" in ote.tokens)\n}\n");
        }

        tc.append("fact {\nall te: TaskEvent | (te.task = ").append(argTypes.get(0)).append(" or te.task = ")
                .append(argTypes.get(1)).append(" or no (").append(token).append(" & te.tokens))\nsome te: TaskEvent | ")
                .append(token).append(" in te.tokens implies (all ote: TaskEvent| ").append(token)
                .append(" in ote.tokens implies ote.data&").append(value).append(" = te.data&").append(value).append(")\n}\n");

        return tc.toString();
    }

    private String generateDifferentTokens(String value, String token) {
        StringBuilder tc = new StringBuilder();
        tc.append("abstract sig ").append(token).append(" extends DiffToken {}\n").append("fact { all te:TaskEvent | (some ")
                .append(token).append(" & te.tokens) implies (some ").append(value).append("&te.data) and not Single[")
                .append(value).append("&te.data] }\n");

        tc.append("fact { all te:TaskEvent| some (te.data&").append(value).append(") implies #{te.tokens&").append(token)
                .append("}<Amount[te.data&").append(value).append("]}\n");

        for (int i = 0; i < maxSameInstances; ++i) {
            String ast = token + 'i' + i;
            tc.append("one sig ").append(ast).append(" extends ").append(token).append(" {}\n")
                    .append("fact { all te: TaskEvent | ")
                    .append(ast).append(" in te.tokens implies (one ote: TaskEvent | not ote = te and ").append(ast).append(" in ote.tokens) }\n");
        }

        return tc.toString();
    }

    private String handleBinaryExpression(BinaryExpression bex) {
        if (bex.getNode().getType() == Token.Type.Comparator) {
            handleNumericComparison(bex);
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
            alloy.append("(one (");
            tc.append(generateExpression(bex.getLeft()));
            alloy.append('&');
            tc.append(generateExpression(bex.getRight()));
            alloy.append("))");
            return tc.toString();
        }

        if (bex.getNode().getValue().equals("not in")) {
            alloy.append("(no (");
            tc.append(generateExpression(bex.getLeft()));
            alloy.append('&');
            tc.append(generateExpression(bex.getRight()));
            alloy.append("))");
            return tc.toString();
        }

        alloy.append('(');
        tc.append(generateExpression(bex.getLeft()));
        alloy.append(' ').append(bex.getNode().getValue()).append(' ');
        tc.append(generateExpression(bex.getRight()));
        alloy.append(')');
        return tc.toString();
    }

    private void handleNumericComparison(BinaryExpression bex) {
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
