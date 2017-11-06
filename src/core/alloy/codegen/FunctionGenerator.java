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


        alloy.append(uex.getNode().getValue()).append(" (");
        tc.append(generateExpression(uex.getValue()));
        alloy.append(')');
        return tc.toString();
    }

    private String handleNumericDifferent(String value) {
        String token = Global.constants.getDifferentPrefix() + value + RandomHelper.getNext();
        alloy.append("(not ").append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(") or (").append(args.get(0)).append(".data&").append(value)
                .append('=').append(args.get(1)).append(".data&").append(value).append(" and one (").append(token)
                .append(" & ").append(args.get(1)).append(".tokens) and (").append(token).append(" & ")
                .append(args.get(0)).append(".tokens) = (").append(token).append(" & ").append(args.get(1))
                .append(".tokens)) ");

        StringBuilder tc = new StringBuilder();
        tc.append("abstract sig ").append(token).append(" extends Token {}\n").append("fact { all te:TaskEvent | #{")
                .append(token).append(" & te.tokens}>0 implies #{").append(value).append("&te.data}>0 and not Single[")
                .append(value).append("&te.data] }\n");

        for (int i = 0; i < maxSameInstances; ++i) {
            String ast = token + 'i' + i;
            tc.append("one sig ").append(ast).append(" extends ").append(token).append(" {}\n")
                    .append("fact { #{te: TaskEvent | ").append(ast).append(" in te.tokens}=0 or #{te: TaskEvent | ")
                    .append(ast).append(" in te.tokens } = 2}\n");
        }

        return tc.toString();
    }

    private String handleNumericSame(String value) {
        int token = RandomHelper.getNext();
        String aToken = Global.constants.getSamePrefix1() + value + token;
        String bToken = Global.constants.getSamePrefix2() + value + token;
        alloy.append('(').append(args.get(0)).append(".data&").append(value).append('=').append(args.get(1))
                .append(".data&").append(value).append(" and ((one (").append(aToken).append(" & ").append(args.get(0))
                .append(".tokens) and one (").append(bToken).append(" & ").append(args.get(1)).append(".tokens) and (")
                .append(aToken).append(" & ").append(args.get(0)).append(".tokens).id = (").append(bToken).append(" & ")
                .append(args.get(1)).append(".tokens).id) " +
                //"or Single[").append(args.get(0)).append(".data&").append(value).append("]" + //TODO: as a parameter
                /*
                uncomment previous line to make it work faster,
                but then 'same' for numbers will prefer numbers
                from the intervals 'EqualToN' in most cases.
                not recommended for short logs.
                 */
                "))");

        StringBuilder tc = new StringBuilder();
        tc.append("abstract sig ").append(aToken).append(" extends Token {\nid: disj Int\n}\nabstract sig ")
                .append(bToken).append(" extends Token {\nid: disj Int\n}\n");

        for (int i = 0; i < maxSameInstances; ++i) {
            String ast = aToken + 'i' + i;
            String bst = bToken + 'i' + i;
            tc.append("one sig ").append(ast).append(" extends ").append(aToken).append(" {} {id=")
                    .append(minInt + i).append("}\n").append("one sig ").append(bst).append(" extends ").append(bToken)
                    .append(" {} {id=").append(minInt + i).append("}\n").append("fact {\n#{te: TaskEvent | ").append(ast)
                    .append(" in te.tokens}<=1\n#{te: TaskEvent | ").append(ast).append(" in te.tokens } = #{te: TaskEvent | ")
                    .append(bst).append(" in te.tokens }\n}\n");
        }

        tc.append("fact {\nall te: TaskEvent | (te.task = ").append(argTypes.get(0))
                .append(" or #{").append(aToken).append(" & te.tokens}<=0) and (te.task = ").append(argTypes.get(1))
                .append(" or #{").append(bToken).append(" & te.tokens}<=0)\nsome te: TaskEvent | ").append(aToken)
                .append(" in te.tokens implies (all ote: TaskEvent| ").append(aToken).append(" in ote.tokens or ")
                .append(bToken).append(" in ote.tokens implies ote.data&").append(value).append(" = te.data&")
                .append(value).append(")\n}\n");
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
