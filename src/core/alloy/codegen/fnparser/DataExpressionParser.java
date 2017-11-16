package core.alloy.codegen.fnparser;

import sun.plugin.dom.exception.InvalidStateException;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-19.
 */
public class DataExpressionParser {
    Pattern tokenPattern = Pattern.compile("\\(\\s*\\w+(\\s*,\\s*\\w+)+\\s*\\)|is not|is|not in|in|or|and|not|same|different|-?\\d+|\\w+\\.\\w+|\\w+|\\(|\\)|<=|>=|<|>|=");
    Pattern setTokenPattern = Pattern.compile("\\(\\s*\\w+(\\s*,\\s*\\w+)+\\s*\\)");
    Pattern opTokenPattern = Pattern.compile("is not|is|not in|in|or|and|not|same|different");
    Pattern varTokenPattern = Pattern.compile("\\w+\\.\\w+");
    Pattern numTokenPattern = Pattern.compile("-?\\d+");
    Pattern taskTokenPattern = Pattern.compile("\\w+");
    Pattern groupTokenPattern = Pattern.compile("\\(|\\)");
    Pattern compTokenPattern = Pattern.compile("<=|>=|<|>|=");

    public DataExpression parse(String code) {
        List<Token> tokens = parseTokens(code);
        DataExpression tree = buildExpressionTree(tokens);
        return tree;
    }

    private DataExpression buildExpressionTree(List<Token> tokens) {
        //priority: is/is not/in/not in, not/same/different/<>=, not, and, or
        //parsing is backwards

        tokens = unwrap(tokens);

        int depth = 0;
        for (Token i : tokens) {    //or
            if ((depth = depthLevel(i, depth)) > 0) continue;
            if (i.getType() == Token.Type.Operator && i.getValue().equals("or"))
                return new BinaryExpression(i, getLeft(tokens, i.position), getRight(tokens, i.position));
        }

        for (Token i : tokens) {    //and
            if ((depth = depthLevel(i, depth)) > 0) continue;
            if (i.getType() == Token.Type.Operator && i.getValue().equals("and"))
                return new BinaryExpression(i, getLeft(tokens, i.position), getRight(tokens, i.position));
        }

        for (Token i : tokens) {    //not
            if ((depth = depthLevel(i, depth)) > 0) continue;
            if (i.getType() == Token.Type.Operator && i.getValue().equals("not"))
                return new UnaryExpression(i, getRight(tokens, i.position));
        }

        for (Token i : tokens) {    //other unary
            if ((depth = depthLevel(i, depth)) > 0) continue;
            if (i.getType() == Token.Type.Operator && (i.getValue().equals("same") || i.getValue().equals("different")))
                return new UnaryExpression(i, getRight(tokens, i.position));
        }

        for (Token i : tokens) {    //other binary
            if ((depth = depthLevel(i, depth)) > 0) continue;
            if (i.getType() == Token.Type.Operator || i.getType() == Token.Type.Comparator)
                return new BinaryExpression(i, getLeft(tokens, i.position), getRight(tokens, i.position));
        }

        if (tokens.size() > 1)
            throw new InvalidStateException("tokens: " + tokens.size() + "\n" +
                    String.join(" ", tokens.stream().map(i -> i.getValue()).collect(Collectors.toList())));

        for (Token i : tokens) {    //values
            if (i.getType() == Token.Type.Set
                    || i.getType() == Token.Type.Task
                    || i.getType() == Token.Type.Number
                    || i.getType() == Token.Type.Variable)
                return new ValueExpression(i);
        }

        return new ValueExpression(new Token(0, Token.Type.Task, "1=1"));   // empty expression evaluates to true
    }

    private List<Token> unwrap(List<Token> tokens) {
        if (tokens.isEmpty() || tokens.get(0).getType() != Token.Type.Group)
            return tokens;

        int depth = 1;
        for (int i = 1; i < tokens.size() - 1; ++i) {
            if (depth == 0)
                return tokens;

            depth = depthLevel(tokens.get(i), depth);
        }

        if (depth == 1 && tokens.get(tokens.size() - 1).getType() == Token.Type.Group) {
            List<Token> sub = tokens.subList(1, tokens.size() - 1);
            sub.forEach(i -> i.setPosition(i.getPosition() - 1));
            return sub;
        }

        throw new InvalidStateException("parenthesis mismatch");
    }

    private DataExpression getLeft(List<Token> tokens, int position) {
        return buildExpressionTree(tokens.subList(0, position));
    }


    private DataExpression getRight(List<Token> tokens, int position) {
        List<Token> sub = tokens.subList(position + 1, tokens.size());
        sub.forEach(i -> i.setPosition(i.getPosition() - position - 1));
        return buildExpressionTree(sub);
    }

    private int depthLevel(Token t, int depth) {
        if (t.getType() == Token.Type.Group) {
            if (t.getValue().equals("("))
                ++depth;
            else
                --depth;
        }

        return depth;
    }

    private List<Token> parseTokens(String code) {
        List<Token> tokens = new ArrayList<>();
        int index = 0;
        Matcher token = tokenPattern.matcher(code);
        while (token.find()) {
            tokens.add(createToken(index++, token.group(0)));
        }

        if (!tokens.isEmpty() && tokens.stream().map(i -> i.getType() == Token.Type.Group ? i.getValue().equals("(") ? 1 : -1 : 0).reduce((i, j) -> i + j).get() != 0)
            throw new InvalidStateException("Parenthesis count not match");

        return tokens;
    }

    private Token createToken(int i, String value) {
        // Order matters!

        if (setTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Set, value);

        if (opTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Operator, value);

        if (varTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Variable, value);

        if (numTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Number, value);

        if (taskTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Task, value);

        if (groupTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Group, value);

        if (compTokenPattern.matcher(value).matches())
            return new Token(i, Token.Type.Comparator, value);

        throw new InvalidStateException("unknown token: " + value);
    }

    public void retrieveNumericExpressions(Map<String, List<DataExpression>> map, DataExpression expr) {
        if (expr.getNode().getType() == Token.Type.Comparator) {
            String var = getVariableNameFromComparison((BinaryExpression) expr);
            var = var.substring(var.indexOf('.') + 1);
            if (!map.containsKey(var))
                map.put(var, new ArrayList<>());
            map.get(var).add(expr);
        }

        if (expr instanceof UnaryExpression)
            retrieveNumericExpressions(map, ((UnaryExpression) expr).getValue());

        if (expr instanceof BinaryExpression) {
            retrieveNumericExpressions(map, ((BinaryExpression) expr).getLeft());
            retrieveNumericExpressions(map, ((BinaryExpression) expr).getRight());
        }
    }

    private String getVariableNameFromComparison(BinaryExpression expr) {
        if (expr.getLeft().getNode().getType() == expr.getRight().getNode().getType())
            throw new AssertionError("Comparison of variables unsupported yet");

        if (expr.getLeft().getNode().getType() == Token.Type.Variable)
            return expr.getLeft().getNode().getValue();

        if (expr.getRight().getNode().getType() == Token.Type.Variable)
            return expr.getRight().getNode().getValue();

        throw new InvalidStateException("Comparison should include variable");
    }


}
