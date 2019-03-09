package core.models.intervals;

import core.exceptions.BadSolutionException;
import core.exceptions.GenerationException;
import declare.DeclareParserException;
import declare.fnparser.BinaryExpression;
import declare.fnparser.DataExpression;
import declare.fnparser.Token;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public abstract class Interval {
    protected Random rnd = new Random();

    public abstract String get();

    Map<String, String> sameCache;

    public String getSame(List<String> keys) {
        String value = null;
        for (String key : keys)
            if (sameCache.containsKey(key))
                value = sameCache.get(key);

        if (value == null)
            value = get();

        for (String key : keys)
            sameCache.put(key, value);

        return value;
    }

    public void resetCaches() {
        if (sameCache == null || sameCache.size() > 0)
            sameCache = new HashMap<>();
    }

    public abstract String getDifferent(List<String> tokens) throws BadSolutionException;

    public abstract boolean isCompliant(DataExpression expr) throws GenerationException, DeclareParserException;

    protected BinaryExpression rot(BinaryExpression expr) {   // move number to the right part of expression
        if (expr.getRight().getNode().getType() == Token.Type.Number)
            return expr;

        Token t = expr.getNode();
        String newOp = t.getValue().contains(">") ? t.getValue().replace('>', '<') : t.getValue().replace('<', '>');
        return new BinaryExpression(new Token(t.getPosition(), t.getType(), newOp), expr.getRight(), expr.getLeft());
    }

    public abstract int getValueCount(int limit);



}
