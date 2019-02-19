package core;

import core.helpers.RandomHelper;
import declare.fnparser.Token;
import declare.lang.Constraint;
import declare.lang.DataConstraint;

import java.util.*;

public class QueryBuider {

    private Map<String, String> paramEncoding = new HashMap<>();
    private Set<String> dataParams = new HashSet<>();
    private Map<String, String> nameToCode;

    public QueryBuider(Map<String, String> nameToCode ) {
        this.nameToCode = nameToCode;
    }

    public void extractQueryParams(List constraints) {
        for (Constraint constraint : (List<Constraint>) constraints) {
            encodeQueryParam(paramEncoding, constraint, 0);
            if (constraint.isBinary()) {
                encodeQueryParam(paramEncoding, constraint, 1);
            }
        }
    }

    private void encodeQueryParam(Map<String, String> paramEncoding, Constraint constraint, int n) {
        String name = constraint.getArgs().get(n);
        if (name.startsWith("?")) {
            String encoded = paramEncoding.getOrDefault(name, RandomHelper.getName());
            paramEncoding.put(name, encoded);
            constraint.getArgs().set(n, encoded + ".task");
            if (constraint instanceof DataConstraint) {
                Token node = ((DataConstraint) constraint).getFunctions().get(n).getExpression().getNode();
                if (node.getType().equals(Token.Type.R) && node.getValue().equals("?")) {
                    node.setValue(encoded + ".data=" + (char) ('A' + n) + ".data");
                    dataParams.add(name);
                }
            }
        } else {
            constraint.getArgs().set(n, nameToCode.get(name));
        }
    }

    public Map<String, String> getParamEncoding() {
        return paramEncoding;
    }

    public Set<String> getDataParams() {
        return dataParams;
    }
}
