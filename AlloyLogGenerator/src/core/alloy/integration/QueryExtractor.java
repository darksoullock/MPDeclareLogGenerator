package core.alloy.integration;

import core.Global;
import core.models.query.QueryEvent;
import core.models.query.QueryState;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;

import java.io.IOException;
import java.util.*;

public class QueryExtractor {

    public Set<QueryState> get(A4Solution solution, Module world, Map<String, String> paramEncoding, Set<String> dataParams, int limit) throws Err, IOException {
        Set<QueryState> result = new HashSet<>();
        while (solution != null && solution.satisfiable() && limit > 0) {
            result.add(getOne(solution, world, paramEncoding, dataParams));
            solution = solution.next();
            --limit;
        }

        if (limit == 0) {
            Global.log.accept("Limit is reached while extracting query");
        }

        return result;
    }

    private QueryState getOne(A4Solution solution, Module world, Map<String, String> paramEncoding, Set<String> dataParams) throws IOException, Err {
        Map<String, QueryEvent> result = new HashMap<>();
        for (Map.Entry<String, String> param : paramEncoding.entrySet()) {
            QueryEvent item = new QueryEvent();
            item.setTemplateName(param.getKey());
            item.setActivity(getActivityName(solution, world, param.getValue()));
            if (dataParams.contains(param.getKey())) {
                fillData(item.getData(), solution, world, param.getValue());
            }

            String vacuityCheck;
            if (dataParams.contains(param.getKey()))
                vacuityCheck = "some te: Event | (te.task = " + param.getValue() + ".task and " + param.getValue() + ".data in te.data)";
            else
                vacuityCheck = "some te: Event | (te.task = " + param.getValue() + ".task)";

            Object ok = solution.eval(world.parseOneExpressionFromString(vacuityCheck));
            if (ok instanceof Boolean)
                item.setVacuous((Boolean) ok);

            result.put(item.getTemplateName(), item);
        }

        return new QueryState(result);
    }

    private void fillData(Map<String, String> result, A4Solution solution, Module world, String param) throws IOException, Err {
        for (A4Tuple t : (A4TupleSet) solution.eval(world.parseOneExpressionFromString(param + ".data"))) {
            result.put(t.sig(0).parent.label.substring(5), t.sig(0).label.substring(5));
        }
    }

    private String getActivityName(A4Solution solution, Module world, String param) throws Err, IOException {
        for (A4Tuple t : (A4TupleSet) solution.eval(world.parseOneExpressionFromString(param + ".task"))) {
            return t.sig(0).label.substring(5);
        }

        return null;
    }
}
