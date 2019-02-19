package core.models.query;

import java.util.Set;

public class TraceQueryResults {
    public TraceQueryResults(String name, Set<QueryState> states) {
        this.name = name;
        this.states = states;
    }

    private String name;
    private Set<QueryState> states;

    public String getName() {
        return name;
    }

    public void setName(String name) {
        this.name = name;
    }

    public Set<QueryState> getStates() {
        return states;
    }

    public void setStates(Set<QueryState> states) {
        this.states = states;
    }
}
