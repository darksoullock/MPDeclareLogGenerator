package core.models.query;

import java.util.List;
import java.util.Objects;

public class QueryState {
    private List<QueryEvent> state;

    public QueryState(List<QueryEvent> state) {
        this.state = state;
    }

    public List<QueryEvent> getState() {
        return state;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryState that = (QueryState) o;
        return Objects.equals(state, that.state);
    }

    @Override
    public int hashCode() {

        return Objects.hash(state);
    }
}
