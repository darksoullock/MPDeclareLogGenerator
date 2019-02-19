package core.models.query;

import java.util.Map;
import java.util.Objects;

// State of model compliant with trace.
// Contains list valid values for each template of query
public class QueryState {
    private Map<String, QueryEvent> templateValues;

    public QueryState(Map<String, QueryEvent> templateValues) {
        this.templateValues = templateValues;
    }

    public Map<String, QueryEvent> getTemplateValuesMap() {
        return templateValues;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryState that = (QueryState) o;
        return Objects.equals(templateValues, that.templateValues);
    }

    @Override
    public int hashCode() {

        return Objects.hash(templateValues);
    }
}
