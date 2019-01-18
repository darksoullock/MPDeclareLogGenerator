package core.models.query;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.function.Function;
import java.util.stream.Collectors;

public class QueryEvent {
    private String param;
    private String activity;
    private Map<String, String> data;
    private boolean vacuous;

    public QueryEvent() {
        data = new HashMap<>();
    }

    public String getParam() {
        return param;
    }

    public void setParam(String param) {
        this.param = param;
    }

    public String getActivity() {
        return activity;
    }

    public void setActivity(String activity) {
        this.activity = activity;
    }

    public Map<String, String> getData() {
        return data;
    }

    public void setData(Map<String, String> data) {
        this.data = data;
    }

    public boolean isVacuous() {
        return vacuous;
    }

    public void setVacuous(boolean vacuous) {
        this.vacuous = vacuous;
    }

    public String toString(Map<String, String> codeToName) {
        return param + ": " +
                "activity: '" + codeToName.get(activity) + '\'' +
                ", data: \n" + String.join("\n", data.entrySet().stream().map(encodedDataEntryToString(codeToName)).collect(Collectors.toList())) +
                ", present=" + vacuous
                ;
    }

    private Function<Map.Entry<String, String>, String> encodedDataEntryToString(Map<String, String> codeToName) {
        return i -> codeToName.get(i.getKey()) + "=" + codeToName.get(i.getValue());
    }

    @Override
    public String toString() {
        return param + ": " +
                "activity='" + activity + '\'' +
                ", data=" + data +
                ", present=" + vacuous
                ;
    }

    @Override
    public boolean equals(Object o) {
        if (this == o) return true;
        if (o == null || getClass() != o.getClass()) return false;
        QueryEvent that = (QueryEvent) o;
        return Objects.equals(param, that.param) &&
                Objects.equals(activity, that.activity) &&
                Objects.equals(data, that.data);
    }

    @Override
    public int hashCode() {

        return Objects.hash(param, activity, data);
    }
}
