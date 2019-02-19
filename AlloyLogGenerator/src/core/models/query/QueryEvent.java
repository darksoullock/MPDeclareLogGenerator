package core.models.query;

import java.util.HashMap;
import java.util.Map;
import java.util.Objects;

//contains name and value(s) for one query template
public class QueryEvent {
    private String templateName;
    private String activity;
    private Map<String, String> data;
    private boolean vacuous;

    public QueryEvent() {
        data = new HashMap<>();
    }

    public String getTemplateName() {
        return templateName;
    }

    public void setTemplateName(String templateName) {
        this.templateName = templateName;
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

    public void decode(Map<String, String> codeToName) {
        activity = codeToName.get(activity);
        Map<String, String> decodedData = new HashMap<>();
        data.forEach((key, value) -> decodedData.put(codeToName.get(key), removePrefix(codeToName.getOrDefault(value, value), codeToName.get(key))));
        data = decodedData;
    }

    private String removePrefix(String s, String prefix) {
        if (s != null && s.startsWith(prefix) && s.length() > prefix.length() + 1) {
            return s.substring(prefix.length() + 1);
        }

        return s;
    }

    @Override
    public String toString() {
        return templateName + ": " +
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
        return Objects.equals(templateName, that.templateName) &&
                Objects.equals(activity, that.activity) &&
                Objects.equals(data, that.data);
    }

    @Override
    public int hashCode() {

        return Objects.hash(templateName, activity, data);
    }
}
