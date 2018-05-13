package core.models.serialization;


import java.util.Date;
import java.util.List;

public class EventAdapter {
    private int position;
    private String taskName;
    private List<Payload> payload;
    private Date timestamp;

    public EventAdapter(int position, String taskName, List<Payload> payload) {
        this.position = position;
        this.taskName = taskName;
        this.payload = payload;
    }

    public int getPosition() {
        return position;
    }

    public String getActivityName() {
        return this.taskName;
    }

    public List<Payload> getPayload() {
        return payload;
    }

    public Date getTimestamp() {
        return timestamp;
    }

    public void setTimestamp(Date timestamp) {
        this.timestamp = timestamp;
    }
}
