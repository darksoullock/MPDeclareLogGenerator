package core.models.serialization;


import java.util.List;

public class EventAdapter {
    private int position;
    private String taskName;
    private List<Payload> payload;

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
}
