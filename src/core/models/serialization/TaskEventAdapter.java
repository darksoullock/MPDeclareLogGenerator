package core.models.serialization;


import java.util.List;

public class TaskEventAdapter {
    private int position;
    private String taskName;
    private List<Payload> payload;

    public TaskEventAdapter(int position, String taskName, List<Payload> payload) {
        this.position = position;
        this.taskName = taskName;
        this.payload = payload;
    }

    public int getPosition() {
        return position;
    }

    public String getTaskName() {
        return this.taskName;
    }

    public List<Payload> getPayload() {
        return payload;
    }
}
