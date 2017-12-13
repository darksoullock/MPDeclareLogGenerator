package core;

import core.models.serialization.EventAdapter;

import java.time.Duration;
import java.time.LocalDateTime;
import java.time.ZoneId;
import java.util.ArrayList;
import java.util.Date;
import java.util.List;
import java.util.Random;

public class TimestampGenerator {
    private LocalDateTime startDate;
    private Duration duration;
    private Random rnd = new Random();

    public TimestampGenerator(LocalDateTime startDate, Duration duration) {
        this.startDate = startDate;
        this.duration = duration;
    }

    public void setForTrace(List<EventAdapter> trace) {
        long s = duration.getSeconds();
        List<Long> offsets = new ArrayList<>();
        for (int i = 0; i < trace.size(); ++i)
            offsets.add(Math.abs(rnd.nextLong()) % s);
        offsets.sort(Long::compareTo);
        for (int i = 0; i < trace.size(); ++i) {
            trace.get(i).setTimestamp(toDate(startDate.plusSeconds(offsets.get(i))));
        }
        startDate = startDate.plusSeconds(s);
    }

    private Date toDate(LocalDateTime datetime) {
        return Date.from(datetime.atZone(ZoneId.systemDefault()).toInstant());
    }
}
