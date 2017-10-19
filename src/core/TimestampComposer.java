package core;

import java.time.LocalDateTime;
import java.time.ZoneOffset;
import java.util.Date;
import java.util.Random;

public class TimestampComposer { // TODO review
    private static final LocalDateTime referenceDate = LocalDateTime.now();
    private static final Random rand = new Random();

    public static Date composeForEvent(int eventNo) {
        LocalDateTime newDate = referenceDate.plusMinutes((long)eventNo).plusSeconds(rand.nextInt(60));
        return new Date(newDate.toInstant(ZoneOffset.UTC).toEpochMilli());
    }
}
