package core.interfaces;

import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.XTrace;

import java.time.Duration;
import java.time.LocalDateTime;

public interface GeneratorFunction {
    XLog invoke(int minTraceLength,
                int maxTraceLength,
                int numberOfTraces,
                int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                String declare,
                String alsFilename,
                int intervalSplits,
                boolean vacuity,
                boolean negativeTraces,
                boolean shuffleConstraints,
                LocalDateTime start,
                Duration duration,
                XTrace trace) throws Exception;
}
