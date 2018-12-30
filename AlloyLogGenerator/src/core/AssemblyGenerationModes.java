package core;

import core.helpers.StatisticsHelper;
import core.interfaces.Function2;
import core.interfaces.Function3;
import core.interfaces.GeneratorFunction;
import org.deckfour.xes.model.XLog;
import org.deckfour.xes.model.impl.XAttributeMapImpl;
import org.deckfour.xes.model.impl.XLogImpl;

import java.time.Duration;
import java.time.LocalDateTime;

// some options (e.g. fair trace length distribution) require to run generator multiple times
// this class controls this process (of running actual generator) and to assemble log from one or many generation iterations
public class AssemblyGenerationModes {

    public static XLog getLog(int minTraceLength,
                              int maxTraceLength,
                              int numberOfPositiveTracesWithoutVacuity,
                              int numberOfPositiveTracesWithVacuity,
                              int numberOfNegativeTracesWithoutVacuity,
                              int numberOfNegativeTracesWithVacuity,
                              int shuffleConstraintsIterations, // If some constraints are rarely activated, different order (different priority) may fix this problem. value 0 means that order is as it is in input .decl file
                              boolean evenLengthsDistribution,
                              int maxSameInstances, // higher values of this parameter can have significant performance impact for some models. Keep it 1 unless you use same/different constraints for numbers. Otherwise recommended to increment by 1
                              int intervalSplits,
                              String declare,
                              String alsFilename,
                              LocalDateTime start,
                              Duration duration,
                              GeneratorFunction getLogSingleRun)
            throws Exception {

        Function3<Boolean, Boolean, Integer, XLog> getLogNow;

        if (evenLengthsDistribution)
            getLogNow =
                    (vacuity2, negative, nTraces) -> getLogEvenTraceLengthDistribution(
                            minTraceLength,
                            maxTraceLength,
                            nTraces,
                            (length, amount) -> getLogFairConstraintsPriority(
                                    amount,
                                    shuffleConstraintsIterations,
                                    (amount2, shuffle) -> getLogSingleRun.invoke(
                                            length,
                                            length,
                                            amount2,
                                            maxSameInstances,
                                            declare,
                                            alsFilename,
                                            intervalSplits,
                                            vacuity2,
                                            negative,
                                            shuffle,
                                            start,
                                            duration,
                                            null)));
        else
            getLogNow =
                    (vacuity2, negative, nTraces) -> getLogFairConstraintsPriority(
                            nTraces,
                            shuffleConstraintsIterations,
                            (amount2, shuffle) -> getLogSingleRun.invoke(
                                    minTraceLength,
                                    maxTraceLength,
                                    amount2,
                                    maxSameInstances,
                                    declare,
                                    alsFilename,
                                    intervalSplits,
                                    vacuity2,
                                    negative,
                                    shuffle,
                                    start,
                                    duration,
                                    null));

        XLog log = createEmptyLog();
        log.addAll(getLogNow.invoke(false, false, numberOfPositiveTracesWithoutVacuity));
        log.addAll(getLogNow.invoke(true, false, numberOfPositiveTracesWithVacuity));
        log.addAll(getLogNow.invoke(false, true, numberOfNegativeTracesWithoutVacuity));
        log.addAll(getLogNow.invoke(true, true, numberOfNegativeTracesWithVacuity));
        return log;
    }

    public static XLog getLogEvenTraceLengthDistribution(int minTraceLength,
                                                         int maxTraceLength,
                                                         int numberOfTraces,
                                                         Function2<Integer, Integer, XLog> getLogForN)
            throws Exception {
        int n = numberOfTraces / (maxTraceLength - minTraceLength + 1);
        XLog log = getLogForN.invoke(maxTraceLength, n);
        StatisticsHelper.time.add(System.nanoTime());
        for (int i = minTraceLength; i < maxTraceLength; ++i) {
            Global.log.accept("\ngeneration for length " + i);
            XLog log2 = getLogForN.invoke(i, n);
            log.addAll(log2);
        }

        return log;
    }

    public static XLog getLogFairConstraintsPriority(
            int numberOfTraces,
            int shuffleConstraintsIterations,
            Function2<Integer, Boolean, XLog> getLog) // int N, bool shuffle
            throws Exception {

        if (numberOfTraces == 0)
            return createEmptyLog();

        int n = numberOfTraces;
        if (shuffleConstraintsIterations > 0)
            n /= shuffleConstraintsIterations;

        XLog log = getLog.invoke(n, shuffleConstraintsIterations > 0);
        for (int i = 1; i < shuffleConstraintsIterations; ++i) {
            Global.log.accept("\ngeneration step " + i);
            XLog log2 = getLog.invoke(n, true);
            log.addAll(log2);
        }

        return log;
    }

    private static XLog createEmptyLog() {
        return new XLogImpl(new XAttributeMapImpl());
    }
}
