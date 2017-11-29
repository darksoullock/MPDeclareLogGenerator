package core;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-26.
 */
public class StatisticsHelper {
    static Map<Integer, Integer> lengthsMap = new HashMap<>();
    static List<Integer> lengths = new ArrayList<>();
    static Map<String, Integer> times = new HashMap<>();
    static int scnt = 0;
    static int st = 0;
    public static int trace;

    public static void add(int a) {
        if (!lengthsMap.containsKey(a))
            lengthsMap.put(a, 0);
        lengthsMap.put(a, lengthsMap.get(a) + 1);
        lengths.add(a);
    }

    public static void print() {
        for (Integer i : lengthsMap.keySet()) {
            System.out.println(i + ": " + lengthsMap.get(i));
        }
    }

    public static void executionTime(Runnable o) {
        o.run();
    }
}
