package core.helpers;

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
    public static int trace;

    public static void add(int a) {
        if (!lengthsMap.containsKey(a))
            lengthsMap.put(a, 0);
        lengthsMap.put(a, lengthsMap.get(a) + 1);
        lengths.add(a);
    }

    public static void print() {
        int total = 0;
        int traces = 0;
        for (Integer i : lengthsMap.keySet()) {
            System.out.println(i + ": " + lengthsMap.get(i));
            total+=i*lengthsMap.get(i);
            traces+=lengthsMap.get(i);
        }
        System.out.println(((double)total)/traces);
    }
}
