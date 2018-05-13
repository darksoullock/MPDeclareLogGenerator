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
    public static List<Long> time = new ArrayList<>();

    public static void printTime() {
        for (Long i : time) {
            System.out.println(i / 1000);
        }
    }

    public static void addLength(int a) {
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
            total += i * lengthsMap.get(i);
            traces += lengthsMap.get(i);
        }
        System.out.println(((double) total) / traces);
    }

    static long start;
    static long end;
    static long total = 0;
    static int tc = 1;
    public static void starttime(){
        start = System.nanoTime();
    }
    public static void endtime(int x) {
        end = System.nanoTime();
        total+=(end - start);
        if (++tc%x == 0) {
            System.out.println(total/1000000);
            tc = 0;
            total = 0;
        }
    }
}
