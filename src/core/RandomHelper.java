package core;

import java.util.UUID;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class RandomHelper {
    static int start = 99999;

    public static int getNext() {
        return ++start;
    }

    public static String getName() {
        return "x" + UUID.randomUUID().toString().replace('-','x');
    }
}
