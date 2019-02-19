package core.helpers;

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
        return "x" + UUID.randomUUID().toString().replace('-', 'x');
    }

    public static String getValidNameFor(String prefix, String name) {
        StringBuilder sb = new StringBuilder(prefix).append("_");
        for (int i = 0; i < name.length(); ++i) {
            char currentChar = name.charAt(i);
            if (Character.isLetterOrDigit(currentChar)) {
                sb.append(currentChar);
            }
        }

        sb.append("_r").append(++start);
        return sb.toString();
    }
}
