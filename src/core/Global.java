package core;

import java.util.function.Consumer;

/**
 * Created by Vasiliy on 2017-11-03.
 */
public class Global {
    public static String samePrefix = "Same";

    public static String differentPrefix = "Diff";

    /*
    when true it work faster,
    but then 'same' for numbers will prefer numbers
    from the intervals 'EqualToN' in most cases.
    not recommended for short logs.
     */
    public static boolean singleFirstForSame = false;
    public static boolean deepNamingCheck = false;  // increase execution time by ~1s. but can show errors
    public static boolean encodeNames = true;  // set to false only if you want to debug intermediate .als

    public static Consumer<String> log = System.out::println;
}
