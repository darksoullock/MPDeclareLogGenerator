package core;

import java.util.HashSet;
import java.util.Set;
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
    public static boolean encodeNames = !true;  // set to false only if you want to debug intermediate .als
    public static boolean noExtensions = true;  // disable xml extensions in .xes file (log attributes)
    public static boolean rawAlloyAllowed = true; // should be false

    public static Consumer<String> log = System.out::println;

    public static Set<String> getSupportedConstraints() {
        Set<String> supported = new HashSet<>();
        supported.add("Init");
        supported.add("Existence");
        supported.add("Existence");
        supported.add("Absence");
        supported.add("Absence");
        supported.add("Exactly");
        supported.add("Choice");
        supported.add("ExclusiveChoice");
        supported.add("RespondedExistence");
        supported.add("Response");
        supported.add("AlternateResponse");
        supported.add("ChainResponse");
        supported.add("Precedence");
        supported.add("AlternatePrecedence");
        supported.add("ChainPrecedence");
        supported.add("NotRespondedExistence");
        supported.add("NotResponse");
        supported.add("NotPrecedence");
        supported.add("NotChainResponse");
        supported.add("NotChainPrecedence");
        return supported;
    }
}
