package core;

/**
 * Created by Vasiliy on 2017-10-25.
 */
public class RandomHelper {
    static int start = 99999;
    public static int getNext(){
        return ++start;
    }
}
