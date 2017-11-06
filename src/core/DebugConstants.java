package core;

/**
 * Created by Vasiliy on 2017-11-03.
 */
public class DebugConstants implements  Constants {
    @Override
    public String getSamePrefix1() {
        return "Get";
    }

    @Override
    public String getSamePrefix2() {
        return "Set";
    }

    @Override
    public String getDifferentPrefix() {
        return "Dif";
    }
}
