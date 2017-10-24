package core.models;

/**
 * Created by Vasiliy on 2017-10-24.
 */
public class IntegerInterval  extends Interval {

    int min;
    int max;

    public IntegerInterval(int min, int max) {
        this.min = min;
        this.max = max;
    }

    @Override
    public String get(){
        return String.valueOf(rnd.nextInt()%(max-min)+min);
    }
}