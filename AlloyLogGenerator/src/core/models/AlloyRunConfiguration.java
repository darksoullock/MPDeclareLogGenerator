package core.models;

/**
 * Created by Vasiliy on 2018-03-22.
 */
public class AlloyRunConfiguration {

    public int intervalSplits = 1;

    public int minLength = 2;

    public int maxLength = 10;

    public int nPositiveTraces = 0;

    public int nNegativeTraces = 0;

    public int nVacuousTraces = 0;

    public int nNegativeVacuousTraces = 0;

    /*
    should be 1 if 'same' or 'different' constraints
    not used or used at most once for any task.
    should be <=N if 'same'/'different' constraint
    used more than once and solution not found (or found few)
     */
    public int maxSameInstances = 2;

    public int shuffleStatementsIterations = 0;

    public boolean evenLengthsDistribution = false;

    public String inFilename;

    public String alsFilename = "temp.als";

    public String outFilename = "out.xes";

    public boolean saveSmv = false;
}