package core;

import core.models.AlloyRunConfiguration;

import static core.models.AlloyRunConfiguration.ExecutionMode;

/**
 * Created by Vasiliy on 2018-03-22.
 */
public class CLI {
    public static AlloyRunConfiguration getConfigFromArgs(String[] args) {
        AlloyRunConfiguration config = new AlloyRunConfiguration();

        if (args.length > 4) {
            config.minLength = Integer.parseInt(args[0]);
            config.maxLength = Integer.parseInt(args[1]);
            config.modelFilename = args[3];
            config.logFilename = args[4];
            config.alsFilename = "temp.als";
            config.mode = ExecutionMode.GENERATION;

            boolean vacuity = false;
            boolean negativeTraces = false;

            for (int i = 5; i < args.length; ++i) {
                if (args[i].equals("-vacuity")) // or equalsIgnoreCase ?
                    vacuity = true;
                else if (args[i].equals("-negative"))
                    negativeTraces = true;
                else if (args[i].equals("-eld"))
                    config.evenLengthsDistribution = true;
                else if (args[i].equals("-shuffle"))
                    config.shuffleStatementsIterations = Integer.parseInt(getArg(args, ++i, "shuffle"));
                else if (args[i].equals("-is"))
                    config.intervalSplits = Integer.parseInt(getArg(args, ++i, "is"));
                else if (args[i].equals("-msi"))
                    config.maxSameInstances = Integer.parseInt(getArg(args, ++i, "msi"));
                else if (args[i].equals("-smv"))
                    config.saveSmv = true;
                else if (args[i].equals("-wait"))
                    config.waitInputBeforeExit = true;
                else if (args[i].equals("-underscore_spaces"))
                    config.underscore_spaces = true;
                else if (args[i].equals("-validatelog"))
                    config.mode = ExecutionMode.COMPLIANCE_CHECK;
                else if (args[i].equals("-query"))
                    config.mode = ExecutionMode.QUERY;
                else if (args[i].equals("-validatefn")) {
                    config.function = getArg(args, ++i, "validatefn");
                    config.mode = ExecutionMode.FUNCTION_VALIDATION;
                } else if (args[i].equals("-minsupport")) {
                    config.minSupport = Float.parseFloat(getArg(args, ++i, "minsupport"));
                } else if (args[i].equals("-filter")) {
                    config.queryFilterModel = getArg(args, ++i, "filter");
                }
                
                else throw new IllegalArgumentException("Unknown argument '" + args[i] + "'");
            }

            int n = Integer.parseInt(args[2]);
            if (negativeTraces)
                if (vacuity)
                    config.nNegativeVacuousTraces = n;
                else
                    config.nNegativeTraces = n;
            else if (vacuity)
                config.nVacuousTraces = n;
            else
                config.nPositiveTraces = n;

            return config;
        } else {
            System.out.println("\nusage: java -jar AlloyToLog.jar minLength maxLength NTraces input output " +
                    "[-vacuity] [-negative] [-eld] [-shuffle N] [-msi N]\n\n" +
                    "example use: java -jar AlloyToLog.jar 5 15 1000 model.decl log.xes -eld -shuffle 2\n\n\n" +
                    "\targuments:" +
                    "minLength - integer number, minimal length of trace\n\n" +
                    "maxLength - integer number, maximal length of trace\n\n" +
                    "NTraces - integer number, minimal length of trace\n\n" +
                    "input - name of input file (model); relative or absolute location\n\n" +
                    "output - name of output file (log)\n\n" +
                    "\toptional parameters:\n\n" +
                    "-vacuity - all constraints in the model will be activated at least once for each trace\n\n" +
                    "-negative - all trace will have at least one constraint violated\n\n" +
                    "-eld - length of traces between min and max will be evenly distributed between min and max " +
                    "(actual amount of traces might be lower with this option)\n\n" +
                    "-shuffle N - reorders constraints priority N times; might improve log quality when two or more " +
                    "constraints with opposite activation function present in a model. Value more than 1 will " +
                    "make generation process in N stages. 0 - no shuffle\n\n" +
                    "-msi N - max. same instances. Don't use\n\n" +
                    "-is N - interval splits count. >=1\n\n" +
                    "-smv - do not generate traces; save .smv code instead (for NuXMV-based generator)\n\n");
                    // query log for constrain templates: java -jar AlloyToLog.jar 0 0 0 queries.decl log.xes -query
            return null;
        }
    }

    private static String getArg(String[] args, int i, String name) {
        if (args.length <= i)
            throw new IndexOutOfBoundsException("Value for " + name + "required but not found");

        return args[i];
    }
}
