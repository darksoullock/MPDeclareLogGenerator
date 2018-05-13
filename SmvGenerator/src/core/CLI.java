package core;

/**
 * Created by Vasiliy on 2018-03-22.
 */
public class CLI {
    public static RunConfiguration getConfigFromArgs(String[] args) throws GenerationException {
        RunConfiguration config = new RunConfiguration();

        if (args.length > 4) {
            config.minLength = Integer.parseInt(args[0]);
            config.maxLength = Integer.parseInt(args[1]);
            config.inFilename = args[3];
            config.outFilename = args[4];

            for (int i = 5; i < args.length; ++i) {
                if (args[i].equals("-vacuity")) // or equalsIgnoreCase ?
                    config.vacuity = true;
                else if (args[i].equals("-negative"))
                    config.negativeTraces = true;
                else throw new IllegalArgumentException("Unknown argument '" + args[i] + "'");
            }

            return config;
        } else {
            System.out.println("\nusage: java -jar AlloyToLog.jar minLength maxLength NTraces input output " +
                    "[-vacuity] [-negative]\n\n" +
                    "example use: java -jar AlloyToLog.jar 5 15 1000 model.decl out.smv -vacuity\n\n\n" +
                    "\targuments:" +
                    "minLength - integer number, minimal length of trace\n\n" +
                    "maxLength - integer number, maximal length of trace\n\n" +
                    "NTraces - integer number, minimal length of trace\n\n" +
                    "input - name of input file (model); relative or absolute location\n\n" +
                    "output - name of output file (smv)\n\n" +
                    "\toptional parameters:\n\n" +
                    "-vacuity - all constraints in the model will be activated at least once for each trace\n\n" +
                    "-negative - all trace will have at least one constraint violated\n\n");

            return null;
        }
    }

    private static String getArg(String[] args, int i, String name) {
        if (args.length <= i)
            throw new IndexOutOfBoundsException("Value for " + name + "required but not found");

        return args[i];
    }
}
