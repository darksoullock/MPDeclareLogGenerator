package core;

import declare.DeclareModel;
import declare.DeclareParser;
import declare.DeclareParserException;

import java.io.IOException;

public class Evaluator {

    private static RunConfiguration debugConf() {
        RunConfiguration conf = new RunConfiguration();
        conf.minLength = 10;
        conf.maxLength = 10;
        //conf.nNegativeVacuousTraces = 10;
        conf.inFilename = "./../data/bt_nodata.decl";
        //conf.inFilename = "./../data/loanApplication.decl";
        conf.outFilename = "./../data/testSMV";
        return conf;
    }

    public static void main(String[] args) throws DeclareParserException, GenerationException, IOException {
        RunConfiguration config;
        //config = debugConf();
        config = CLI.getConfigFromArgs(args);

        if (config == null)
            return;

        saveSmv(config);
    }

    private static void saveSmv(RunConfiguration config) throws GenerationException, DeclareParserException, IOException {
        DeclareModel model = new DeclareParser().Parse(IOHelper.readAllText(config.inFilename));
        SmvCodeGenerator gen = new SmvCodeGenerator();
        gen.run(model, config);
        IOHelper.writeAllText(config.outFilename, gen.getSmv());
        IOHelper.writeAllText(config.outFilename + ".db.json", gen.getDataBindingJson());
    }
}
