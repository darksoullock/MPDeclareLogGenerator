package core.alloy.integration;


import core.Global;
import edu.mit.csail.sdg.alloy4.A4Reporter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4.ErrorWarning;
import edu.mit.csail.sdg.alloy4compiler.ast.Command;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.parser.CompUtil;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Options.SatSolver;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.TranslateAlloyToKodkod;

public class AlloyComponent {
    private A4Options config;
    private A4Reporter reporter;
    private Module world;

    public Module parse(String filename) throws Err {
        this.config = new A4Options();
        this.config.solver = SatSolver.SAT4J; // use for windows
        //this.config.solver = SatSolver.MiniSatJNI; // use for linux

//        Global.log.accept("Chosen solver: " + this.config.solver);
        this.config.skolemDepth = 4;
        this.config.noOverflow = true;
        this.reporter = new A4Reporter() {
            public void warning(ErrorWarning msg) {
                System.out.print("Relevance Warning:\n" + msg.toString().trim() + "\n\n");
                System.out.flush();
            }
        };

        return this.world = CompUtil.parseEverything_fromFile(this.reporter, null, filename);
    }

    public A4Solution executeFromFile(int maxTraceLength, int bitwidth) throws Err {
        if (world.getAllCommands().size() != 1)
            Global.log.accept("Should be only one command");

        Sig scopeChange = getSignature("this/Event", world);
        Command c = this.world.getAllCommands().get(0);
        Command newCommand = changeBitwidth(bitwidth, c.change(scopeChange, false, maxTraceLength));
//        Global.log.accept("Bitwidth: " + newCommand.bitwidth);
        return TranslateAlloyToKodkod.execute_command(this.reporter, this.world.getAllReachableSigs(), newCommand, config);
    }

    private Command changeBitwidth(int bitwidth, Command command) {
        return new Command(
                command.pos,
                command.label,
                command.check,
                command.overall,
                bitwidth,
                command.maxseq,
                command.expects,
                command.scope,
                command.additionalExactScopes,
                command.formula,
                command.parent);
    }

    private static Sig getSignature(String label, Module module) {
        return module.getAllReachableSigs().stream().filter(i -> i.label.equals(label)).findFirst().get();    // should fail here if signature not present
    }
}
