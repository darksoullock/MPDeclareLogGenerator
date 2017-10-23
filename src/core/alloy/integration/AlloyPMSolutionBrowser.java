package core.alloy.integration;


import core.models.serialization.Payload;
import core.models.serialization.TaskEventAdapter;
import edu.mit.csail.sdg.alloy4.Err;
import edu.mit.csail.sdg.alloy4compiler.ast.Expr;
import edu.mit.csail.sdg.alloy4compiler.ast.Module;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig;
import edu.mit.csail.sdg.alloy4compiler.ast.Sig.PrimSig;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Solution;
import edu.mit.csail.sdg.alloy4compiler.translator.A4Tuple;
import edu.mit.csail.sdg.alloy4compiler.translator.A4TupleSet;
import edu.mit.csail.sdg.alloy4whole.Helper;
import sun.plugin.dom.exception.InvalidStateException;

import java.io.IOException;
import java.lang.reflect.Field;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;
import java.util.logging.Logger;

public class AlloyPMSolutionBrowser {
    private static Logger logger = Logger.getLogger("AlloySolutionBrowser");
    private Module module;
    private A4Solution solution;
    private Map<String, PrimSig> atomToSig;
    private int length;

    public AlloyPMSolutionBrowser(A4Solution solution, Module module, int length) {
        this.solution = solution;
        this.module = module;
        this.length = length;

        try {
            this.atomToSig = Helper.atom2sig(solution);
        } catch (Err err) {
            logger.log(Level.SEVERE, err.getMessage());
        }
    }

    public Sig atom2Sig(String atom) {
        return atomToSig.get(atom);
    }

    public List<TaskEventAdapter> orderPEvents() throws Err, IOException {
        TaskEventAdapter[] orderedPEvents = new TaskEventAdapter[length];
        int max = (int) Math.pow(2.0D, (double) this.solution.getBitwidth()) / 2;
        for (int i = 0; i < length; ++i) {
            int pos = (i - max);
            Expr taskExpr = exprFromString("getHTEventAtPos[" + pos + "].task");
            String name = retrieveAtomValue(taskExpr);
            List<Payload> payload = retrievePayload(pos);
            orderedPEvents[i] = new TaskEventAdapter(i, name, payload);
        }

        return Arrays.asList(orderedPEvents);
    }

    private List<Payload> retrievePayload(int originalEventPos) throws Err, IOException {
        Expr payloadExpr = exprFromString("(getHTEventAtPos[" + originalEventPos + "].data)");
        ArrayList<Payload> result = new ArrayList<>();
        for (A4Tuple t : ((A4TupleSet) solution.eval(payloadExpr))) {
            String name = getParentSignature(t.atom(0)).label;
            String value = atom2Sig(t.atom(0)).label;
            result.add(new Payload(name, value));
        }

        if (result.stream().map(i -> i.getName()).distinct().count() != result.size())
            throw new AssertionError("Two payloads with the same name present in activity. Check alloy model");

        return result;
    }

    private Sig getParentSignature(String atom) {
        try {
            Field parentField = PrimSig.class.getField("parent");
            parentField.setAccessible(true);
            return (Sig) parentField.get(atom2Sig(atom));
        } catch (NoSuchFieldException e) {
            System.out.println("No 'parent' field found. It worked on alloy 4.2. Check alloy encoding for payloads");
            e.printStackTrace();
        } catch (IllegalAccessException e) {
            System.out.println("Is 'parentField.setAccessible(true);' still there?");
            e.printStackTrace();
        }

        throw new Error();  // fail here; return null would cause other error later;
    }

    private String retrieveAtomValue(Expr exprToTupleSet) throws Err {
        for (A4Tuple t : (A4TupleSet) solution.eval(exprToTupleSet)) {
            return atom2Sig(t.atom(0)).label;
        }

        throw new InvalidStateException("No value present for a given expression");
    }

    public Expr exprFromString(String stringExpr) throws IOException, Err {
        return module.parseOneExpressionFromString(stringExpr);
    }
}