package core.SMV;

import core.Exceptions.DeclareParserException;
import core.Exceptions.GenerationException;
import core.Global;
import core.models.declare.Constraint;
import core.models.declare.DataConstraint;

import java.util.List;
import java.util.Set;

/**
 * Created by Vasiliy on 2018-03-26.
 */
public class LtlGen {

    StringBuilder smv;
    DataConstraintGenerator dcGen = new DataConstraintGenerator();

    public LtlGen(StringBuilder smv) {
        this.smv = smv;
    }

    public void generateConstraints(List<Constraint> constraints) throws DeclareParserException, GenerationException {
        // All LTL constraints are negated, because model checker gives counterexamples
        // G (state != _tail) -- eventually end of trace
        // F (state = _tail & X state != _tail) -- nothing happens after the end
        // F (length < minlength & state = _tail) -- no end until minimum length is reached
        smv.append("LTLSPEC G (state != _tail) | F (state = _tail & X state != _tail) | F (length<minlength & state = _tail) | ");

        Set<String> supported = Global.getAlloySupportedConstraints();
        for (Constraint i : constraints) {
            if (!supported.contains(i.getName()))
                throw new DeclareParserException("at line " + i.getStatement().getLine() + ":\nConstraint '" + i.getName() +
                        "' is not supported by SMV. \nSupported constraints are: " + String.join(", ", supported));

            generateLtlFor(i);
        }

        smv.append("FALSE");
    }

    public void generateLtlFor(Constraint c) throws DeclareParserException, GenerationException {
        validateConstraint(c);
        switch (c.getName()) {
            case "Init":
                generateInit(c);
                break;
            case "Existence":
                generateExistence(c);
                break;
            case "Absence":
                generateAbsence(c);
                break;
            case "Exactly":
                generateExactly(c);
                break;
            case "RespondedExistence":
                generateRespondedExistence(c);
                break;
            case "Response":
                generateResponse(c);
                break;
            case "AlternateResponse":
                generateAlternateResponse(c);
                break;
            case "ChainResponse":
                generateChainResponse(c);
                break;
            case "Precedence":
                generatePrecedence(c);
                break;
            case "AlternatePrecedence":
                generateAlternatePrecedence(c);
                break;
            case "ChainPrecedence":
                generateChainPrecedence(c);
                break;
            case "NotRespondedExistence":
                generateNotRespondedExistence(c);
                break;
            case "NotResponse":
                generateNotResponse(c);
                break;
            case "NotPrecedence":
                generateNotPrecedence(c);
                break;
            case "NotChainResponse":
                generateNotChainResponse(c);
                break;
            case "NotChainPrecedence":
                generateNotChainPrecedence(c);
                break;
            case "Choice":
                generateChoice(c);
                break;
            case "ExclusiveChoice":
                generateExclusiveChoice(c);
                break;
            default:
                throw new DeclareParserException("Constraint '" + c.getName() + "' is not supported in SMV.");
        }

    }

    private void validateConstraint(Constraint c) {

    }

    private void generateInit(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);

        smv.append("(first -> state != ").append(taskA).append(") | ");
    }

    private void generateExistence(Constraint c) throws GenerationException {
        int n = c.isBinary() ? Integer.parseInt(c.taskB()) : 1;
        if (n < 1)
            throw new GenerationException("Existence of " + n + " unsupported. N should be >=1");

        String taskA = attachADataC(c);

        smv.append("!( F (state = ").append(taskA);
        for (int i = 1; i < n; ++i)
            smv.append(" & (X F state = ").append(taskA);

        for (int i = 0; i < n; ++i)
            smv.append(')');

        smv.append(") | ");
    }

    private void generateAbsence(Constraint c) throws GenerationException {
        int n = c.isBinary() ? Integer.parseInt(c.taskB()) : 0;
        if (n < 0)
            throw new GenerationException("Absence of " + n + " unsupported. N should be >=0");

        String taskA = attachADataC(c);
        smv.append("( F (state = ").append(taskA);
        for (int i = 1; i <= n; ++i)
            smv.append(" & (X F state = ").append(taskA);

        for (int i = 0; i <= n; ++i)
            smv.append(')');

        smv.append(") | ");
    }

    private void generateExactly(Constraint c) throws GenerationException {
        generateExistence(c);
        generateAbsence(c);
    }

    private void generateRespondedExistence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("((F state = ").append(taskA).append(") & (!F state = ").append(taskB).append("))");
        smv.append(" | ");
    }
    
    private void generateResponse(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskA).append(" -> X F state = ").append(taskB).append(")");
        smv.append(" | ");
    }


    private void generateAlternateResponse(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskA)
                .append(" -> X(state != ").append(taskA)
                .append(" U state = ").append(taskB).append("))");
        smv.append(" | ");
    }

    private void generateChainResponse(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskA).append(" -> X state = ").append(taskB).append(")");
        smv.append(" | ");
    }


    private void generatePrecedence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("(state=").append(taskA).append(" V state!=").append(taskB).append(")");
        smv.append(" | ");
    }

    private void generateAlternatePrecedence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskA)
                .append(" -> (X(state != ").append(taskA)
                .append(" U state = ").append(taskB)
                .append("))) | (state=").append(taskA)
                .append(" V state!=").append(taskB).append(")");
        smv.append(" | ");
    }

    private void generateChainPrecedence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G(X state = ").append(taskB).append(" -> state = ").append(taskA).append(")");
        smv.append(" | ");
    }


    private void generateNotRespondedExistence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("((F state = ").append(taskA).append(") & (F state = ").append(taskB).append("))");
        smv.append(" | ");
    }

    private void generateNotResponse(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskA).append(" -> X !F state = ").append(taskB).append(")");
        smv.append(" | ");
    }

    private void generateNotPrecedence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskB).append(" -> X !F state = ").append(taskA).append(")");
        smv.append(" | ");
    }

    private void generateNotChainResponse(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskA).append(" -> X state != ").append(taskB).append(")");
        smv.append(" | ");
    }

    private void generateNotChainPrecedence(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("!G (state = ").append(taskB).append(" -> X state != ").append(taskA).append(")");
        smv.append(" | ");
    }

    private void generateChoice(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("((!F state = ").append(taskA).append(") & (!F state = ").append(taskB).append("))");
        smv.append(" | ");
    }

    private void generateExclusiveChoice(Constraint c) throws GenerationException {
        String taskA = attachADataC(c);
        String taskB = attachBDataC(c);
        smv.append("((!F state = ").append(taskA)
                .append(") & (!F state = ").append(taskB)
                .append(") | (F state = ").append(taskA)
                .append(") & (F state = ").append(taskB).append("))");
        smv.append(" | ");
    }

    private String attachADataC(Constraint c) throws GenerationException {
        String task = c.taskA();
        if (c instanceof DataConstraint) {
            task = task + dcGen.getLtl(((DataConstraint) c).getFirstFunction());
        }
        return task;
    }

    private String attachBDataC(Constraint c) throws GenerationException {
        String task = c.taskB();
        if (c instanceof DataConstraint) {
            task = task + dcGen.getLtl(((DataConstraint) c).getSecondFunction());
        }
        return task;
    }
}
