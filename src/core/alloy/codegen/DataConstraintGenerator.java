package core.alloy.codegen;

import core.models.declare.DataConstraint;
import core.models.declare.data.NumericData;

import java.util.Map;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class DataConstraintGenerator {

    Map<String, NumericData> map;
    StringBuilder alloy;
    FunctionGenerator fnGen = new FunctionGenerator();

    public String Generate(DataConstraint c, String name, Map<String, NumericData> map) {
        this.map = map;
        this.alloy = new StringBuilder();

        if (c.getName().equals("Init"))
            addInitDataConstraint(c, name);

        if (c.getName().equals("Absence")) {
            if (c.getArgs().size() > 1)
                addAbsenceDataConstraint(c, name, Integer.parseInt(c.taskB()));
            else
                addAbsenceDataConstraint(c, name);
        }

        if (c.getName().equals("Existence")) {
            if (c.getArgs().size() > 1)
                addExistenceDataConstraint(c, name, Integer.parseInt(c.taskB()));
            else
                addExistenceDataConstraint(c, name);
        }

        if (c.getName().equals("Exactly"))
            addExactlyDataConstraint(c, name, Integer.parseInt(c.taskB()));

        if (c.getName().equals("RespondedExistence"))
            addRespondedExistenceDataConstraint(c, name, name+"c");

        if (c.getName().equals("Response"))
            addResponseDataConstraint(c, name, name+"c");

        if (c.getName().equals("AlternateResponse"))
            addAlternateResponseDataConstraint(c, name, name+"c");

        if (c.getName().equals("ChainResponse"))
            addChainResponseDataConstraint(c, name, name+"c");

        if (c.getName().equals("Precedence"))
            addPrecedenceDataConstraint(c, name, name+"c");

        if (c.getName().equals("AlternatePrecedence"))
            addAlternatePrecedenceDataConstraint(c, name, name+"c");

        if (c.getName().equals("ChainPrecedence"))
            addChainPrecedenceDataConstraint(c, name, name+"c");

        if (c.getName().equals("NotRespondedExistence"))
            addNotRespondedExistenceDataConstraint(c, name, name+"c");

        if (c.getName().equals("NotResponse"))
            addNotResponseDataConstraint(c, name, name+"c");

        if (c.getName().equals("NotPrecedence"))
            addNotPrecedenceDataConstraint(c, name, name+"c");

        if (c.getName().equals("NotChainResponse"))
            addNotChainResponseDataConstraint(c, name, name+"c");

        if (c.getName().equals("NotChainPrecedence"))
            addNotChainPrecedenceDataConstraint(c, name, name+"c");

        return alloy.toString();
    }

    private void addInitDataConstraint(DataConstraint one, String name) {
        alloy.append("fact { one te: TaskEvent | ").append(one.taskA()).append(" = te.task and te.pos = TE0.pos and ").append(name).append("[te.data] }\n");
        alloy.append(fnGen.generateFunction(name, one.getFirstFunction(), map));
    }

    private void addExistenceDataConstraint(DataConstraint one, String fnName) {
        alloy.append("fact { some te: TaskEvent | te.task = ").append(one.taskA()).append(" and ").append(fnName).append("[te.data]}\n");
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map));
    }

    private void addExistenceDataConstraint(DataConstraint one, String fnName, int n) {
        alloy.append("fact { #{ te: TaskEvent | ").append(one.taskA()).append(" in te.task and ").append(fnName).append("[te.data]").append("} >= ").append(n).append(" }\n");
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map));
    }

    private void addAbsenceDataConstraint(DataConstraint one, String fnName) {
        alloy.append("fact { no te: TaskEvent | te.task = ").append(one.taskA()).append(" and ").append(fnName).append("[te.data] }\n");
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map));
    }

    private void addAbsenceDataConstraint(DataConstraint one, String fnName, int n) {
        alloy.append("fact { #{ te: TaskEvent | ").append(one.taskA()).append(" in te.task and ").append(fnName).append("[te.data]").append("} <= ").append(n).append(" }\n");
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map));
    }

    private void addExactlyDataConstraint(DataConstraint one, String fnName, int n) {
        alloy.append("fact { #{ te: TaskEvent | ").append(one.taskA()).append(" in te.task and ").append(fnName).append("[te.data]").append("} = ").append(n).append(" }\n");
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map));
    }

    private void addRespondedExistenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ ote: TaskEvent | ").append(one.taskB()).append(" = ote.task and ").append(sFnName).append("[te.data, ote.data]").append("} > 0").append(" }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos > te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } > 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addAlternateResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos > te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] and #{ ite: TaskEvent | ite.pos > te.pos and ite.pos < fte.pos and ").append(one.taskA()).append(" = ite.task and ").append(fFnName).append("[ite.data]} = 0 } > 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addChainResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos = int[te.pos + 1] and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } > 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos < te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } > 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addAlternatePrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos < te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] and #{ ite: TaskEvent | ite.pos < te.pos and ite.pos > fte.pos and ").append(one.taskA()).append(" = ite.task and ").append(fFnName).append("[ite.data]} = 0 } > 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addChainPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | int[fte.pos + 1] = te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } > 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addNotRespondedExistenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ ote: TaskEvent | ").append(one.taskB()).append(" = ote.task and ").append(sFnName).append("[te.data, ote.data]").append("} = 0").append(" }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addNotResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos > te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } = 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addNotChainResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos = int[te.pos + 1] and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } = 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addNotPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | fte.pos < te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } = 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addNotChainPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) {
        addActivation(one, fFnName);
        alloy.append("#{ fte: TaskEvent | int[fte.pos + 1] = te.pos and ").append(one.taskB()).append(" = fte.task and ").append(sFnName).append("[te.data, fte.data] } = 0 }\n");
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map));
    }

    private void addActivation(DataConstraint one, String fFnName) {
        alloy.append("fact { all te: TaskEvent | (").append(one.taskA()).append(" = te.task and ").append(fFnName).append("[te.data]) implies ");
    }
}
