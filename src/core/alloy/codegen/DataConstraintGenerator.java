package core.alloy.codegen;

import core.Exceptions.DeclareParserException;
import core.Global;
import core.models.declare.DataConstraint;
import core.models.declare.data.NumericData;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Created by Vasiliy on 2017-10-23.
 */
public class DataConstraintGenerator {

    boolean vacuity;
    Map<String, NumericData> map;
    StringBuilder alloy;
    FunctionGenerator fnGen;
    Set<String> supported = Global.getAlloySupportedConstraints();
    List<String> alloyConstraints;

    public DataConstraintGenerator(int maxSameInstances, int bitwidth, boolean vacuity) {
        this.vacuity = vacuity;
        this.fnGen = new FunctionGenerator(maxSameInstances, bitwidth);
    }

    public String Generate(DataConstraint c, String name, Map<String, NumericData> map, List<String> alloyConstraints)
            throws DeclareParserException {
        this.map = map;
        this.alloy = new StringBuilder();
        this.alloyConstraints = alloyConstraints;

        if (!supported.contains(c.getName()))
            throw new DeclareParserException("Constraint '" + c.getName() + "' is not supported. Supported constraints are: " +
                    String.join(", ", supported));

        if (c.getName().equals("Init"))
            addInitDataConstraint(c, name);

        if (c.getName().equals("Absence")) {
            if (c.isBinary())
                addAbsenceDataConstraint(c, name, Integer.parseInt(c.taskB()));
            else
                addAbsenceDataConstraint(c, name);
        }

        if (c.getName().equals("Existence")) {
            if (c.isBinary())
                addExistenceDataConstraint(c, name, Integer.parseInt(c.taskB()));
            else
                addExistenceDataConstraint(c, name);
        }

        if (c.getName().equals("Exactly"))
            addExactlyDataConstraint(c, name, Integer.parseInt(c.taskB()));

        if (c.getName().equals("RespondedExistence"))
            addRespondedExistenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("Response"))
            addResponseDataConstraint(c, name, name + "c");

        if (c.getName().equals("AlternateResponse"))
            addAlternateResponseDataConstraint(c, name, name + "c");

        if (c.getName().equals("ChainResponse"))
            addChainResponseDataConstraint(c, name, name + "c");

        if (c.getName().equals("Precedence"))
            addPrecedenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("AlternatePrecedence"))
            addAlternatePrecedenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("ChainPrecedence"))
            addChainPrecedenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("NotRespondedExistence"))
            addNotRespondedExistenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("NotResponse"))
            addNotResponseDataConstraint(c, name, name + "c");

        if (c.getName().equals("NotPrecedence"))
            addNotPrecedenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("NotChainResponse"))
            addNotChainResponseDataConstraint(c, name, name + "c");

        if (c.getName().equals("NotChainPrecedence"))
            addNotChainPrecedenceDataConstraint(c, name, name + "c");

        if (c.getName().equals("Choice"))
            addChoiceDataConstraint(c, name, name + "a");

        if (c.getName().equals("ExclusiveChoice"))
            addExclusiveChoiceDataConstraint(c, name, name + "a");

        if (vacuity && c.supportsVacuity()) {
            alloy.append("fact { some te: Event | te.task = ").append(c.taskA()).append(" and ").append(name).append("[te]} //vc\n");
        }

        return alloy.toString();
    }

    private void addInitDataConstraint(DataConstraint one, String name) throws DeclareParserException {
        alloyConstraints.add(String.format("%s = TE0.task and  %s[TE0]", one.taskA(), name));
        alloy.append(fnGen.generateFunction(name, one.getFirstFunction(), map, one.getArgs()));
    }

    private void addExistenceDataConstraint(DataConstraint one, String fnName) throws DeclareParserException {
        alloyConstraints.add(String.format("some te: Event | te.task = %s and %s[te]", one.taskA(), fnName));
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map, one.getArgs()));
    }

    private void addExistenceDataConstraint(DataConstraint one, String fnName, int n) throws DeclareParserException {
        alloyConstraints.add(String.format("#{ te: Event | %s  = te.task and %s[te]} >= %d", one.taskA(), fnName, n));
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map, one.getArgs()));
    }

    private void addAbsenceDataConstraint(DataConstraint one, String fnName) throws DeclareParserException {
        alloyConstraints.add(String.format("no te: Event | te.task = %s and %s[te]", one.taskA(), fnName));
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map, one.getArgs()));
    }

    private void addAbsenceDataConstraint(DataConstraint one, String fnName, int n) throws DeclareParserException {
        alloyConstraints.add(String.format("#{ te: Event | te.task = %s and %s[te]} <= %d", one.taskA(), fnName, n));
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map, one.getArgs()));
    }

    private void addExactlyDataConstraint(DataConstraint one, String fnName, int n) throws DeclareParserException {
        alloyConstraints.add(String.format("#{ te: Event | te.task = %s and %s[te]} = %d", one.taskA(), fnName, n));
        alloy.append(fnGen.generateFunction(fnName, one.getFirstFunction(), map, one.getArgs()));
    }

    private void addRespondedExistenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(
                String.format("%s(some ote: Event | %s = ote.task and %s[te, ote])",
                        getActivation(one, fFnName),
                        one.taskB(),
                        sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(some fte: Event | %s = fte.task and %s[te, fte] and After[te, fte])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addAlternateResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(some fte: Event | %s = fte.task and %s[te, fte] and After[te, fte] and " +
                        "(no ite: Event | %s = ite.task and %s[ite] and  After[te, ite] and After[ite, fte]))",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName,
                one.taskA(),
                fFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addChainResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(some fte: Event | %s = fte.task and Next[te, fte] and %s[te, fte])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(some fte: Event | %s = fte.task and %s[te, fte] and After[fte, te])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addAlternatePrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(some fte: Event | %s = fte.task and %s[te, fte] and After[fte, te] and " +
                        "(no ite: Event | %s = ite.task and %s[ite] and After[fte, ite] and After[ite, te]))",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName,
                one.taskA(),
                fFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addChainPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(some fte: Event | %s = fte.task and Next[fte, te] and %s[te, fte])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addNotRespondedExistenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(no ote: Event | %s = ote.task and %s[te, ote])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateNotFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addNotResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(no fte: Event | %s = fte.task and %s[te, fte] and After[te, fte])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateNotFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addNotChainResponseDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        String a = getActivation(one, fFnName);
        alloyConstraints.add(String.format("(%s(no fte: Event | %s = fte.task and Next[te, fte] and %s[te, fte])) and " +
                        "(%s(no fte: Event | DummyActivity = fte.task and Next[te, fte]))",
                a,
                one.taskB(),
                sFnName,
                a));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateNotFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addNotPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("%s(no fte: Event | %s = fte.task and %s[te, fte] and After[fte, te])",
                getActivation(one, fFnName),
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateNotFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addNotChainPrecedenceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        String a = getActivation(one, fFnName);
        alloyConstraints.add(String.format("(%s(no fte: Event | %s = fte.task and Next[fte, te] and %s[te, fte])) and " +
                        "(%s(no fte: Event | DummyActivity = fte.task and Next[fte, te]))",
                a,
                one.taskB(),
                sFnName,
                a));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateNotFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addChoiceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("some te: Event | te.task = %s and %s[te] or te.task = %s and %s[te, te]",
                one.taskA(),
                fFnName,
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private void addExclusiveChoiceDataConstraint(DataConstraint one, String fFnName, String sFnName) throws DeclareParserException {
        alloyConstraints.add(String.format("(some te: Event | te.task = %s and %s[te] or te.task = %s and %s[te, te]) and " +
                        "((no te: Event | %s = te.task and %s[te]) or (no te: Event | %s = te.task and %s[te, te]))",
                one.taskA(),
                fFnName,
                one.taskB(),
                sFnName,
                one.taskA(),
                fFnName,
                one.taskB(),
                sFnName));
        alloy.append(fnGen.generateFunction(fFnName, one.getFirstFunction(), map, one.getArgs()));
        alloy.append(fnGen.generateFunction(sFnName, one.getSecondFunction(), map, one.getArgs()));
    }

    private String getActivation(DataConstraint one, String fFnName) {
        return String.format("all te: Event | (%s = te.task and %s[te]) implies ", one.taskA(), fFnName);
    }
}
