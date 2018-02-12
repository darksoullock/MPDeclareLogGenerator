package core.alloy.codegen;

import core.Exceptions.DeclareParserException;
import core.Global;
import core.helpers.RandomHelper;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import core.models.declare.Activity;
import core.models.declare.Constraint;
import core.models.declare.DataConstraint;
import core.models.declare.Statement;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.NumericData;
import core.models.intervals.Interval;
import core.models.serialization.trace.AbstractTraceAttribute;

import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-16.
 */
public class AlloyCodeGenerator {
    int maxTraceLength;
    int minTraceLength;
    int bitwidth;
    boolean vacuity;

    StringBuilder alloy;
    List<String> alloyConstraints;

    List<AbstractTraceAttribute> traceAttributes;

    List<String> tasksCode;
    List<String> traceAttributesCode;
    List<String> dataCode;
    List<String> dataBindingsCode;
    List<Statement> constraintsCode;
    List<Statement> dataConstraintsCode;

    Map<String, NumericData> numericData;
    Map<String, List<DataExpression>> numericExpressions;

    DeclareParser parser;
    DataConstraintGenerator gen;

    public AlloyCodeGenerator(int maxTraceLength, int minTraceLength, int bitwidth, int maxSameInstances, int intervalSplits, boolean vacuity) {
        this.maxTraceLength = maxTraceLength;
        this.minTraceLength = minTraceLength;
        this.bitwidth = bitwidth;
        this.vacuity = vacuity;
        this.parser = new DeclareParser(intervalSplits);
        maxSameInstances = (int) Math.min(maxSameInstances, Math.pow(2, bitwidth));
        this.gen = new DataConstraintGenerator(maxSameInstances, bitwidth, vacuity);
    }

    public void Run(String declare, boolean negativeTraces) throws DeclareParserException {
        Init();
        if (Global.encodeNames)
            declare = parser.encodeNames(declare);
        GenerateEvents(maxTraceLength);
        GenerateNextPredicate(maxTraceLength);
        GenerateAfterPredicate(maxTraceLength);
        SortInput(parser.splitStatements(declare));
        List<Activity> tasks = parser.parseActivities(tasksCode);
        generateActivities(tasks);
        List<EnumeratedData> data = parser.parseData(dataCode, numericData);
        ParseAndGenerateDataBindings();
        List<Constraint> constraints = parseConstraints();
        generateConstraints(constraints);
        if (vacuity)
            generateVacuity(constraints);
        List<DataConstraint> dataConstraints = parser.parseDataConstraints(dataConstraintsCode, numericExpressions);
        ExtendNumericData();
        GenerateData(data);
        GenerateDataConstraints(dataConstraints);
        AttachConstraints(negativeTraces);
        traceAttributes = parser.parseTraceAttributes(traceAttributesCode);
    }

    private void AttachConstraints(boolean negativeTraces) {
        if (negativeTraces)
            alloy.append("fact {\n").append("(not ").append(String.join(") or not (", alloyConstraints)).append(")\n}\n");
        else
            alloy.append("fact {\n").append(String.join("\n", alloyConstraints)).append("\n}\n");
    }

    public String getAlloyCode() {
        if (alloy != null)
            return alloy.toString();
        return null;
    }

    public List<AbstractTraceAttribute> getTraceAttr() {
        return traceAttributes;
    }

    public Map<String, Interval> generateNumericMap() {
        Map<String, Interval> map = new HashMap<>();
        for (NumericData ed : numericData.values())
            for (String i : ed.getMapping().keySet())
                map.put(i, ed.getMapping().get(i));

        return map;
    }

    private void Init() {
        tasksCode = new ArrayList<>();
        traceAttributesCode = new ArrayList<>();
        dataCode = new ArrayList<>();
        dataBindingsCode = new ArrayList<>();
        constraintsCode = new ArrayList<>();
        dataConstraintsCode = new ArrayList<>();

        numericData = new HashMap<>();
        numericExpressions = new HashMap<>();

        alloy = new StringBuilder(GetBase());
        alloyConstraints = new ArrayList<>();
        //IOHelper.writeAllText("./data/base.als", GetBase());
    }

    public Map<String, String> getNamesEncoding() {
        return parser.getNamesEncoding();
    }

    private void GenerateDataConstraints(List<DataConstraint> dataConstraints) throws DeclareParserException {
        for (DataConstraint i : dataConstraints) {
            try {
                alloy.append(gen.Generate(i, getRandomFunctionName(), numericData, alloyConstraints));
            } catch (DeclareParserException ex) {
                Global.log.accept("at line " + i.getStatement().getLine() + ":\n" + ex.getMessage());
                throw ex;
            } catch (IndexOutOfBoundsException ex) {
                Global.log.accept("Did you define variable for data constraint (e.g. Existence[Task A]|A.value>1 instead of Existence[Task]|A.value>1)");
                Global.log.accept("at line " + i.getStatement().getLine() + ":\n" + ex.getMessage());
                throw ex;
            }
        }
    }

    private List<Constraint> parseConstraints() {
        List<Constraint> constraints = new ArrayList<>();
        for (Statement s : constraintsCode) {
            String[] p = s.getCode().split("\\s*[\\[\\],]\\s*");
            constraints.add(new Constraint(p[0], Arrays.stream(p).skip(1).collect(Collectors.toList()), s));
        }

        return constraints;
    }

    private void generateConstraints(List<Constraint> constraints) throws DeclareParserException {
        Set<String> supported = Global.getSupportedConstraints();
        for (Constraint i : constraints) {
            if (!supported.contains(i.getName()))
                throw new DeclareParserException("at line " + i.getStatement().getLine() + ":\nConstraint '" + i.getName() +
                        "' is not supported. \nSupported constraints are: " + String.join(", ", supported) +
                        "\nIf the name in error different from the model source code, and part of it replaced with random sequence, " +
                        "then some of the short names you used might be part of keywords (like the name of constraint). " +
                        "Try to enclose such names in single quotes, 'like this'");

            if (i.isBinary())
                alloyConstraints.add(String.format("%s[%s,%s]", i.getName(), i.taskA(), i.taskB()));
            else
                alloyConstraints.add(String.format("%s[%s]", i.getName(), i.taskA()));
        }
    }


    private void generateVacuity(List<Constraint> constraints) {
        alloy.append("fact {\n");
        for (String i : constraints.stream().filter(x -> x.supportsVacuity()).map(x -> x.taskA()).distinct().collect(Collectors.toList()))
            alloy.append("Existence[").append(i).append("]\n");

        alloy.append("}\n");
    }

    private String getRandomFunctionName() {
        return "p" + RandomHelper.getNext();
    }

    private void ParseAndGenerateDataBindings() {
        Map<String, List<String>> taskToData = new HashMap<>();
        Map<String, List<String>> dataToActivity = new HashMap<>();

        for (String line : dataBindingsCode) {
            line = line.substring(5);
            List<String> data = Arrays.stream(line.split("[:,\\s]+")).filter(i -> !i.isEmpty()).collect(Collectors.toList());
            String task = data.get(0);
            if (!taskToData.containsKey(task))
                taskToData.put(task, new ArrayList<>());
            for (String i : data.stream().skip(1).collect(Collectors.toList())) {
                taskToData.get(task).add(i);
                if (!dataToActivity.containsKey(i))
                    dataToActivity.put(i, new ArrayList<>());
                dataToActivity.get(i).add(task);
            }
        }

        WriteDataBinding(taskToData, dataToActivity);
    }


    private void ExtendNumericData() throws DeclareParserException {
        for (NumericData d : numericData.values())
            if (numericExpressions.containsKey(d.getType()))
                for (DataExpression i : numericExpressions.get(d.getType()))
                    d.addValue(getNumberFromComparison((BinaryExpression) i));
    }

    private String getNumberFromComparison(BinaryExpression ex) throws DeclareParserException {
        if (ex.getLeft().getNode().getType() == Token.Type.Number)
            return ex.getLeft().getNode().getValue();

        if (ex.getRight().getNode().getType() == Token.Type.Number)
            return ex.getRight().getNode().getValue();

        throw new DeclareParserException("No number in comparison operator: " + ex.toString());
    }

    private void GenerateData(List<EnumeratedData> data) {
        for (EnumeratedData item : data) {
            if (item instanceof NumericData) {
                GenerateNumericDataItem((NumericData) item);
                continue;
            }
            alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {}\n");
            alloy.append("fact { all te: Event | (lone ").append(item.getType()).append(" & te.data)}\n");
            for (String value : item.getValues()) {
                alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}\n");
            }
        }
    }

    private void GenerateNumericDataItem(NumericData item) {
        alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {\namount: Int\n}\n");
        alloy.append("fact { all te: Event | (lone ").append(item.getType()).append(" & te.data) }\n");
        alloy.append("pred Single(pl: ").append(item.getType()).append(") {{pl.amount=1}}\n");
        alloy.append("fun Amount(pl: ").append(item.getType()).append("): one Int {{pl.amount}}\n");
        int limit = (int) Math.pow(2, bitwidth - 1);
        for (String value : item.getValues()) {
            int cnt = item.getMapping().get(value).getValueCount(limit);
            if (cnt < 0)
                cnt = limit - 1;
            alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}{amount=")
                    .append(cnt).append("}\n");
        }
    }

    private void generateActivities(List<Activity> tasks) {
        for (Activity i : tasks)
            alloy.append("one sig ").append(i.getName()).append(" extends Activity {}\n");
    }

    private void SortInput(String[] st) {
        int line = 0;
        for (String i : st) {
            ++line;

            if (i.isEmpty() || i.startsWith("/"))
                continue;

            if (parser.isActivity(i))
                tasksCode.add(i);

            if (parser.isTraceAttribute(i))
                traceAttributesCode.add(i);

            if (parser.isData(i))
                dataCode.add(i);

            if (parser.isDataBinding(i))
                dataBindingsCode.add(i);

            if (parser.isConstraint(i))
                constraintsCode.add(new Statement(i, line));

            if (parser.isDataConstraint(i))
                dataConstraintsCode.add(new Statement(i, line));
        }
    }

    private void GenerateEvents(int length) {
        for (int i = 0; i < length; i++) {
            if (i < minTraceLength)
                alloy.append("one sig TE").append(i).append(" extends Event {}{not task=DummyActivity}\n");
            else
                alloy.append("one sig TE").append(i).append(" extends Event {}\n");
        }
    }


    private void GenerateNextPredicate(int length) {
        alloy.append("pred Next(pre, next: Event){");
        alloy.append("pre=TE0 and next=TE1");
        for (int i = 2; i < length; i++) {
            alloy.append(" or pre=TE").append(i - 1).append(" and next=TE").append(i);
        }

        alloy.append("}\n");
    }

    private void GenerateAfterPredicate(int length) {
        alloy.append("pred After(b, a: Event){// b=before, a=after\n");
        int middle = length / 2;
        alloy.append("b=TE0 or a=TE").append(length - 1);
        for (int i = 1; i < length - 2; ++i) {
            alloy.append(" or b=TE").append(i).append(" and ");
            if (i < middle) {
                alloy.append("not (a=TE").append(0);
                for (int j = 1; j < i; ++j) {
                    alloy.append(" or a=TE").append(j);
                }
                alloy.append(")");
            } else {
                alloy.append("(a=TE").append(length - 1);
                for (int j = length - 2; j > i; --j) {
                    alloy.append(" or a=TE").append(j);
                }
                alloy.append(")");
            }
        }

        alloy.append("}\n");
    }

    private void WriteDataBinding(Map<String, List<String>> taskToData, Map<String, List<String>> dataToActivity) {
        for (String task : taskToData.keySet()) {
            alloy.append("fact { all te: Event | te.task = ")
                    .append(task)
                    .append(" implies (one ")
                    .append(String.join(" & te.data and one ", taskToData.get(task)))
                    .append(" & te.data")
                    .append(")}\n");
        }

        for (String payload : dataToActivity.keySet()) {
            alloy.append("fact { all te: Event | lone(").append(payload).append(" & te.data) }\n");
            alloy.append("fact { all te: Event | some (")
                    .append(payload)
                    .append(" & te.data) implies te.task in (")
                    .append(String.join(" + ", dataToActivity.get(payload)))
                    .append(") }\n");
        }
    }

    private String GetBase() {
        return "abstract sig Activity {}\n" +
                "abstract sig Payload {}\n" +
                "\n" +
                "abstract sig Event{\n" +
                "\ttask: one Activity,\n" +
                "\tdata: set Payload,\n" +
                "\ttokens: set Token\n" +
                "}\n" +
                "\n" +
                "one sig DummyPayload extends Payload {}\n" +
                "fact { no te:Event | DummyPayload in te.data }\n" +
                "\n" +
                "one sig DummyActivity extends Activity {}\n" +
                "\n" +
                "abstract sig Token {}\n" +
                "abstract sig SameToken extends Token {}\n" +
                "abstract sig DiffToken extends Token {}\n" +
                "lone sig DummySToken extends SameToken{}\n" +
                "lone sig DummyDToken extends DiffToken{}\n" +
                "fact { \n" +
                "\tno DummySToken\n" +
                "\tno DummyDToken\n" +
                "\tall te:Event| no (te.tokens & SameToken) or no (te.tokens & DiffToken)\n" +
                "}\n" +
                "\n" +
                "pred True[]{some TE0}\n" +
                "\n" +
                "// declare templates\n" +
                "\n" +
                "pred Init(taskA: Activity) { \n" +
                "\ttaskA = TE0.task\n" +
                "}\n" +
                "\n" +
                "pred Existence(taskA: Activity) { \n" +
                "\tsome te: Event | te.task = taskA\n" +
                "}\n" +
                "\n" +
                "pred Existence(taskA: Activity, n: Int) {\n" +
                "\t#{ te: Event | taskA = te.task } >= n\n" +
                "}\n" +
                "\n" +
                "pred Absence(taskA: Activity) { \n" +
                "\tno te: Event | te.task = taskA\n" +
                "}\n" +
                "\n" +
                "pred Absence(taskA: Activity, n: Int) {\n" +
                "\t#{ te: Event | taskA = te.task } <= n\n" +
                "}\n" +
                "\n" +
                "pred Exactly(taskA: Activity, n: Int) {\n" +
                "\t#{ te: Event | taskA = te.task } = n\n" +
                "}\n" +
                "\n" +
                "pred Choice(taskA, taskB: Activity) { \n" +
                "\tsome te: Event | te.task = taskA or te.task = taskB\n" +
                "}\n" +
                "\n" +
                "pred ExclusiveChoice(taskA, taskB: Activity) { \n" +
                "\tsome te: Event | te.task = taskA or te.task = taskB\n" +
                "\t(no te: Event | taskA = te.task) or (no te: Event | taskB = te.task )\n" +
                "}\n" +
                "\n" +
                "pred RespondedExistence(taskA, taskB: Activity) {\n" +
                "\t(some te: Event | taskA = te.task) implies (some ote: Event | taskB = ote.task)\n" +
                "}\n" +
                "\n" +
                "pred Response(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred AlternateResponse(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte] and (no ite: Event | taskA = ite.task and After[te, ite] and After[ite, fte]))\n" +
                "}\n" +
                "\n" +
                "pred ChainResponse(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred Precedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te])\n" +
                "}\n" +
                "\n" +
                "pred AlternatePrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te] and (no ite: Event | taskA = ite.task and After[fte, ite] and After[ite, te]))\n" +
                "}\n" +
                "\n" +
                "pred ChainPrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[fte, te])\n" +
                "}\n" +
                "\n" +
                "pred NotRespondedExistence(taskA, taskB: Activity) {\n" +
                "\t(some te: Event | taskA = te.task) implies (no te: Event | taskB = te.task)\n" +
                "}\n" +
                "\n" +
                "pred NotResponse(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred NotPrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[fte, te])\n" +
                "}\n" +
                "\n" +
                "pred NotChainResponse(taskA, taskB: Activity) { \n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred NotChainPrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[fte, te])\n" +
                "}\n" +
                "//-\n" +
                "\n" +
                "pred example { }\n" +
                "run example\n" +
                "\n---------------------- end of static code block ----------------------\n" +
                "\n--------------------- generated code starts here ---------------------\n\n";
        //return IOHelper.readAllText("./data/base.als");
    }
}
