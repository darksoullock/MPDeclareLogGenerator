package core.alloy.codegen;

import core.Global;
import core.IOHelper;
import core.RandomHelper;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import core.models.declare.Constraint;
import core.models.declare.DataConstraint;
import core.models.declare.Task;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.NumericData;
import core.models.intervals.Interval;
import core.models.serialization.trace.AbstractTraceAttribute;
import sun.plugin.dom.exception.InvalidStateException;

import java.io.FileNotFoundException;
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

    List<AbstractTraceAttribute> traceAttributes;

    List<String> tasksCode;
    List<String> traceAttributesCode;
    List<String> dataCode;
    List<String> dataBindingsCode;
    List<String> constraintsCode;
    List<String> dataConstraintsCode;

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

    public void Run(String declare) throws FileNotFoundException {
        Init();
        if (Global.encodeNames)
            declare = parser.encodeNames(declare);
        GenerateTaskEvents(maxTraceLength);
        GenerateNextPredicate(maxTraceLength);
        GenerateAfterPredicate(maxTraceLength);
        GenerateVariableLengthConstraint(minTraceLength, maxTraceLength);
        SortInput(parser.splitStatements(declare));
        List<Task> tasks = parser.parseTasks(tasksCode);
        generateTasks(tasks);
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
        traceAttributes = parser.parseTraceAttributes(traceAttributesCode);
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

    private void Init() throws FileNotFoundException {
        tasksCode = new ArrayList<>();
        traceAttributesCode = new ArrayList<>();
        dataCode = new ArrayList<>();
        dataBindingsCode = new ArrayList<>();
        constraintsCode = new ArrayList<>();
        dataConstraintsCode = new ArrayList<>();

        numericData = new HashMap<>();
        numericExpressions = new HashMap<>();

        alloy = new StringBuilder(GetBase());
    }

    public Map<String, String> getNamesEncoding() {
        return parser.getNamesEncoding();
    }

    private void GenerateDataConstraints(List<DataConstraint> dataConstraints) {
        for (DataConstraint i : dataConstraints) {
            alloy.append(gen.Generate(i, getRandomFunctionName(), numericData));
        }
    }

    private List<Constraint> parseConstraints() {
        List<Constraint> constraints = new ArrayList<>();
        for (String c : constraintsCode) {
            String[] p = c.split("\\s*[\\[\\],]\\s*");
            constraints.add(new Constraint(p[0], Arrays.stream(p).skip(1).collect(Collectors.toList())));
        }

        return constraints;
    }

    private void generateConstraints(List<Constraint> constraints) {
        alloy.append("fact {\n");
        for (Constraint i : constraints) {
            alloy.append(i.getName()).append('[').append(i.taskA());
            if (i.isBinary())
                alloy.append(',').append(i.taskB());
            alloy.append("]\n");
        }

        alloy.append("}\n");
    }

    private void generateVacuity(List<Constraint> constraints) {
        alloy.append("fact {\n");
        for (String i : constraints.stream().filter(i -> i.supportsVacuity()).map(i -> i.taskA()).distinct().collect(Collectors.toList()))
            alloy.append("Existence[").append(i).append("]\n");

        alloy.append("}\n");
    }

    private String getRandomFunctionName() {
        return "p" + RandomHelper.getNext();
    }

    private void ParseAndGenerateDataBindings() {
        Map<String, List<String>> taskToData = new HashMap<>();
        Map<String, List<String>> dataToTask = new HashMap<>();

        for (String line : dataBindingsCode) {
            line = line.substring(5);
            List<String> data = Arrays.stream(line.split("[:,\\s]+")).filter(i -> !i.isEmpty()).collect(Collectors.toList());
            String task = data.get(0);
            if (!taskToData.containsKey(task))
                taskToData.put(task, new ArrayList<>());
            for (String i : data.stream().skip(1).collect(Collectors.toList())) {
                taskToData.get(task).add(i);
                if (!dataToTask.containsKey(i))
                    dataToTask.put(i, new ArrayList<>());
                dataToTask.get(i).add(task);
            }
        }

        WriteDataBinding(taskToData, dataToTask);
    }


    private void ExtendNumericData() {  // adds split values to the numeric range
        for (NumericData d : numericData.values())
            if (numericExpressions.containsKey(d.getType()))
                for (DataExpression i : numericExpressions.get(d.getType()))
                    d.addValue(getNumberFromComparison((BinaryExpression) i));
    }

    private String getNumberFromComparison(BinaryExpression ex) {
        if (ex.getLeft().getNode().getType() == Token.Type.Number)
            return ex.getLeft().getNode().getValue();

        if (ex.getRight().getNode().getType() == Token.Type.Number)
            return ex.getRight().getNode().getValue();

        throw new InvalidStateException("No number in comparison operator");
    }

    private void GenerateData(List<EnumeratedData> data) {
        for (EnumeratedData item : data) {
            if (item instanceof NumericData) {
                GenerateNumericDataItem((NumericData) item);
                continue;
            }
            alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {}\n");
            alloy.append("fact { all te: TaskEvent | (lone ").append(item.getType()).append(" & te.data)}\n");
            for (String value : item.getValues()) {
                alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}\n");
            }
        }
    }

    private void GenerateNumericDataItem(NumericData item) {
        alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {\namount: Int\n}\n");
        alloy.append("fact { all te: TaskEvent | (lone ").append(item.getType()).append(" & te.data) }\n");
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

    private void generateTasks(List<Task> tasks) {
        for (Task i : tasks)
            alloy.append("one sig ").append(i.getName()).append(" extends Task {}\n");
    }

    private void SortInput(String[] st) {
        for (String i : st) {
            if (i.isEmpty() || i.startsWith("/"))
                continue;

            if (parser.isTask(i))
                tasksCode.add(i);

            if (parser.isTraceAttribute(i))
                traceAttributesCode.add(i);

            if (parser.isData(i))
                dataCode.add(i);

            if (parser.isDataBinding(i))
                dataBindingsCode.add(i);

            if (parser.isConstraint(i))
                constraintsCode.add(i);

            if (parser.isDataConstraint(i))
                dataConstraintsCode.add(i);
        }
    }

    private void GenerateTaskEvents(int length) {
        for (int i = 0; i < length; i++) {
            if (i < minTraceLength)
                alloy.append("one sig TE");
            else
                alloy.append("lone sig TE");
            alloy.append(i).append(" extends TaskEvent {}\n");
        }
    }


    private void GenerateNextPredicate(int length) {
        alloy.append("pred Next(pre, next: TaskEvent){");
        alloy.append("pre=TE0 and next=TE1");
        for (int i = 2; i < length; i++) {
            alloy.append(" or pre=TE").append(i - 1).append(" and next=TE").append(i);
        }

        alloy.append("}\n");
    }

    private void GenerateAfterPredicate(int length) {
        alloy.append("pred After(b, a: TaskEvent){// b=before, a=after\n");
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

    private void GenerateVariableLengthConstraint(int minTraceLength, int maxTraceLength) {
        alloy.append("fact{\n");
        for (int i = minTraceLength; i < maxTraceLength - 1; ++i) {
            alloy.append("one TE").append(i + 1).append(" implies one TE").append(i).append('\n');
        }

        alloy.append("}\n");
    }


    private void WriteDataBinding(Map<String, List<String>> taskToData, Map<String, List<String>> dataToTask) {
        for (String task : taskToData.keySet()) {
            alloy.append("fact { all te: TaskEvent | te.task = ")
                    .append(task)
                    .append(" implies (one ")
                    .append(String.join(" & te.data and one ", taskToData.get(task)))
                    .append(" & te.data")
                    .append(")}\n");
        }

        for (String payload : dataToTask.keySet()) {
            alloy.append("fact { all te: TaskEvent | lone(").append(payload).append(" & te.data) }\n");
            alloy.append("fact { all te: TaskEvent | one (")
                    .append(payload)
                    .append(" & te.data) implies te.task in (")
                    .append(String.join(" + ", dataToTask.get(payload)))
                    .append(") }\n");
        }
    }

    private String GetBase() throws FileNotFoundException {
        return IOHelper.readAllText("./data/base.als");
    }
}
