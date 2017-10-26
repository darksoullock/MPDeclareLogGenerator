package core.alloy.codegen;

import core.IOHelper;
import core.RandomHelper;
import core.alloy.codegen.fnparser.BinaryExpression;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.Token;
import core.models.intervals.Interval;
import core.models.declare.DataConstraint;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.NumericData;
import core.models.serialization.trace.AbstractTraceAttribute;
import sun.plugin.dom.exception.InvalidStateException;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.*;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-16.
 */
public class AlloyCodeGenerator {
    int traceLength;
    int minTraceLength;
    int bitwidth;

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

    Map<String, List<String>> taskToData;
    Map<String, List<String>> dataToTask;

    DeclareParser parser = new DeclareParser();
    DataConstraintGenerator gen = new DataConstraintGenerator();

    public AlloyCodeGenerator(int traceLength, int minTraceLength, int bitwidth) {
        this.traceLength = traceLength;
        this.minTraceLength = minTraceLength;
        this.bitwidth = bitwidth;
    }

    public void Run(String declare) throws FileNotFoundException {
        Init();
        SetMinTraceLength(minTraceLength, traceLength);
        GenerateTaskEvents(traceLength, bitwidth);
        SortInput(parser.SplitStatements(declare));
        ParseAndGenerateTasks();
        List<EnumeratedData> data = parser.parseData(dataCode, numericData);
        ParseAndGenerateDataBindings();
        ParseAndGenerateConstraints();
        List<DataConstraint> dataConstraints = parser.ParseDataConstraints(dataConstraintsCode, numericExpressions);
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

        taskToData = new HashMap<>();
        dataToTask = new HashMap<>();

        numericData = new HashMap<>();
        numericExpressions = new HashMap<>();

        alloy = new StringBuilder(GetBase());
    }

    private void SetMinTraceLength(int minTraceLength, int traceLength) {
        alloy.append("fact {#{te:TaskEvent | te.task=Dummy } <= ").append(traceLength - minTraceLength).append("}\n");
    }


    private void GenerateDataConstraints(List<DataConstraint> dataConstraints) {
        for (DataConstraint i : dataConstraints) {
            alloy.append(gen.Generate(i, getRandomFunctionName(), numericData));
        }
    }

    private void ParseAndGenerateConstraints() {
        alloy.append("fact {\n");
        for (String i : constraintsCode) {
            alloy.append(i).append('\n');
        }

        alloy.append("}\n");
    }

    private String getRandomFunctionName() {
        return "p" + RandomHelper.getNext();
    }

    private void ParseAndGenerateDataBindings() {
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

        WriteDataBinding();
    }


    private void ExtendNumericData() {
        for (EnumeratedData d : numericData.values())
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
            alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {}\n");
            alloy.append("fact { all te: TaskEvent | #{").append(item.getType()).append(" & te.data} <= 1 }\n");
            for (String value : item.getValues()) {
                alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}\n");
            }
        }
    }

    private void ParseAndGenerateTasks() {
        for (String i : tasksCode)
            alloy.append("one sig ").append(i).append(" extends Task {}\n");
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

    private void GenerateTaskEvents(int length, int bitwidth) {
        --bitwidth;
        int offset = 1 << bitwidth;
        for (int i = 0; i < length; i++) {
            alloy.append("one sig TE").append(i).append(" extends TaskEvent {} {pos=").append(i - offset).append("}\n");
        }
    }

    private void WriteDataBinding() {
        for (String task : taskToData.keySet()) {
            alloy.append("fact { all te: TaskEvent | te.task = ")
                    .append(task)
                    .append(" implies #{(")
                    .append(String.join(" + ", taskToData.get(task)))
                    .append(") & te.data} = ")
                    .append(taskToData.get(task).size())
                    .append(" }\n");
        }

        for (String payload : dataToTask.keySet()) {
            alloy.append("fact { all te: TaskEvent | #{").append(payload).append(" & te.data} <= 1 }\n");
            alloy.append("fact { all te: TaskEvent | #{")
                    .append(payload)
                    .append(" & te.data} = 1 implies te.task in (")
                    .append(String.join(" + ", dataToTask.get(payload)))
                    .append(") }\n");
        }
    }

    private String GetBase() throws FileNotFoundException {
        return IOHelper.readAllText(new FileInputStream("./data/base.als"));
    }
}
