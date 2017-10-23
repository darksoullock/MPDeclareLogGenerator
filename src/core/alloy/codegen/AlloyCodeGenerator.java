package core.alloy.codegen;

import core.IOHelper;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.DataExpressionParser;
import core.alloy.codegen.fnparser.DataFunction;
import core.models.declare.DataConstraint;
import core.models.declare.EnumeratedData;
import core.models.declare.FloatData;
import core.models.declare.IntegerData;
import core.models.serialization.trace.AbstractTraceAttribute;
import core.models.serialization.trace.EnumTraceAttribute;
import core.models.serialization.trace.FloatTraceAttribute;
import core.models.serialization.trace.IntTraceAttribute;
import sun.plugin.dom.exception.InvalidStateException;

import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
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
    List<EnumeratedData> data;
    List<DataConstraint> dataConstraints;

    List<String> tasksCode;
    List<String> traceAttributesCode;
    List<String> dataCode;
    List<String> dataBindingsCode;
    List<String> constraintsCode;
    List<String> dataConstraintsCode;

    Map<String, EnumeratedData> numericData;

    Map<String, List<String>> taskToData;
    Map<String, List<String>> dataToTask;

    boolean dataConstraintsParsed = false;

    DeclareParser parser = new DeclareParser();
    DataExpressionParser expressionParser = new DataExpressionParser();

    DataConstraintGenerator gen = new DataConstraintGenerator();

    Pattern inRectBrackets = Pattern.compile(".*\\[\\s*(.+?)\\s*\\].*");

    Random rnd = new Random();

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
        ParseData();
        ParseAndGenerateDataBindings();
        ParseAndGenerateConstraints();
        ParseDataConstraints();
        GenerateDataConstraints();
        GenerateData();
        AddTraceAttributes();
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

        data = new ArrayList<>();
        dataConstraints = new ArrayList<>();
        traceAttributes = new ArrayList<>();

        numericData = new HashMap<>();

        alloy = new StringBuilder(GetBase());
    }

    private void SetMinTraceLength(int minTraceLength, int traceLength) {
        alloy.append("fact {#{te:TaskEvent | te.task=Dummy } <= ").append(traceLength - minTraceLength).append("}\n");
    }

    private void ParseDataConstraints()
    {
        for (String line : dataConstraintsCode) {
            String[] lr = line.split("\\|");
            String activity = lr[0].substring(0, lr[0].indexOf('['));
            List<String[]> args = Arrays.stream(getActivityArgsFromConstraintText(lr[0]).split(",\\s*"))
                    .map(i -> i.split("\\s+"))
                    .collect(Collectors.toList());
            List<DataFunction> fns = new ArrayList<>();
            for (int i = 1; i < lr.length; ++i) {
                DataExpression expr = expressionParser.parse(lr[i]);
                DataFunction fn = new DataFunction(args.stream().map(x -> x[1]).collect(Collectors.toList()), expr);
                fns.add(fn);
            }

            DataConstraint c = new DataConstraint(activity, args.stream().map(i -> i[0]).collect(Collectors.toList()), fns);
            dataConstraints.add(c);
        }

        dataConstraintsParsed = true;
    }

    private void GenerateDataConstraints() {
        for (DataConstraint i : dataConstraints) {
            alloy.append(gen.Generate(i, getRandomFunctionName()));
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
        return "p" + Math.abs(rnd.nextInt());   //TODO: change
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

    private void ParseData() {
        for (String i : dataCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (i.contains(":"))
                data.add(new EnumeratedData(a[0], Arrays.stream(a).skip(1).collect(Collectors.toList())));

            if (a[2].equals("integer")) {
                IntegerData b = new IntegerData(a[0], Integer.parseInt(a[3]), Integer.parseInt(a[5]));
                data.add(b);
                numericData.put(b.getType(), b);
            }

            if (a[2].equals("float")) {
                FloatData b = new FloatData(a[0], Float.parseFloat(a[3]), Float.parseFloat(a[5]));
                data.add(b);
                numericData.put(b.getType(), b);
            }
        }
    }

    private void GenerateData() {
        if (!dataConstraintsParsed)
            throw new InvalidStateException("Data constraints should be parsed first. Otherwise numbers might be skipped");

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

    public String getAlloyCode() {
        if (alloy != null)
            return alloy.toString();
        return null;
    }

    public List<AbstractTraceAttribute> getTraceAttr() {
        return traceAttributes;
    }

    private void GenerateTaskEvents(int length, int bitwidth) {
        --bitwidth;
        int offset = 1 << bitwidth;
        for (int i = 0; i < length; i++) {
            alloy.append("one sig TE").append(i).append(" extends TaskEvent {} {pos=").append(i - offset).append("}\n");
        }
    }

    private String getActivityArgsFromConstraintText(String v) {
        Matcher m = inRectBrackets.matcher(v);
        m.matches();
        return m.group(1);
    }

    private void AddTraceAttributes() {
        for (String i : traceAttributesCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (i.contains(":"))
                traceAttributes.add(new EnumTraceAttribute(a[1], Arrays.stream(a).skip(2).collect(Collectors.toList())));

            if (a[2].equals("integer"))
                traceAttributes.add(new IntTraceAttribute(a[1], Integer.parseInt(a[4]), Integer.parseInt(a[6])));

            if (a[2].equals("float"))
                traceAttributes.add(new FloatTraceAttribute(a[1], Float.parseFloat(a[4]), Float.parseFloat(a[6])));
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
