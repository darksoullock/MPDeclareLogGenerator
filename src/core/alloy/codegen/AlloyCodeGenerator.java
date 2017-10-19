package core.alloy.codegen;

import core.IOHelper;
import core.models.serialization.TraceProperty;

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
    List<TraceProperty> tattr;

    List<String> tasksCode;
    List<String> traceAttributesCode;
    List<String> dataCode;
    List<String> dataBindingsCode;
    List<String> constraintsCode;
    List<String> dataConstraintsCode;

    Map<String, List<String>> taskToData;
    Map<String, List<String>> dataToTask;

    DeclareParser parser = new DeclareParser();

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
        GenerateTasks();
        GenerateData();
        GenerateDataBindings();
        GenerateConstraints();
        GenerateDataConstraints();
        AddTraceAttributes();
    }

    private void SetMinTraceLength(int minTraceLength, int traceLength) {
        alloy.append("fact {#{te:TaskEvent | te.task=Dummy } <= ").append(traceLength-minTraceLength).append("}\n");
    }

    private void GenerateDataConstraints()  // TODO: incomplete
    {
        for (String i : dataConstraintsCode) {
            if (i.startsWith("Absence"))
                AddAbsenceDataConstraint(i);
        }
    }

    private void GenerateConstraints() {
        alloy.append("fact {\n");
        for (String i : constraintsCode) {
            alloy.append(i).append('\n');
        }

        alloy.append("}\n");
    }

    private void GenerateDataBindings() {
        for (String line : dataBindingsCode) {
            List<String> data = Arrays.stream(line.split("[:,]")).map(i -> i.trim()).filter(i -> !i.isEmpty()).collect(Collectors.toList());
            String task = data.get(0).substring(5);
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

    private void GenerateData()  // TODO: incomplete
    {
        for (String i : dataCode) {
            String[] lr = i.split(":");
            String type = lr[0];
            alloy.append("abstract sig ").append(type).append(" extends Payload {}\n");
            alloy.append("fact { all te: TaskEvent | #{").append(type).append(" & te.data} <= 1 }\n");
            String[] values = lr[1].split(",");
            for (String value : values) {
                alloy.append("one sig ").append(value).append(" extends ").append(type).append("{}\n");
            }
        }
    }

    private void GenerateTasks() {
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

    private void Init() throws FileNotFoundException {
        tasksCode = new ArrayList<>();
        traceAttributesCode = new ArrayList<>();
        dataCode = new ArrayList<>();
        dataBindingsCode = new ArrayList<>();
        constraintsCode = new ArrayList<>();
        dataConstraintsCode = new ArrayList<>();

        taskToData = new HashMap<>();
        dataToTask = new HashMap<>();

        tattr = new ArrayList<>();

        alloy = new StringBuilder(GetBase());
    }

    public String getAlloyCode() {
        if (alloy != null)
            return alloy.toString();
        return null;
    }

    public List<TraceProperty> getTraceAttr() {
        return tattr;
    }

    private void GenerateTaskEvents(int length, int bitwidth) {
        --bitwidth;
        int offset = 1<<bitwidth;
        for (int i = 0; i < length; i++) {
            alloy.append("one sig TE").append(i).append(" extends TaskEvent {} {pos=").append(i - offset).append("}\n");
        }
    }

    private void AddAbsenceDataConstraint(String line) {    //TODO: redo
        String[] lr = line.split("\\|");
        String[] activity = getActivityNameFromConstraintText(lr[0]).split("\\s+"); // [type, name]
        String fn = getRandomFunctionName();

        alloy.append("fact { no te: TaskEvent | te.task = ").append(activity[0]).append(" and ").append(fn).append("[te.data] }\n");
        String co = lr[1];
        if (co.contains("=")) {
            alloy.append("pred ").append(fn).append("(").append(activity[1]).append(": set Payload) { { ").append(co.replace('.', '&')).append(" } }\n");
        }
    }

    private String getRandomFunctionName() {
        return "p" + Math.abs(rnd.nextInt());   //TODO: change
    }

    private String getActivityNameFromConstraintText(String v) {
        Matcher m = inRectBrackets.matcher(v);
        m.matches();
        return m.group(1);
    }

    private void AddTraceAttributes()  // TODO: incomplete, not final syntax
    {
        for (String i : traceAttributesCode) {
            String[] a = i.substring(6).split(" ");
            tattr.add(new TraceProperty(a[0], a[1], Arrays.stream(a).skip(2).collect(Collectors.toList())));
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
