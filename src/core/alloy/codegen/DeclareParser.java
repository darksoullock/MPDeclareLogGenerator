package core.alloy.codegen;

import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.DataExpressionParser;
import core.alloy.codegen.fnparser.DataFunction;
import core.models.declare.DataConstraint;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.FloatData;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;
import core.models.serialization.trace.AbstractTraceAttribute;
import core.models.serialization.trace.EnumTraceAttribute;
import core.models.serialization.trace.FloatTraceAttribute;
import core.models.serialization.trace.IntTraceAttribute;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-16.
 */
public class DeclareParser {
    Pattern task = Pattern.compile("^\\s*\\w+\\s*$");
    Pattern inRectBrackets = Pattern.compile(".*\\[\\s*(.+?)\\s*].*");

    int intervalSplits;
    DataExpressionParser expressionParser = new DataExpressionParser();

    public DeclareParser(int intervalSplits) {
        this.intervalSplits = intervalSplits;
    }

    public boolean isTask(String line) {
        return task.matcher(line).matches();
    }

    public boolean isTraceAttribute(String line) {
        return line.startsWith("trace ");
    }

    public boolean isData(String line) {
        return (line.contains(":") && !isDataBinding(line) || line.contains(" between ")) && !isTraceAttribute(line);
    }

    public boolean isDataBinding(String line) {
        return line.startsWith("bind ");
    }

    public boolean isConstraint(String line) {
        return line.contains("[") && !isDataConstraint(line);
    }

    public boolean isDataConstraint(String line) {
        return line.contains("|");
    }

    public String[] SplitStatements(String code) {
        return code.replace("\r\n", "\n").split("\n");
    }

    public List<EnumeratedData> parseData(List<String> dataCode, Map<String, NumericData> numericData) {
        ArrayList<EnumeratedData> data = new ArrayList<>();
        for (String i : dataCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (i.contains(":"))
                data.add(new EnumeratedData(a[0], Arrays.stream(a).skip(1).collect(Collectors.toList())));

            if (a[1].equals("integer")) {
                IntegerData b = new IntegerData(a[0], Integer.parseInt(a[3]), Integer.parseInt(a[5]), intervalSplits);
                data.add(b);
                numericData.put(b.getType(), b);
            }

            if (a[1].equals("float")) {
                FloatData b = new FloatData(a[0], Float.parseFloat(a[3]), Float.parseFloat(a[5]), intervalSplits);
                data.add(b);
                numericData.put(b.getType(), b);
            }
        }

        return data;
    }

    public List<DataConstraint> parseDataConstraints(List<String> dataConstraintsCode, Map<String, List<DataExpression>> numericExpressions) {
        List<DataConstraint> dataConstraints = new ArrayList<>();
        for (String line : dataConstraintsCode) {
            String[] lr = line.split("\\|");
            String activity = lr[0].substring(0, lr[0].indexOf('['));
            List<String[]> args = Arrays.stream(getActivityArgsFromConstraintText(lr[0]).split(",\\s*"))
                    .map(i -> i.split("\\s+"))
                    .collect(Collectors.toList());
            List<DataFunction> fns = new ArrayList<>();
            for (int i = 1; i < lr.length; ++i) {
                DataExpression expr = expressionParser.parse(lr[i]);
                expressionParser.retrieveNumericExpressions(numericExpressions, expr);
                DataFunction fn = new DataFunction(args.stream().filter(x -> x.length == 2).map(x -> x[1]).limit(i).collect(Collectors.toList()), expr);
                fns.add(fn);
            }

            DataConstraint c = new DataConstraint(activity, args.stream().map(i -> i[0]).collect(Collectors.toList()), fns);
            dataConstraints.add(c);
        }

        return dataConstraints;
    }


    private String getActivityArgsFromConstraintText(String v) {
        Matcher m = inRectBrackets.matcher(v);
        m.matches();
        return m.group(1);
    }

    public List<AbstractTraceAttribute> parseTraceAttributes(List<String> traceAttributesCode) {
        List<AbstractTraceAttribute> traceAttributes = new ArrayList<>();
        for (String i : traceAttributesCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (i.contains(":"))
                traceAttributes.add(new EnumTraceAttribute(a[1], Arrays.stream(a).skip(2).collect(Collectors.toList())));

            if (a[2].equals("integer"))
                traceAttributes.add(new IntTraceAttribute(a[1], Integer.parseInt(a[4]), Integer.parseInt(a[6])));

            if (a[2].equals("float"))
                traceAttributes.add(new FloatTraceAttribute(a[1], Float.parseFloat(a[4]), Float.parseFloat(a[6])));
        }

        return traceAttributes;
    }
}