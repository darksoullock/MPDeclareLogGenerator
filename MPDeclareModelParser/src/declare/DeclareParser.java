package declare;

import declare.fnparser.DataExpression;
import declare.fnparser.DataExpressionParser;
import declare.fnparser.DataFunction;
import declare.lang.Activity;
import declare.lang.Constraint;
import declare.lang.DataConstraint;
import declare.lang.Statement;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;
import declare.lang.trace.EnumTraceAttribute;
import declare.lang.trace.FloatTraceAttribute;
import declare.lang.trace.IntTraceAttribute;
import org.apache.commons.lang3.StringUtils;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import java.util.stream.Collectors;

/**
 * Created by Vasiliy on 2017-10-16.
 */
public class DeclareParser {
    Pattern inRectBrackets = Pattern.compile(".*\\[\\s*(.+?)\\s*].*");

    List<String> tasksCode;
    List<String> traceAttributesCode;
    List<String> dataCode;
    List<String> dataBindingsCode;
    List<Statement> constraintsCode;
    List<Statement> dataConstraintsCode;

    DataExpressionParser expressionParser = new DataExpressionParser();

    public DeclareModel Parse(String declare)
            throws DeclareParserException {
        Init();
        DeclareModel model = new DeclareModel();
        SortInput(splitStatements(declare));
        model.setActivities(parseActivities(tasksCode));
        parseData(dataCode, model.getEnumeratedData(), model.getIntegerData(), model.getFloatData());
        ParseDataBindings(model.getActivityToData(), model.getDataToActivity());
        model.setConstraints(parseConstraints());
        model.setDataConstraints(parseDataConstraints(dataConstraintsCode));
        parseTraceAttributes(traceAttributesCode, model.getEnumTraceAttributes(), model.getIntTraceAttributes(), model.getFloatTraceAttributes());
        return model;
    }

    private void Init() {
        tasksCode = new ArrayList<>();
        traceAttributesCode = new ArrayList<>();
        dataCode = new ArrayList<>();
        dataBindingsCode = new ArrayList<>();
        constraintsCode = new ArrayList<>();
        dataConstraintsCode = new ArrayList<>();
    }

    private void SortInput(String[] st) {
        int line = 0;
        for (String i : st) {
            ++line;

            if (i.isEmpty() || i.startsWith("/"))
                continue;

            if (isActivity(i))
                tasksCode.add(i);

            if (isTraceAttribute(i))
                traceAttributesCode.add(i);

            if (isData(i))
                dataCode.add(i);

            if (isDataBinding(i))
                dataBindingsCode.add(i);

            if (isConstraint(i))
                constraintsCode.add(new Statement(i, line));

            if (isDataConstraint(i))
                dataConstraintsCode.add(new Statement(i, line));
        }
    }

    private void ParseDataBindings(Map<String, Set<String>> activityToData, Map<String, Set<String>> dataToActivity) {
        for (String line : dataBindingsCode) {
            line = line.substring(5);
            List<String> data = Arrays.stream(line.split("[:,\\s]+")).filter(i -> !i.isEmpty()).collect(Collectors.toList());
            String activity = data.get(0);
            if (!activityToData.containsKey(activity))
                activityToData.put(activity, new HashSet<>());
            for (String i : data.stream().skip(1).collect(Collectors.toList())) {
                activityToData.get(activity).add(i);
                if (!dataToActivity.containsKey(i))
                    dataToActivity.put(i, new HashSet<>());
                dataToActivity.get(i).add(activity);
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

    public boolean isActivity(String line) {
        return line.startsWith("activity ");
    }

    public boolean isTraceAttribute(String line) {
        return line.startsWith("trace ");
    }

    public boolean isData(String line) {
        return (StringUtils.countMatches(line, ':') % 2 == 1 && !isTraceAttribute(line)) && !isDataBinding(line);
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

    public String[] splitStatements(String code) {
        return code.replace("\r\n", "\n").split("\n");
    }

    public Set<Activity> parseActivities(List<String> tasksCode) {
        Set<Activity> data = new HashSet<>();
        for (String i : tasksCode) {
            String name = i.substring(9); // syntax: 'activity ActivityName'
            data.add(new Activity(name));
        }

        return data;
    }

    public void parseData(List<String> dataCode, Set<EnumeratedData> edata,
                          Set<IntegerData> idata, Set<FloatData> fdata) {
        for (String i : dataCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (a[1].equals("integer") && a[2].equals("between")) {
                idata.add(new IntegerData(a[0], Integer.parseInt(a[3]), Integer.parseInt(a[5])));
            } else if (a[1].equals("float") && a[2].equals("between")) {
                fdata.add(new FloatData(a[0], Float.parseFloat(a[3]), Float.parseFloat(a[5])));
            } else {
                edata.add(new EnumeratedData(a[0], Arrays.stream(a).skip(1).collect(Collectors.toList())));
            }
        }
    }

    public List<DataConstraint> parseDataConstraints(List<Statement> dataConstraintsCode) throws DeclareParserException {
        List<DataConstraint> dataConstraints = new ArrayList<>();
        for (Statement st : dataConstraintsCode) {
            String[] lr = st.getCode().split("\\|", -1);
            String activity = lr[0].substring(0, lr[0].indexOf('['));
            List<String[]> args = Arrays.stream(getActivityArgsFromConstraintText(lr[0]).split(",\\s*"))
                    .map(i -> (i + " A").split("\\s+"))
                    .collect(Collectors.toList());

            if (args.size() > 1) {
                args.get(1)[args.get(1).length - 1] = "B";
            }

            List<DataFunction> fns = new ArrayList<>();
            for (int i = 1; i < lr.length; ++i) {
                DataExpression expr = expressionParser.parse(lr[i]);
                DataFunction fn = new DataFunction(args.stream().filter(x -> x.length >= 2).map(x -> x[1]).limit(i).collect(Collectors.toList()), expr);
                fns.add(fn);
            }

            DataConstraint c = new DataConstraint(activity, args.stream().map(i -> i[0]).collect(Collectors.toList()), fns, st);


            dataConstraints.add(c);
        }

        return dataConstraints;
    }


    private String getActivityArgsFromConstraintText(String v) {
        Matcher m = inRectBrackets.matcher(v);
        m.matches();
        return m.group(1);
    }

    public void parseTraceAttributes(List<String> traceAttributesCode, List<EnumTraceAttribute> eta,
                                     List<IntTraceAttribute> ita, List<FloatTraceAttribute> fta) {
        for (String i : traceAttributesCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (a[2].equals("integer")) {
                ita.add(new IntTraceAttribute(a[1], Integer.parseInt(a[4]), Integer.parseInt(a[6])));
            } else if (a[2].equals("float")) {
                fta.add(new FloatTraceAttribute(a[1], Float.parseFloat(a[4]), Float.parseFloat(a[6])));
            } else {
                eta.add(new EnumTraceAttribute(a[1], Arrays.stream(a).skip(2).collect(Collectors.toList())));
            }
        }
    }
}