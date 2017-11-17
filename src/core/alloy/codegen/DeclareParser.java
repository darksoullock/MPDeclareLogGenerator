package core.alloy.codegen;

import core.Global;
import core.IOHelper;
import core.RandomHelper;
import core.alloy.codegen.fnparser.DataExpression;
import core.alloy.codegen.fnparser.DataExpressionParser;
import core.alloy.codegen.fnparser.DataFunction;
import core.models.declare.DataConstraint;
import core.models.declare.Task;
import core.models.declare.data.EnumeratedData;
import core.models.declare.data.FloatData;
import core.models.declare.data.IntegerData;
import core.models.declare.data.NumericData;
import core.models.serialization.trace.AbstractTraceAttribute;
import core.models.serialization.trace.EnumTraceAttribute;
import core.models.serialization.trace.FloatTraceAttribute;
import core.models.serialization.trace.IntTraceAttribute;
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
    Map<String, String> namesEncoding;

    int intervalSplits;
    DataExpressionParser expressionParser = new DataExpressionParser();

    public DeclareParser(int intervalSplits) {
        this.intervalSplits = intervalSplits;
    }

    public boolean isTask(String line) {
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

    public List<Task> parseTasks(List<String> tasksCode) {
        ArrayList<Task> data = new ArrayList<>();
        for (String i : tasksCode) {
            String name = i.substring(9); // syntax: 'activity TaskName'
            data.add(new Task(name));
        }

        return data;
    }

    public List<EnumeratedData> parseData(List<String> dataCode, Map<String, NumericData> numericData) {
        ArrayList<EnumeratedData> data = new ArrayList<>();
        for (String i : dataCode) {
            String[] a = i.split(":\\s*|,?\\s+");

            if (a[1].equals("integer")) {
                IntegerData b = new IntegerData(a[0], Integer.parseInt(a[3]), Integer.parseInt(a[5]), intervalSplits);
                data.add(b);
                numericData.put(b.getType(), b);
            } else if (a[1].equals("float")) {
                FloatData b = new FloatData(a[0], Float.parseFloat(a[3]), Float.parseFloat(a[5]), intervalSplits);
                data.add(b);
                numericData.put(b.getType(), b);
            } else {
                data.add(new EnumeratedData(a[0], Arrays.stream(a).skip(1).collect(Collectors.toList())));
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

            try {
                if (a[2].equals("integer"))
                    traceAttributes.add(new IntTraceAttribute(a[1], Integer.parseInt(a[4]), Integer.parseInt(a[6])));

                if (a[2].equals("float"))
                    traceAttributes.add(new FloatTraceAttribute(a[1], Float.parseFloat(a[4]), Float.parseFloat(a[6])));

            } catch (NumberFormatException ex) {
                System.out.println(namesEncoding.get(a[4]) + " or " + namesEncoding.get(a[6]) + " caused an error");
                System.out.println("Possible reason: name containing only digits without quote marks");
                throw ex;
            }
        }

        return traceAttributes;
    }

    public Map<String, String> getNamesEncoding() {
        return namesEncoding;
    }

    public String encodeNames(String declare) {
        namesEncoding = new HashMap<>();
        List<String> names = new ArrayList<>();

        for (String i : splitStatements(declare)) {
            if (i.isEmpty() || i.startsWith("/"))
                continue;

            if (isTask(i))
                names.add(i.substring(9));

            if (isTraceAttribute(i))   // to be added
                names.addAll(getTraceAttributeNamesFromRawCode(i));

            if (isData(i))
                names.addAll(getDataNamesFromRawCode(i));
        }

        return replaceNames(declare, names);
    }

    private List<String> getTraceAttributeNamesFromRawCode(String taCode) {
        return getDataNamesFromRawCode(taCode.substring(6));    // now syntax is the same with 'trace ' prefix
    }

    public List<String> getDataNamesFromRawCode(String dataCode) {
        int scc = StringUtils.countMatches(dataCode, ':');
        int cc = StringUtils.countMatches(dataCode, ',');

        // matches last ':' of odd sequence of this symbol. e.g. ':', ':::', ':::::'
        // or the same with ','
        String[] a = dataCode.split("(?<=([^:](::){0," + scc + "})):(?!:)\\s*|(?<=([^,](,,){0," + cc + "})),(?!,)\\s*");

        if (a[1].startsWith("integer"))
            return Arrays.asList(a[0]);

        if (a[1].startsWith("float"))
            return Arrays.asList(a[0]);

        return Arrays.asList(a);
    }

    private String replaceNames(String declare, List<String> names) {
        checkInterference(declare, names);

        names.sort((i, j) -> j.length() - i.length());

        String[] from = new String[names.size()];
        String[] to = new String[names.size()];

        int i = 0;
        for (String name : names) {
            String newVal = RandomHelper.getName();
            from[i] = name;
            to[i] = newVal;
            namesEncoding.put(newVal, unescapeName(name));
            ++i;
        }

        declare = StringUtils.replaceEach(declare, from, to);
        return declare;
    }

    private String unescapeName(String name) {
        name = StringUtils.replaceEach(name, new String[]{"::", ",,"}, new String[]{":", ","}).trim();
        if (name.charAt(0) == '\'' && name.charAt(name.length() - 1) == '\'' || name.charAt(0) == '"' && name.charAt(name.length() - 1) == '"')
            name = name.substring(1, name.length() - 1);

        return name;
    }

    // may throw exception if name might interfere with reserved keywords
    private void checkInterference(String declare, List<String> names) {
        String keywords = IOHelper.readAllText("./data/keywords.txt");
        for (String name : names) {
            if (keywords.contains(name)) {
                System.out.println("The name '" + name + "' might be part of reserved keyword. If other errors appear try to rename it or use in quote marks.");
                continue;
            }

            if (Global.deepNamingCheck) {
                Pattern pattern = Pattern.compile("[\\d\\w]" + name + "[\\d\\w]|[\\d\\w]" + name + "|" + name + "[\\d\\w]");
                Matcher m = pattern.matcher(declare);
                if (m.find() && !name.contains(m.group(0)))
                    System.out.println("The name '" + name + "' might be part of reserved keyword. If other errors appear try to rename it or use in quote marks.");
            }
        }
    }
}