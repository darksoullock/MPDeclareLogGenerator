//package core.alloy.codegen;
//
//import core.Exceptions.DeclareParserException;
//import core.Global;
//import core.alloy.codegen.fnparser.DataExpression;
//import core.alloy.codegen.fnparser.DataExpressionParser;
//import core.alloy.codegen.fnparser.DataFunction;
//import core.helpers.RandomHelper;
//import core.models.DeclareModel;
//import core.models.declare.Activity;
//import core.models.declare.Constraint;
//import core.models.declare.DataConstraint;
//import core.models.declare.Statement;
//import core.models.declare.data.EnumeratedData;
//import core.models.declare.data.FloatData;
//import core.models.declare.data.IntegerData;
//import core.models.serialization.trace.AbstractTraceAttribute;
//import core.models.serialization.trace.EnumTraceAttribute;
//import core.models.serialization.trace.FloatTraceAttribute;
//import core.models.serialization.trace.IntTraceAttribute;
//import org.apache.commons.lang3.StringUtils;
//
//import java.util.*;
//import java.util.regex.Matcher;
//import java.util.regex.Pattern;
//import java.util.stream.Collectors;
//
///**
// * Created by Vasiliy on 2017-10-16.
// */
//public class DeclareParser {
//    Pattern inRectBrackets = Pattern.compile(".*\\[\\s*(.+?)\\s*].*");
//    Map<String, String> namesEncoding;
//
//    List<String> tasksCode;
//    List<String> traceAttributesCode;
//    List<String> dataCode;
//    List<String> dataBindingsCode;
//    List<Statement> constraintsCode;
//    List<Statement> dataConstraintsCode;
//
//    int intervalSplits;
//    DataExpressionParser expressionParser = new DataExpressionParser();
//
//    public DeclareParser(int intervalSplits) {
//        this.intervalSplits = intervalSplits;
//    }
//
//    public DeclareModel Parse(String declare)
//            throws DeclareParserException {
//        Init();
//        DeclareModel model = new DeclareModel();
//        if (Global.encodeNames)
//            declare = encodeNames(declare);
//        SortInput(splitStatements(declare));
//        model.setActivities(parseActivities(tasksCode));
//        model.setData(parseData(dataCode));
//        ParseDataBindings(model.getActivityToData(), model.getDataToActivity());
//        model.setConstraints(parseConstraints());
//        model.setDataConstraints(parseDataConstraints(dataConstraintsCode));
//        model.setTraceAttributes(parseTraceAttributes(traceAttributesCode));
//        return model;
//    }
//
//    private void Init() {
//        tasksCode = new ArrayList<>();
//        traceAttributesCode = new ArrayList<>();
//        dataCode = new ArrayList<>();
//        dataBindingsCode = new ArrayList<>();
//        constraintsCode = new ArrayList<>();
//        dataConstraintsCode = new ArrayList<>();
//    }
//
//    private void SortInput(String[] st) {
//        int line = 0;
//        for (String i : st) {
//            ++line;
//
//            if (i.isEmpty() || i.startsWith("/"))
//                continue;
//
//            if (isActivity(i))
//                tasksCode.add(i);
//
//            if (isTraceAttribute(i))
//                traceAttributesCode.add(i);
//
//            if (isData(i))
//                dataCode.add(i);
//
//            if (isDataBinding(i))
//                dataBindingsCode.add(i);
//
//            if (isConstraint(i))
//                constraintsCode.add(new Statement(i, line));
//
//            if (isDataConstraint(i))
//                dataConstraintsCode.add(new Statement(i, line));
//        }
//    }
//
//    private void ParseDataBindings(Map<String, List<String>> activityToData, Map<String, List<String>> dataToActivity) {
//        for (String line : dataBindingsCode) {
//            line = line.substring(5);
//            List<String> data = Arrays.stream(line.split("[:,\\s]+")).filter(i -> !i.isEmpty()).collect(Collectors.toList());
//            String activity = data.get(0);
//            if (!activityToData.containsKey(activity))
//                activityToData.put(activity, new ArrayList<>());
//            for (String i : data.stream().skip(1).collect(Collectors.toList())) {
//                activityToData.get(activity).add(i);
//                if (!dataToActivity.containsKey(i))
//                    dataToActivity.put(i, new ArrayList<>());
//                dataToActivity.get(i).add(activity);
//            }
//        }
//    }
//
//    private List<Constraint> parseConstraints() {
//        List<Constraint> constraints = new ArrayList<>();
//        for (Statement s : constraintsCode) {
//            String[] p = s.getCode().split("\\s*[\\[\\],]\\s*");
//            constraints.add(new Constraint(p[0], Arrays.stream(p).skip(1).collect(Collectors.toList()), s));
//        }
//
//        return constraints;
//    }
//
//    public boolean isActivity(String line) {
//        return line.startsWith("activity ");
//    }
//
//    public boolean isTraceAttribute(String line) {
//        return line.startsWith("trace ");
//    }
//
//    public boolean isData(String line) {
//        return (StringUtils.countMatches(line, ':') % 2 == 1 && !isTraceAttribute(line)) && !isDataBinding(line);
//    }
//
//    public boolean isDataBinding(String line) {
//        return line.startsWith("bind ");
//    }
//
//    public boolean isConstraint(String line) {
//        return line.contains("[") && !isDataConstraint(line);
//    }
//
//    public boolean isDataConstraint(String line) {
//        return line.contains("|");
//    }
//
//    public String[] splitStatements(String code) {
//        return code.replace("\r\n", "\n").split("\n");
//    }
//
//    public List<Activity> parseActivities(List<String> tasksCode) {
//        ArrayList<Activity> data = new ArrayList<>();
//        for (String i : tasksCode) {
//            String name = i.substring(9); // syntax: 'activity ActivityName'
//            data.add(new Activity(name));
//        }
//
//        return data;
//    }
//
//    public List<EnumeratedData> parseData(List<String> dataCode) {
//        ArrayList<EnumeratedData> data = new ArrayList<>();
//        for (String i : dataCode) {
//            String[] a = i.split(":\\s*|,?\\s+");
//
//            if (a[1].equals("integer")) {
//                IntegerData b = new IntegerData(a[0], Integer.parseInt(a[3]), Integer.parseInt(a[5]), intervalSplits, null);
//                data.add(b);
//            } else if (a[1].equals("float")) {
//                FloatData b = new FloatData(a[0], Float.parseFloat(a[3]), Float.parseFloat(a[5]), intervalSplits, null);
//                data.add(b);
//            } else {
//                data.add(new EnumeratedData(a[0], Arrays.stream(a).skip(1).collect(Collectors.toList())));
//            }
//        }
//
//        return data;
//    }
//
//    public List<DataConstraint> parseDataConstraints(List<Statement> dataConstraintsCode) throws DeclareParserException {
//        List<DataConstraint> dataConstraints = new ArrayList<>();
//        for (Statement st : dataConstraintsCode) {
//            String[] lr = st.getCode().split("\\|", -1);
//            String activity = lr[0].substring(0, lr[0].indexOf('['));
//            List<String[]> args = Arrays.stream(getActivityArgsFromConstraintText(lr[0]).split(",\\s*"))
//                    .map(i -> (i + " A").split("\\s+"))
//                    .collect(Collectors.toList());
//
//            if (args.size() > 1) {
//                args.get(1)[args.get(1).length - 1] = "B";
//            }
//
//            List<DataFunction> fns = new ArrayList<>();
//            for (int i = 1; i < lr.length; ++i) {
//                DataExpression expr = expressionParser.parse(lr[i]);
//                DataFunction fn = new DataFunction(args.stream().filter(x -> x.length >= 2).map(x -> x[1]).limit(i).collect(Collectors.toList()), expr);
//                fns.add(fn);
//            }
//
//            DataConstraint c = new DataConstraint(activity, args.stream().map(i -> i[0]).collect(Collectors.toList()), fns, st);
//
//
//            dataConstraints.add(c);
//        }
//
//        return dataConstraints;
//    }
//
//
//    private String getActivityArgsFromConstraintText(String v) {
//        Matcher m = inRectBrackets.matcher(v);
//        m.matches();
//        return m.group(1);
//    }
//
//    public List<AbstractTraceAttribute> parseTraceAttributes(List<String> traceAttributesCode) {
//        List<AbstractTraceAttribute> traceAttributes = new ArrayList<>();
//        for (String i : traceAttributesCode) {
//            String[] a = i.split(":\\s*|,?\\s+");
//
//            if (a[2].equals("integer")) {
//                traceAttributes.add(new IntTraceAttribute(a[1], Integer.parseInt(a[4]), Integer.parseInt(a[6])));
//            } else if (a[2].equals("float")) {
//                traceAttributes.add(new FloatTraceAttribute(a[1], Float.parseFloat(a[4]), Float.parseFloat(a[6])));
//            } else {
//                traceAttributes.add(new EnumTraceAttribute(a[1], Arrays.stream(a).skip(2).collect(Collectors.toList())));
//            }
//        }
//
//        return traceAttributes;
//    }
//
//    public Map<String, String> getNamesEncoding() {
//        return namesEncoding;
//    }
//
//    public String encodeNames(String declare) {
//        namesEncoding = new HashMap<>();
//        List<String> names = new ArrayList<>();
//
//        for (String i : splitStatements(declare)) {
//            if (i.isEmpty() || i.startsWith("/"))
//                continue;
//
//            if (isActivity(i))
//                names.add(i.substring(9).trim());
//
//            if (isTraceAttribute(i))
//                names.addAll(getTraceAttributeNamesFromRawCode(i));
//
//            if (isData(i))
//                names.addAll(getDataNamesFromRawCode(i));
//        }
//
//        return replaceNames(declare, names);
//    }
//
//    private List<String> getTraceAttributeNamesFromRawCode(String taCode) {
//        return getDataNamesFromRawCode(taCode.substring(6).trim());    // now syntax is the same with 'trace ' prefix
//    }
//
//    private List<String> getDataNamesFromRawCode(String dataCode) {
//        int scc = StringUtils.countMatches(dataCode, ':');
//        int cc = StringUtils.countMatches(dataCode, ',');
//
//        // matches last ':' of odd sequence of this symbol. e.g. ':', ':::', ':::::'
//        // or the same with ','
//        String[] a = dataCode.split("(?<=([^:](::){0," + scc + "})):(?!:)\\s*|(?<=([^,](,,){0," + cc + "})),(?!,)\\s*");
//
//        if (a[1].startsWith("integer"))
//            return Arrays.asList(a[0].trim());
//
//        if (a[1].startsWith("float"))
//            return Arrays.asList(a[0].trim());
//
//        return Arrays.asList(a);
//    }
//
//    private String replaceNames(String declare, List<String> names) {
//        checkInterference(declare, names);
//
//        names.sort((i, j) -> j.length() - i.length());
//
//        String[] from = new String[names.size()];
//        String[] to = new String[names.size()];
//
//        int i = 0;
//        for (String name : names) {
//            String newVal = RandomHelper.getName();
//            from[i] = name;
//            to[i] = newVal;
//            namesEncoding.put(newVal, unescapeName(name));
//            ++i;
//        }
//
//        declare = StringUtils.replaceEach(declare, from, to);
//        return declare;
//    }
//
//    private String unescapeName(String name) {
//        name = StringUtils.replaceEach(name, new String[]{"::", ",,"}, new String[]{":", ","}).trim();
//        if (name.charAt(0) == '\'' && name.charAt(name.length() - 1) == '\'' || name.charAt(0) == '"' && name.charAt(name.length() - 1) == '"')
//            name = name.substring(1, name.length() - 1);
//
//        return name;
//    }
//
//    // may throw exception if name might interfere with reserved keywords
//    private void checkInterference(String declare, List<String> names) {
//        //String keywords = IOHelper.readAllText("./data/keywords.txt");
//        String keywords = " activity x\n" +
//                " Init[]\n" +
//                " Existence[] \n" +
//                " Existence[]\n" +
//                " Absence[]\n" +
//                " Absence[]\n" +
//                " Exactly[]\n" +
//                " Choice[] \n" +
//                " ExclusiveChoice[] \n" +
//                " RespondedExistence[] \n" +
//                " Response[] \n" +
//                " AlternateResponse[] \n" +
//                " ChainResponse[]\n" +
//                " Precedence[] \n" +
//                " AlternatePrecedence[] \n" +
//                " ChainPrecedence[] \n" +
//                " NotRespondedExistence[] \n" +
//                " NotResponse[] \n" +
//                " NotPrecedence[] \n" +
//                " NotChainResponse[]\n" +
//                " NotChainPrecedence[]\n" +
//                " integer between x and x\n" +
//                " float between x and x\n" +
//                " trace x\n" +
//                " bind x\n" +
//                " : , x\n" +
//                " is not x\n" +
//                " not in x\n" +
//                " is x\n" +
//                " in x\n" +
//                " not x\n" +
//                " or x\n" +
//                " and x\n" +
//                " same x\n" +
//                " different x\n" +
//                " not x\n" +
//                " [ ] x\n" +
//                " ( ) x\n" +
//                " . x\n" +
//                " > x\n" +
//                " < x\n" +
//                " >= x\n" +
//                " <= x\n" +
//                " = x\n" +
//                " | x\n" +
//                "\n";
//        for (String name : names) {
//            if (keywords.contains(name)) {
//                Global.log.accept("The name '" + name + "' might be part of reserved keyword. If other errors appear try to rename it or use in quote marks.");
//                continue;
//            }
//
//            if (Global.deepNamingCheck) {
//                Pattern pattern = Pattern.compile("[\\d\\w]" + name + "[\\d\\w]|[\\d\\w]" + name + "|" + name + "[\\d\\w]");
//                Matcher m = pattern.matcher(declare);
//                if (m.find() && !name.contains(m.group(0)))
//                    Global.log.accept("The name '" + name + "' might be part of reserved keyword. If other errors appear try to rename it or use in quote marks.");
//            }
//        }
//    }
//}