package core.alloy.codegen;

import core.Global;
import core.helpers.RandomHelper;
import declare.DeclareParser;
import org.apache.commons.lang3.StringUtils;

import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Created by Vasiliy on 2018-05-10.
 */
public class NameEncoder {

    Map<String, String> namesEncoding;
    DeclareParser parser;

    public NameEncoder(DeclareParser parser) {
        this.parser = parser;
    }

    public String encode(String declare) {
        namesEncoding = new HashMap<>();
        List<String> names = new ArrayList<>();

        for (String i : parser.splitStatements(declare)) {
            if (i.isEmpty() || i.startsWith("/"))
                continue;

            if (parser.isActivity(i))
                names.add(i.substring(9).trim());

            if (parser.isTraceAttribute(i))
                names.addAll(getTraceAttributeNamesFromRawCode(i));

            if (parser.isData(i))
                names.addAll(getDataNamesFromRawCode(i));
        }

        return replaceNames(declare, names);
    }

    private List<String> getTraceAttributeNamesFromRawCode(String taCode) {
        return getDataNamesFromRawCode(taCode.substring(6).trim());    // now syntax is the same with 'trace ' prefix
    }

    private List<String> getDataNamesFromRawCode(String dataCode) {
        int scc = StringUtils.countMatches(dataCode, ':');
        int cc = StringUtils.countMatches(dataCode, ',');

        // matches last ':' of odd sequence of this symbol. e.g. ':', ':::', ':::::'
        // or the same with ','
        String[] a = dataCode.split("(?<=([^:](::){0," + scc + "})):(?!:)\\s*|(?<=([^,](,,){0," + cc + "})),(?!,)\\s*");

        if (a[1].startsWith("integer"))
            return Arrays.asList(a[0].trim());

        if (a[1].startsWith("float"))
            return Arrays.asList(a[0].trim());

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
        //String keywords = IOHelper.readAllText("./data/keywords.txt");
        String keywords = " activity x\n" +
                " Init[]\n" +
                " Existence[] \n" +
                " Existence[]\n" +
                " Absence[]\n" +
                " Absence[]\n" +
                " Exactly[]\n" +
                " Choice[] \n" +
                " ExclusiveChoice[] \n" +
                " RespondedExistence[] \n" +
                " Response[] \n" +
                " AlternateResponse[] \n" +
                " ChainResponse[]\n" +
                " Precedence[] \n" +
                " AlternatePrecedence[] \n" +
                " ChainPrecedence[] \n" +
                " NotRespondedExistence[] \n" +
                " NotResponse[] \n" +
                " NotPrecedence[] \n" +
                " NotChainResponse[]\n" +
                " NotChainPrecedence[]\n" +
                " integer between x and x\n" +
                " float between x and x\n" +
                " trace x\n" +
                " bind x\n" +
                " : , x\n" +
                " is not x\n" +
                " not in x\n" +
                " is x\n" +
                " in x\n" +
                " not x\n" +
                " or x\n" +
                " and x\n" +
                " same x\n" +
                " different x\n" +
                " not x\n" +
                " [ ] x\n" +
                " ( ) x\n" +
                " . x\n" +
                " > x\n" +
                " < x\n" +
                " >= x\n" +
                " <= x\n" +
                " = x\n" +
                " | x\n" +
                "\n";
        for (String name : names) {
            if (keywords.contains(name)) {
                Global.log.accept("The name '" + name + "' might be part of reserved keyword. If other errors appear try to rename it or use in quote marks.");
                continue;
            }

            if (Global.deepNamingCheck) {
                Pattern pattern = Pattern.compile("[\\d\\w]" + name + "[\\d\\w]|[\\d\\w]" + name + "|" + name + "[\\d\\w]");
                Matcher m = pattern.matcher(declare);
                if (m.find() && !name.contains(m.group(0)))
                    Global.log.accept("The name '" + name + "' might be part of reserved keyword. If other errors appear try to rename it or use in quote marks.");
            }
        }
    }

    public Map<String, String> getEncoding() {
        return namesEncoding;
    }
}
