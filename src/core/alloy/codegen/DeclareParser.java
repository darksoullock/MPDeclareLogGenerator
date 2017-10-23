package core.alloy.codegen;

import java.util.regex.Pattern;

/**
 * Created by Vasiliy on 2017-10-16.
 */
public class DeclareParser
{
    Pattern task = Pattern.compile("^\\s*\\w+\\s*$");

    public boolean isTask(String line)
    {
        return task.matcher(line).matches();
    }

    public boolean isTraceAttribute(String line)
    {
        return line.startsWith("trace ");
    }

    public boolean isData(String line)
    {
        return (line.contains(":") && !isDataBinding(line) || line.contains(" between ") )&& !isTraceAttribute(line);
    }

    public boolean isDataBinding(String line)
    {
        return line.startsWith("bind ");
    }

    public boolean isConstraint(String line)
    {
        return line.contains("[") && !isDataConstraint(line);
    }

    public boolean isDataConstraint(String line)
    {
        return line.contains("|");
    }

    public String[] SplitStatements(String code)
    {
        return code.replace("\r\n", "\n").split("\n");
    }
}