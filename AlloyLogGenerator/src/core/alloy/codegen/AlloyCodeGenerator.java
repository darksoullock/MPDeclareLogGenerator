package core.alloy.codegen;

import core.Global;
import core.exceptions.GenerationException;
import core.helpers.RandomHelper;
import core.models.declare.data.EnumeratedDataImpl;
import core.models.declare.data.FloatDataImpl;
import core.models.declare.data.IntegerDataImpl;
import core.models.declare.data.NumericDataImpl;
import core.models.intervals.FloatInterval;
import core.models.intervals.IntegerInterval;
import core.models.intervals.Interval;
import core.models.intervals.IntervalSplit;
import declare.DeclareModel;
import declare.DeclareParserException;
import declare.fnparser.BinaryExpression;
import declare.fnparser.DataExpression;
import declare.fnparser.DataExpressionParser;
import declare.fnparser.Token;
import declare.lang.Activity;
import declare.lang.Constraint;
import declare.lang.DataConstraint;
import declare.lang.Statement;
import declare.lang.data.EnumeratedData;
import declare.lang.data.FloatData;
import declare.lang.data.IntegerData;
import org.apache.commons.lang3.tuple.Pair;
import org.deckfour.xes.model.XAttribute;
import org.deckfour.xes.model.XEvent;
import org.deckfour.xes.model.XTrace;
import org.deckfour.xes.model.impl.XAttributeContinuousImpl;
import org.deckfour.xes.model.impl.XAttributeDiscreteImpl;
import org.deckfour.xes.model.impl.XAttributeLiteralImpl;

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
    boolean shuffleConstraints;
    boolean writeConstraints;
    boolean usesSameConstraint;
    boolean dataQueryParamPresent;

    StringBuilder alloy;
    List<Pair<Statement, String>> alloyConstraints;
    Map<String, NumericDataImpl> numericData;
    DataConstraintGenerator gen;

    public AlloyCodeGenerator(int maxTraceLength, int minTraceLength, int bitwidth,
                              int maxSameInstances, boolean vacuity, boolean shuffleConstraints, boolean writeConstraints) {
        this.maxTraceLength = maxTraceLength;
        this.minTraceLength = minTraceLength;
        this.bitwidth = bitwidth;
        this.vacuity = vacuity;
        this.shuffleConstraints = shuffleConstraints;
        this.writeConstraints = writeConstraints;
        maxSameInstances = (int) Math.min(maxSameInstances, Math.pow(2, bitwidth));
        this.gen = new DataConstraintGenerator(maxSameInstances, bitwidth, vacuity);
        this.usesSameConstraint = maxSameInstances > 0;
    }

    public void Run(DeclareModel model, boolean negativeTraces, int intervalSplits, XTrace trace) throws DeclareParserException, GenerationException {

        alloy = new StringBuilder(GetBase());
        alloyConstraints = new ArrayList<>();
        if (trace != null && maxTraceLength < trace.size()) {
            maxTraceLength = trace.size();
        }

        List<EnumeratedDataImpl> data = collectData(model, intervalSplits);
        numericData = fillNumericDataMap(data);
        ExtendNumericData(getNumericExpressionsMap(model.getDataConstraints()));

        generateActivities(model.getActivities());
        GenerateEvents(maxTraceLength);
        GenerateNextPredicate(maxTraceLength);
        GenerateAfterPredicate(maxTraceLength);
        GenerateDataBinding(model.getActivityToData(), model.getDataToActivity());
        if (vacuity)
            generateVacuity(model.getConstraints());
        generateConstraints(model.getConstraints());
        GenerateData(data, shuffleConstraints);
        GenerateDataConstraints(model.getDataConstraints());
        if (shuffleConstraints)
            Collections.shuffle(alloyConstraints);
        if (writeConstraints)
            AttachConstraints(negativeTraces);
        GenerateTraceContent(trace, model);
    }

    private void GenerateTraceContent(XTrace trace, DeclareModel model) throws DeclareParserException {
        if (trace == null || trace.size() == 0) {
            return;
        }

        alloy.append("fact {\n");
        generateTraceFlow(trace, model);
        alloy.append("\n}\n");
    }

    private void generateTraceFlow(XTrace trace, DeclareModel model) throws DeclareParserException {
        int index = 0;

        for (XEvent event : trace) {
            XAttribute nameAttribute = event.getAttributes().get("concept:name");
            if (nameAttribute == null) {
                throw new DeclareParserException("Event name not found in " + event);
            }

            String activityName = ((XAttributeLiteralImpl) nameAttribute).getValue();
            alloy.append(activityName).append(" = TE").append(index).append(".task\n");

            for (String dataAttributeName : model.getActivityToData().getOrDefault(activityName, Collections.emptySet())) {
                XAttribute attribute = event.getAttributes().get(dataAttributeName);

                if (attribute == null) {
                    alloy.append("__").append(dataAttributeName).append("__no_value").append(" = TE").append(index).append(".data & ").append(dataAttributeName).append("\n");
                }

                if (attribute instanceof XAttributeLiteralImpl &&
                        model.getEnumeratedData().stream().anyMatch(i -> i.getType().equals(attribute.getKey()) && i.getValues().contains(((XAttributeLiteralImpl) attribute).getValue()))) {
                    alloy.append(((XAttributeLiteralImpl) attribute).getValue()).append(" = TE").append(index).append(".data & ").append(attribute.getKey()).append("\n");
                }

                if (attribute instanceof XAttributeDiscreteImpl) {
                    Optional<IntegerData> intData = model.getIntegerData().stream().filter(i -> i.getType().equals(attribute.getKey())).findAny();
                    if (intData.isPresent()) {
                        alloy.append(getIntervalFor(intData.get(), ((XAttributeDiscreteImpl) attribute).getValue())).append(" = TE").append(index).append(".data & ").append(attribute.getKey()).append("\n");
                    }
                }

                if (attribute instanceof XAttributeContinuousImpl) {
                    Optional<FloatData> floatData = model.getFloatData().stream().filter(i -> i.getType().equals(attribute.getKey())).findAny();
                    if (floatData.isPresent())
                        alloy.append(getIntervalFor(floatData.get(), ((XAttributeContinuousImpl) attribute).getValue())).append(" = TE").append(index).append(".data & ").append(attribute.getKey()).append("\n");
                }
            }

            ++index;
        }
    }

    private String getIntervalFor(IntegerData integerData, long attributeValue) throws DeclareParserException {
        NumericDataImpl numericData = this.numericData.get(integerData.getType());
        return numericData.getMapping().entrySet().stream().filter(i -> ((IntegerInterval) i.getValue()).isIn((int) attributeValue)).map(Map.Entry::getKey).findAny()
                .orElseThrow(() -> new DeclareParserException("no interval for " + integerData.getType() + " = " + attributeValue));
    }

    private String getIntervalFor(FloatData floatData, double attributeValue) throws DeclareParserException {
        NumericDataImpl numericData = this.numericData.get(floatData.getType());
        return numericData.getMapping().entrySet().stream().filter(i -> ((FloatInterval) i.getValue()).isIn((int) attributeValue)).map(Map.Entry::getKey).findAny()
                .orElseThrow(() -> new DeclareParserException("no interval for " + floatData.getType() + " = " + attributeValue));
    }

    public Map<String, NumericDataImpl> getNumericData() {
        return numericData;
    }

    public List<EnumeratedDataImpl> collectData(DeclareModel model, int intervalSplits) {
        List<EnumeratedDataImpl> data = new ArrayList<>(model.getEnumeratedData().size() +
                model.getIntegerData().size() + model.getFloatData().size());

        for (EnumeratedData i : model.getEnumeratedData()) {
            data.add(new EnumeratedDataImpl(i.getType(), i.getValues(), i.isRequired()));
        }

        for (IntegerData i : model.getIntegerData()) {
            data.add(new IntegerDataImpl(i.getType(), i.getMin(), i.getMax(), intervalSplits, null, i.isRequired()));
        }

        for (FloatData i : model.getFloatData()) {
            data.add(new FloatDataImpl(i.getType(), i.getMin(), i.getMax(), intervalSplits, null, i.isRequired()));
        }

        return data;
    }

    public Map<String, NumericDataImpl> fillNumericDataMap(List<EnumeratedDataImpl> data) {
        Map<String, NumericDataImpl> map = new HashMap<>();
        for (EnumeratedDataImpl item : data)
            if (item instanceof NumericDataImpl)
                map.put(item.getType(), (NumericDataImpl) item);

        return map;
    }

    public List<Pair<Statement, String>> getAlloyConstraints() {
        return alloyConstraints;
    }

    private Map<String, List<DataExpression>> getNumericExpressionsMap(List<DataConstraint> dataConstraints) throws DeclareParserException {
        Map<String, List<DataExpression>> numericExpressions = new HashMap<>();
        DataExpressionParser expressionParser = new DataExpressionParser();
        for (DataConstraint i : dataConstraints) {
            expressionParser.retrieveNumericExpressions(numericExpressions, i.getFirstFunction().getExpression());
            if (i.hasSecondFunction())
                expressionParser.retrieveNumericExpressions(numericExpressions, i.getSecondFunction().getExpression());
        }

        return numericExpressions;
    }

    private void AttachConstraints(boolean negativeTraces) {
        List<String> alloyConstraintsValues = alloyConstraints.stream().map(Pair::getValue).collect(Collectors.toList());
        if (negativeTraces)
            alloy.append("fact {\n").append("(not ").append(String.join(") or not (", alloyConstraintsValues)).append(")\n}\n");
        else
            alloy.append("fact {\n").append(String.join("\n", alloyConstraintsValues)).append("\n}\n");
    }

    public String getAlloyCode() {
        if (alloy != null)
            return alloy.toString();
        return null;
    }

    public Map<String, Interval> generateNumericMap() {
        Map<String, Interval> map = new HashMap<>();
        for (NumericDataImpl ed : numericData.values())
            for (String i : ed.getMapping().keySet())
                map.put(i, ed.getMapping().get(i));

        return map;
    }

    private void GenerateDataConstraints(List<DataConstraint> dataConstraints) throws GenerationException, DeclareParserException {
        for (DataConstraint i : dataConstraints) {
            try {
                alloy.append(gen.Generate(i, getRandomFunctionName(), numericData, alloyConstraints));
            } catch (IndexOutOfBoundsException ex) {
                Global.log.accept("Did you define variable for data constraint (e.g. Existence[Task A]|A.value>1 instead of Existence[Task]|A.value>1)");
                Global.log.accept("at line " + i.getStatement().getLine() + ":\n" + ex.getMessage());
                throw ex;
            }
        }
    }

    private void generateConstraints(List<Constraint> constraints) throws DeclareParserException {
        Set<String> supported = Global.getAlloySupportedConstraints();
        for (Constraint i : constraints) {
            if (!supported.contains(i.getName()))
                throw new DeclareParserException("at line " + i.getStatement().getLine() + ":\nConstraint '" + i.getName() +
                        "' is not supported by Alloy. \nSupported constraints are: " + String.join(", ", supported) +
                        "\nIf the name in error different from the model source code, and part of it replaced with random sequence, " +
                        "then some of the short names you used might be part of keywords (like the name of constraint). " +
                        "Try to enclose such names in single quotes, 'like this'");

            if (i.isBinary())
                alloyConstraints.add(Pair.of(i.getStatement(), String.format("%s[%s,%s]", i.getName(), i.taskA(), i.taskB())));
            else
                alloyConstraints.add(Pair.of(i.getStatement(), String.format("%s[%s]", i.getName(), i.taskA())));
        }
    }


    private void generateVacuity(List<Constraint> constraints) {
        alloy.append("fact {\n");
        for (String i : constraints.stream().filter(x -> x.supportsVacuity()).map(x -> x.taskA()).distinct().collect(Collectors.toList()))
            alloy.append("Existence[").append(i).append("]\n");

        alloy.append("}\n");
    }

    private String getRandomFunctionName() {
        return "p" + RandomHelper.getNext();
    }

    private void ExtendNumericData(Map<String, List<DataExpression>> numericExpressions) throws DeclareParserException, GenerationException {
        for (NumericDataImpl d : numericData.values())
            if (numericExpressions.containsKey(d.getType()))
                for (DataExpression i : numericExpressions.get(d.getType()))
                    d.addSplit(getSplitNumberFromComparison((BinaryExpression) i));
    }

    private IntervalSplit getSplitNumberFromComparison(BinaryExpression ex) throws DeclareParserException {
        String value = null;
        boolean numberLeft = false;
        if (ex.getLeft().getNode().getType() == Token.Type.Number) {
            value = ex.getLeft().getNode().getValue();
            numberLeft = true;
        }

        if (ex.getRight().getNode().getType() == Token.Type.Number) {
            value = ex.getRight().getNode().getValue();
        }

        if (value == null)
            throw new DeclareParserException("No number in comparison operator: " + ex.toString());

        String token = ex.getNode().getValue();
        if (token.equals("="))
            return new IntervalSplit(value);

        if (token.equals("<") || token.equals(">="))
            return new IntervalSplit(value, numberLeft ? IntervalSplit.SplitSide.RIGHT : IntervalSplit.SplitSide.LEFT);

        if (token.equals(">") || token.equals("<="))
            return new IntervalSplit(value, numberLeft ? IntervalSplit.SplitSide.LEFT : IntervalSplit.SplitSide.RIGHT);

        throw new DeclareParserException("Unknown token " + token + "\n" + ex.toString());
    }

    private void GenerateData(List<EnumeratedDataImpl> data, boolean shuffle) {
        if (shuffle)
            Collections.shuffle(data);

        for (EnumeratedDataImpl item : data) {
            if (item instanceof NumericDataImpl) {
                GenerateNumericDataItem((NumericDataImpl) item, usesSameConstraint);
                continue;
            }
            alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {}\n");
            alloy.append("fact { all te: Event | (lone ").append(item.getType()).append(" & te.data)}\n");

            if (shuffle)
                Collections.shuffle(item.getValues());

            for (String value : item.getValues()) {
                alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}\n");
            }

            if (!item.isRequired()) {
                alloy.append("one sig ").append("__").append(item.getType()).append("__no_value").append(" extends ").append(item.getType()).append("{}\n");
            }
        }
    }

    private void GenerateNumericDataItem(NumericDataImpl item, boolean includeAmountOfPossibleValuesVariable) {
        alloy.append("abstract sig ").append(item.getType()).append(" extends Payload {");
        if (includeAmountOfPossibleValuesVariable)
            alloy.append("\n__amount: Int\n");
        alloy.append("}\n");

        alloy.append("fact { all te: Event | (lone ").append(item.getType()).append(" & te.data) }\n");
        if (includeAmountOfPossibleValuesVariable) {
            alloy.append("pred Single(pl: ").append(item.getType()).append(") {{pl.__amount=1}}\n");
            alloy.append("fun __Amount(pl: ").append(item.getType()).append("): one Int {{pl.__amount}}\n");
        }

        int limit = (int) Math.pow(2, bitwidth - 1);
        for (String value : item.getValues()) {
            if (includeAmountOfPossibleValuesVariable) {

                int cnt = item.getMapping().get(value).getValueCount(limit);
                if (cnt < 0)
                    cnt = limit - 1;
                alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}{__amount=").append(cnt).append("}\n");
            } else {
                alloy.append("one sig ").append(value).append(" extends ").append(item.getType()).append("{}\n");
            }
        }

        if (!item.isRequired()) {
            alloy.append("one sig ").append("__").append(item.getType()).append("__no_value").append(" extends ").append(item.getType()).append("{}\n");
        }
    }

    private void generateActivities(Set<Activity> tasks) {
        ArrayList<Activity> taskList = new ArrayList<>(tasks);
        if (shuffleConstraints)
            Collections.shuffle(taskList);

        for (Activity i : taskList)
            alloy.append("one sig ").append(i.getName()).append(" extends Activity {}\n");
    }

    private void GenerateEvents(int length) {
        for (int i = 0; i < length; i++) {
            if (i < minTraceLength)
                alloy.append("one sig TE").append(i).append(" extends Event {}{not task=DummyActivity}\n");
            else
                alloy.append("one sig TE").append(i).append(" extends Event {}\n");
        }
    }


    private void GenerateNextPredicate(int length) {
        alloy.append("pred Next(pre, next: Event){");
        alloy.append("pre=TE0 and next=TE1");
        for (int i = 2; i < length; i++) {
            alloy.append(" or pre=TE").append(i - 1).append(" and next=TE").append(i);
        }

        alloy.append("}\n");
    }

    private void GenerateAfterPredicate(int length) {
        alloy.append("pred After(b, a: Event){// b=before, a=after\n");
        int middle = length / 2;
        for (int i = 0; i < length - 1; ++i) {
            if (i > 0) {
                alloy.append(" or ");
            }

            alloy.append("b=TE").append(i).append(" and ");
            if (i < middle) {
                alloy.append("not (a=TE").append(i);
                for (int j = 0; j < i; ++j) {
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

    private void GenerateDataBinding(Map<String, Set<String>> activityToData, Map<String, Set<String>> dataToActivity) {
        GenerateDataBinding(activityToData, dataToActivity, "Event");
    }

    public void generateDataBindingForQuerying(Map<String, Set<String>> activityToData, Map<String, Set<String>> dataToActivity) {
        if (dataQueryParamPresent)
            GenerateDataBinding(activityToData, dataToActivity, "QueryParam");
    }

    private void GenerateDataBinding(Map<String, Set<String>> activityToData, Map<String, Set<String>> dataToActivity, String eventPlaceholderName) {
        for (String activity : activityToData.keySet()) {
            alloy.append("fact { all te: ").append(eventPlaceholderName).append(" | te.task = ")
                    .append(activity)
                    .append(" implies (one ")
                    .append(String.join(" & te.data and one ", activityToData.get(activity)))
                    .append(" & te.data")
                    .append(")}\n");
        }

        for (String payload : dataToActivity.keySet()) {
            alloy.append("fact { all te: ").append(eventPlaceholderName).append(" | some (")
                    .append(payload)
                    .append(" & te.data) implies te.task in (")
                    .append(String.join(" + ", dataToActivity.get(payload)))
                    .append(") }\n");
        }
    }

    // has to be called before GenerateDataBinding(..., QueryParam)
    public void generateQueryPlaceholder(Map<String, String> names, Set<String> dataParams) {
        dataQueryParamPresent = false;
        boolean taskQueryParamPresent = false;

        for (Map.Entry<String, String> name : names.entrySet()) {
            if (dataParams.contains(name.getKey())) {
                alloy.append("one sig ").append(name.getValue()).append(" extends QueryParam {}\n");
                dataQueryParamPresent = true;
            } else {
                alloy.append("one sig ").append(name.getValue()).append(" extends TaskQueryParam {}\n");
                taskQueryParamPresent = true;
            }

        }

        if (taskQueryParamPresent) {
            alloy.append("abstract sig TaskQueryParam{\n" +
                    "\ttask: one Activity,\n" +
                    "}\n");

            alloy.append("fact {\n" +
                    "no qp: TaskQueryParam | qp.task = DummyActivity\n" +
                    "}\n");

        }

        if (dataQueryParamPresent) {
            alloy.append("abstract sig QueryParam{\n" +
                    "\ttask: one Activity,\n" +
                    "\tdata: set Payload\n" +
                    "}\n");

            alloy.append("fact {\n" +
                    "no qp: QueryParam | qp.task = DummyActivity\n" +
                    "no te: QueryParam | DummyPayload in te.data\n" +
                    "}\n");
        }
    }

    private String GetBase() {
        return "abstract sig Activity {}\n" +
                "abstract sig Payload {}\n" +
                "\n" +
                "abstract sig Event{\n" +
                "\ttask: one Activity,\n" +
                "\tdata: set Payload,\n" +
                "\ttokens: set Token\n" +
                "}\n" +
                "\n" +
                "one sig DummyPayload extends Payload {}\n" +
                "fact { no te:Event | DummyPayload in te.data }\n" +
                "\n" +
                "one sig DummyActivity extends Activity {}\n" +
                "\n" +
                "abstract sig Token {}\n" +
                "abstract sig SameToken extends Token {}\n" +
                "abstract sig DiffToken extends Token {}\n" +
                "lone sig DummySToken extends SameToken{}\n" +
                "lone sig DummyDToken extends DiffToken{}\n" +
                "fact { \n" +
                "\tno DummySToken\n" +
                "\tno DummyDToken\n" +
                "\tall te:Event| no (te.tokens & SameToken) or no (te.tokens & DiffToken)\n" +
                "}\n" +
                "\n" +
                "pred True[]{some TE0}\n" +
                "\n" +
                "// lang templates\n" +
                "\n" +
                "pred Init(taskA: Activity) { \n" +
                "\ttaskA = TE0.task\n" +
                "}\n" +
                "\n" +
                "pred Existence(taskA: Activity) { \n" +
                "\tsome te: Event | te.task = taskA\n" +
                "}\n" +
                "\n" +
                "pred Existence(taskA: Activity, n: Int) {\n" +
                "\t#{ te: Event | taskA = te.task } >= n\n" +
                "}\n" +
                "\n" +
                "pred Absence(taskA: Activity) { \n" +
                "\tno te: Event | te.task = taskA\n" +
                "}\n" +
                "\n" +
                "pred Absence(taskA: Activity, n: Int) {\n" +
                "\t#{ te: Event | taskA = te.task } <= n\n" +
                "}\n" +
                "\n" +
                "pred Exactly(taskA: Activity, n: Int) {\n" +
                "\t#{ te: Event | taskA = te.task } = n\n" +
                "}\n" +
                "\n" +
                "pred Choice(taskA, taskB: Activity) { \n" +
                "\tsome te: Event | te.task = taskA or te.task = taskB\n" +
                "}\n" +
                "\n" +
                "pred ExclusiveChoice(taskA, taskB: Activity) { \n" +
                "\tsome te: Event | te.task = taskA or te.task = taskB\n" +
                "\t(no te: Event | taskA = te.task) or (no te: Event | taskB = te.task )\n" +
                "}\n" +
                "\n" +
                "pred RespondedExistence(taskA, taskB: Activity) {\n" +
                "\t(some te: Event | taskA = te.task) implies (some ote: Event | taskB = ote.task)\n" +
                "}\n" +
                "\n" +
                "pred Response(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred AlternateResponse(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte] and (no ite: Event | taskA = ite.task and After[te, ite] and After[ite, fte]))\n" +
                "}\n" +
                "\n" +
                "pred ChainResponse(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred Precedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te])\n" +
                "}\n" +
                "\n" +
                "pred AlternatePrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te] and (no ite: Event | taskA = ite.task and After[fte, ite] and After[ite, te]))\n" +
                "}\n" +
                "\n" +
                "pred ChainPrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[fte, te])\n" +
                "}\n" +
                "\n" +
                "pred NotRespondedExistence(taskA, taskB: Activity) {\n" +
                "\t(some te: Event | taskA = te.task) implies (no te: Event | taskB = te.task)\n" +
                "}\n" +
                "\n" +
                "pred NotResponse(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred NotPrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[fte, te])\n" +
                "}\n" +
                "\n" +
                "pred NotChainResponse(taskA, taskB: Activity) { \n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[te, fte])\n" +
                "}\n" +
                "\n" +
                "pred NotChainPrecedence(taskA, taskB: Activity) {\n" +
                "\tall te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[fte, te])\n" +
                "}\n" +
                "//-\n" +
                "\n" +
                "pred example { }\n" +
                "run example\n" +
                "\n---------------------- end of static code block ----------------------\n" +
                "\n--------------------- generated code starts here ---------------------\n\n";
        //return IOHelper.readAllText("./data/base.als");
    }
}
