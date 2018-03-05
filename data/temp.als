abstract sig Activity {}
abstract sig Payload {}

abstract sig Event{
	task: one Activity,
	data: set Payload,
	tokens: set Token
}

one sig DummyPayload extends Payload {}
fact { no te:Event | DummyPayload in te.data }

one sig DummyActivity extends Activity {}

abstract sig Token {}
abstract sig SameToken extends Token {}
abstract sig DiffToken extends Token {}
lone sig DummySToken extends SameToken{}
lone sig DummyDToken extends DiffToken{}
fact { 
	no DummySToken
	no DummyDToken
	all te:Event| no (te.tokens & SameToken) or no (te.tokens & DiffToken)
}

pred True[]{some TE0}

// declare templates

pred Init(taskA: Activity) { 
	taskA = TE0.task
}

pred Existence(taskA: Activity) { 
	some te: Event | te.task = taskA
}

pred Existence(taskA: Activity, n: Int) {
	#{ te: Event | taskA = te.task } >= n
}

pred Absence(taskA: Activity) { 
	no te: Event | te.task = taskA
}

pred Absence(taskA: Activity, n: Int) {
	#{ te: Event | taskA = te.task } <= n
}

pred Exactly(taskA: Activity, n: Int) {
	#{ te: Event | taskA = te.task } = n
}

pred Choice(taskA, taskB: Activity) { 
	some te: Event | te.task = taskA or te.task = taskB
}

pred ExclusiveChoice(taskA, taskB: Activity) { 
	some te: Event | te.task = taskA or te.task = taskB
	(no te: Event | taskA = te.task) or (no te: Event | taskB = te.task )
}

pred RespondedExistence(taskA, taskB: Activity) {
	(some te: Event | taskA = te.task) implies (some ote: Event | taskB = ote.task)
}

pred Response(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte])
}

pred AlternateResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte] and (no ite: Event | taskA = ite.task and After[te, ite] and After[ite, fte]))
}

pred ChainResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[te, fte])
}

pred Precedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te])
}

pred AlternatePrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te] and (no ite: Event | taskA = ite.task and After[fte, ite] and After[ite, te]))
}

pred ChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[fte, te])
}

pred NotRespondedExistence(taskA, taskB: Activity) {
	(some te: Event | taskA = te.task) implies (no te: Event | taskB = te.task)
}

pred NotResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[te, fte])
}

pred NotPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[fte, te])
}

pred NotChainResponse(taskA, taskB: Activity) { 
	all te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[te, fte])
}

pred NotChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[fte, te])
}
//-

pred example { }
run example

---------------------- end of static code block ----------------------

--------------------- generated code starts here ---------------------

one sig TE0 extends Event {}
one sig TE1 extends Event {}
one sig TE2 extends Event {}
one sig TE3 extends Event {}
one sig TE4 extends Event {}
pred Next(pre, next: Event){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4}
pred After(b, a: Event){// b=before, a=after
b=TE0 or a=TE4 or b=TE1 and not (a=TE0) or b=TE2 and (a=TE4 or a=TE3)}
one sig SubmitLoanApplication extends Activity {}
one sig AssessApplication extends Activity {}
one sig CheckCareer extends Activity {}
one sig CheckMedicalHistory extends Activity {}
one sig NotifyOutcome extends Activity {}
fact { all te: Event | te.task = NotifyOutcome implies (one Result & te.data)}
fact { all te: Event | te.task = SubmitLoanApplication implies (one Salary & te.data and one Amount & te.data)}
fact { all te: Event | te.task = AssessApplication implies (one AssessmentType & te.data and one AssessmentCost & te.data)}
fact { all te: Event | lone(Salary & te.data) }
fact { all te: Event | some (Salary & te.data) implies te.task in (SubmitLoanApplication) }
fact { all te: Event | lone(AssessmentCost & te.data) }
fact { all te: Event | some (AssessmentCost & te.data) implies te.task in (AssessApplication) }
fact { all te: Event | lone(Amount & te.data) }
fact { all te: Event | some (Amount & te.data) implies te.task in (SubmitLoanApplication) }
fact { all te: Event | lone(AssessmentType & te.data) }
fact { all te: Event | some (AssessmentType & te.data) implies te.task in (AssessApplication) }
fact { all te: Event | lone(Result & te.data) }
fact { all te: Event | some (Result & te.data) implies te.task in (NotifyOutcome) }
abstract sig Salary extends Payload {
amount: Int
}
fact { all te: Event | (lone Salary & te.data) }
pred Single(pl: Salary) {{pl.amount=1}}
fun Amount(pl: Salary): one Int {{pl.amount}}
one sig intBetween17005and24012r100004 extends Salary{}{amount=15}
one sig intEqualsTo24000r100005 extends Salary{}{amount=1}
one sig intBetween24000and62039r100006 extends Salary{}{amount=15}
one sig intEqualsTo10000r100002 extends Salary{}{amount=1}
one sig intBetween999and5504r100000 extends Salary{}{amount=15}
one sig intBetween62038and100077r100007 extends Salary{}{amount=15}
one sig intBetween5503and10009r100001 extends Salary{}{amount=15}
one sig intBetween10000and17006r100003 extends Salary{}{amount=15}
abstract sig Amount extends Payload {
amount: Int
}
fact { all te: Event | (lone Amount & te.data) }
pred Single(pl: Amount) {{pl.amount=1}}
fun Amount(pl: Amount): one Int {{pl.amount}}
one sig intBetween30019and50040r100009 extends Amount{}{amount=15}
one sig intEqualsTo50000r100010 extends Amount{}{amount=1}
one sig intBetween75024and100049r100012 extends Amount{}{amount=15}
one sig intEqualsTo100000r100013 extends Amount{}{amount=1}
one sig intBetween9999and30020r100008 extends Amount{}{amount=15}
one sig intBetween100000and300201r100014 extends Amount{}{amount=15}
one sig intBetween50000and75025r100011 extends Amount{}{amount=15}
one sig intBetween300200and500401r100015 extends Amount{}{amount=15}
abstract sig AssessmentType extends Payload {}
fact { all te: Event | (lone AssessmentType & te.data)}
one sig Simple extends AssessmentType{}
one sig Complex extends AssessmentType{}
abstract sig AssessmentCost extends Payload {
amount: Int
}
fact { all te: Event | (lone AssessmentCost & te.data) }
pred Single(pl: AssessmentCost) {{pl.amount=1}}
fun Amount(pl: AssessmentCost): one Int {{pl.amount}}
one sig intBetween49and100r100017 extends AssessmentCost{}{amount=15}
one sig intEqualsTo100r100018 extends AssessmentCost{}{amount=1}
one sig intBetween100and301r100019 extends AssessmentCost{}{amount=15}
one sig intBetween300and501r100020 extends AssessmentCost{}{amount=15}
one sig intBetweenm1and50r100016 extends AssessmentCost{}{amount=15}
abstract sig Result extends Payload {}
fact { all te: Event | (lone Result & te.data)}
one sig Accepted extends Result{}
one sig Rejected extends Result{}
pred p100021(A: Event) { { ((not (A.data&Salary in (intEqualsTo24000r100005 + intEqualsTo10000r100002 + intBetween999and5504r100000 + intBetween5503and10009r100001 + intBetween10000and17006r100003)) or not (A.data&Amount in (intBetween75024and100049r100012 + intEqualsTo100000r100013 + intBetween100000and300201r100014 + intBetween50000and75025r100011 + intBetween300200and500401r100015))) and (not (A.data&Amount in (intBetween100000and300201r100014 + intBetween300200and500401r100015)) and not (A.data&Salary in (intBetween999and5504r100000)))) } }
pred p100021c(A, B: Event) { { ((B.data&AssessmentType=Simple) and B.data&AssessmentCost in (intBetween49and100r100017 + intEqualsTo100r100018 + intBetweenm1and50r100016)) } }
pred p100022(A: Event) { { A.data&Salary in (intBetween999and5504r100000) } }
pred p100022c(A, B: set Event) { { True[] } }
fact {
TE0.task = SubmitLoanApplication
TE1.task = AssessApplication or TE1.task = DummyActivity
TE2.task = CheckCareer
TE3.task = CheckMedicalHistory
TE4.task = NotifyOutcome
all te: Event | (SubmitLoanApplication = te.task and p100021[te]) implies (some fte: Event | AssessApplication = fte.task and p100021c[te, fte] and After[te, fte])
all te: Event | (SubmitLoanApplication = te.task and p100022[te]) implies (no fte: Event | AssessApplication = fte.task and p100022c[te, fte] and After[te, fte])
}

