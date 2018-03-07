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

one sig TE0 extends Event {}{not task=DummyActivity}
one sig TE1 extends Event {}{not task=DummyActivity}
one sig TE2 extends Event {}{not task=DummyActivity}
one sig TE3 extends Event {}{not task=DummyActivity}
one sig TE4 extends Event {}{not task=DummyActivity}
one sig TE5 extends Event {}{not task=DummyActivity}
one sig TE6 extends Event {}{not task=DummyActivity}
one sig TE7 extends Event {}{not task=DummyActivity}
one sig TE8 extends Event {}{not task=DummyActivity}
one sig TE9 extends Event {}{not task=DummyActivity}
pred Next(pre, next: Event){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4 or pre=TE4 and next=TE5 or pre=TE5 and next=TE6 or pre=TE6 and next=TE7 or pre=TE7 and next=TE8 or pre=TE8 and next=TE9}
pred After(b, a: Event){// b=before, a=after
b=TE0 or a=TE9 or b=TE1 and not (a=TE0) or b=TE2 and not (a=TE0 or a=TE1) or b=TE3 and not (a=TE0 or a=TE1 or a=TE2) or b=TE4 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3) or b=TE5 and (a=TE9 or a=TE8 or a=TE7 or a=TE6) or b=TE6 and (a=TE9 or a=TE8 or a=TE7) or b=TE7 and (a=TE9 or a=TE8)}
one sig SubmitLoanApplication extends Activity {}
one sig AssessApplication extends Activity {}
one sig CheckCareer extends Activity {}
one sig CheckMedicalHistory extends Activity {}
one sig NotifyOutcome extends Activity {}
fact { all te: Event | te.task = CheckCareer implies (one Coverage & te.data)}
fact { all te: Event | te.task = CheckMedicalHistory implies (one Cost & te.data)}
fact { all te: Event | lone(Coverage & te.data) }
fact { all te: Event | some (Coverage & te.data) implies te.task in (CheckCareer) }
fact { all te: Event | lone(Cost & te.data) }
fact { all te: Event | some (Cost & te.data) implies te.task in (CheckMedicalHistory) }
abstract sig Coverage extends Payload {
amount: Int
}
fact { all te: Event | (lone Coverage & te.data) }
pred Single(pl: Coverage) {{pl.amount=1}}
fun Amount(pl: Coverage): one Int {{pl.amount}}
one sig intBetweenm1and2r100036 extends Coverage{}{amount=2}
one sig intBetween1and5r100037 extends Coverage{}{amount=3}
one sig intBetween17and31r100040 extends Coverage{}{amount=13}
one sig intEqualsTo5r100038 extends Coverage{}{amount=1}
one sig intBetween5and18r100039 extends Coverage{}{amount=12}
abstract sig Cost extends Payload {
amount: Int
}
fact { all te: Event | (lone Cost & te.data) }
pred Single(pl: Cost) {{pl.amount=1}}
fun Amount(pl: Cost): one Int {{pl.amount}}
one sig intBetween53and99r100042 extends Cost{}{amount=15}
one sig intBetween9and54r100041 extends Cost{}{amount=15}
one sig intEqualsTo100r100043 extends Cost{}{amount=1}
one sig intBetween149and200r100045 extends Cost{}{amount=15}
one sig intBetween100and150r100044 extends Cost{}{amount=15}
pred p100046(A: Event) { { A.data&Coverage in (intBetweenm1and2r100036 + intBetween1and5r100037 + intEqualsTo5r100038) } }
pred p100046c(A, B: Event) { { B.data&Cost in (intBetween53and99r100042 + intBetween9and54r100041 + intEqualsTo100r100043) } }
pred p100047(A: Event) { { A.data&Coverage in (intBetween17and31r100040 + intBetween5and18r100039) } }
pred p100047c(A, B: Event) { { B.data&Cost in (intBetween149and200r100045 + intBetween100and150r100044) } }
fact {
Response[CheckCareer,CheckMedicalHistory]
Response[SubmitLoanApplication,AssessApplication]
Response[CheckMedicalHistory,NotifyOutcome]
Absence[AssessApplication,3]
Absence[CheckMedicalHistory,3]
all te: Event | (CheckCareer = te.task and p100046[te]) implies (some fte: Event | CheckMedicalHistory = fte.task and Next[te, fte] and p100046c[te, fte])
Absence[SubmitLoanApplication,3]
Response[AssessApplication,CheckCareer]
Absence[CheckMedicalHistory,1]
Absence[NotifyOutcome,3]
Absence[CheckCareer,3]
Exactly[CheckCareer,1]
all te: Event | (CheckCareer = te.task and p100047[te]) implies (some fte: Event | CheckMedicalHistory = fte.task and Next[te, fte] and p100047c[te, fte])
}

