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
one sig TE3 extends Event {}
one sig TE4 extends Event {}
pred Next(pre, next: Event){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4}
pred After(b, a: Event){// b=before, a=after
b=TE0 or a=TE4 or b=TE1 and not (a=TE0) or b=TE2 and (a=TE4 or a=TE3)}
one sig A extends Activity {}
one sig B extends Activity {}
one sig C extends Activity {}
fact { all te: Event | te.task = C implies (one D & te.data)}
fact { all te: Event | lone(D & te.data) }
fact { all te: Event | some (D & te.data) implies te.task in (C) }
abstract sig D extends Payload {}
fact { all te: Event | (lone D & te.data)}
one sig val1 extends D{}
one sig val2 extends D{}
pred p100000(c1: Event) { { (c1.data&D=val1) } }
pred p100000c(c1, c2: Event) { { (c2.data&D=val2) } }
fact {
(not Init[A]) or not (Response[A,B]) or not (Existence[C]) or not (all te: Event | (C = te.task and p100000[te]) implies (some fte: Event | C = fte.task and Next[te, fte] and p100000c[te, fte]))
}

