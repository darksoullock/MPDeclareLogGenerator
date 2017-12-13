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
pred Next(pre, next: Event){pre=TE0 and next=TE1 or pre=TE1 and next=TE2}
pred After(b, a: Event){// b=before, a=after
b=TE0 or a=TE2}
one sig A extends Activity {}
one sig B extends Activity {}
fact { all te: Event | te.task = A implies (one C & te.data)}
fact { all te: Event | te.task = B implies (one C & te.data)}
fact { all te: Event | lone(C & te.data) }
fact { all te: Event | some (C & te.data) implies te.task in (A + B) }
fact {
Init[A]
}
abstract sig C extends Payload {
amount: Int
}
fact { all te: Event | (lone C & te.data) }
pred Single(pl: C) {{pl.amount=1}}
fun Amount(pl: C): one Int {{pl.amount}}
one sig intBetweenm1and101r100006 extends C{}{amount=15}
fact { all te: Event | (A = te.task and p100007[te]) implies (some fte: Event | B = fte.task and p100007c[te, fte] and After[te, fte])}
pred p100007(A: Event) { { True[] } }
pred p100007c(A, B: Event) { { (not A.data&C=B.data&C) or (A.data&C=B.data&C and one (DiffC100008 & B.tokens) and (DiffC100008 & A.tokens) = (DiffC100008 & B.tokens))  } }
abstract sig DiffC100008 extends DiffToken {}
fact { all te:Event | (some DiffC100008 & te.tokens) implies (some C&te.data) and not Single[C&te.data] }
fact { all te:Event| some (te.data&C) implies #{te.tokens&DiffC100008}<Amount[te.data&C]}
one sig DiffC100008i0 extends DiffC100008 {}
fact { all te: Event | DiffC100008i0 in te.tokens implies (one ote: Event | not ote = te and DiffC100008i0 in ote.tokens) }
one sig DiffC100008i1 extends DiffC100008 {}
fact { all te: Event | DiffC100008i1 in te.tokens implies (one ote: Event | not ote = te and DiffC100008i1 in ote.tokens) }
fact { all te: Event | (A = te.task and p100009[te]) implies (some fte: Event | B = fte.task and Next[te, fte] and p100009c[te, fte])}
pred p100009(A: Event) { { True[] } }
pred p100009c(A, B: Event) { { (A.data&C=B.data&C and ((one (SameC100010 & A.tokens)  and (SameC100010 & A.tokens) = (SameC100010 & B.tokens)) )) } }
abstract sig SameC100010 extends SameToken {}
one sig SameC100010i0 extends SameC100010 {}
fact {
all te: Event | SameC100010i0 in te.tokens implies (one ote: Event | not ote = te and SameC100010i0 in ote.tokens)
}
one sig SameC100010i1 extends SameC100010 {}
fact {
all te: Event | SameC100010i1 in te.tokens implies (one ote: Event | not ote = te and SameC100010i1 in ote.tokens)
}
fact {
all te: Event | (te.task = A or te.task = B or no (SameC100010 & te.tokens))
some te: Event | SameC100010 in te.tokens implies (all ote: Event| SameC100010 in ote.tokens implies ote.data&C = te.data&C)
}

