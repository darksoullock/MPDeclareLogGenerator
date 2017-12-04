abstract sig Activity {}
abstract sig Payload {}

abstract sig Event{	// One event in trace
	task: one Activity,		// Name of task
	data: set Payload,
	tokens: set Token	// Used only for 'same' or 'different' constraints on numeric data
}

one sig DummyPayload extends Payload {}
fact { no te:Event | DummyPayload in te.data }

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
	#{ te: Event | taskA in te.task } >= n
}

pred Absence(taskA: Activity) {
	no te: Event | te.task = taskA
}

pred Absence(taskA: Activity, n: Int) {
	#{ te: Event | taskA in te.task } <= n
}

pred Exactly(taskA: Activity, n: Int) {
	#{ te: Event | taskA in te.task } = n
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
	all te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and Next[te, fte])
}

pred NotChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and Next[fte, te])
}
//-

pred example { }
run example

