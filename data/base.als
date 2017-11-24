abstract sig Task {}
abstract sig Payload {}

abstract sig TaskEvent{	// One event in trace
	task: one Task,		// Name of task
	data: set Payload,
	tokens: set Token	// Used only for 'same' or 'different' constraints on numeric data
}

one sig DummyPayload extends Payload {}
fact { no te:TaskEvent | DummyPayload in te.data }

abstract sig Token {}
abstract sig SameToken extends Token {}
abstract sig DiffToken extends Token {}
lone sig DummySToken extends SameToken{}
lone sig DummyDToken extends DiffToken{}
fact { 
	no DummySToken
	no DummyDToken
	all te:TaskEvent| no (te.tokens & SameToken) or no (te.tokens & DiffToken)
}

pred True[]{some TE0}

// declare templates

pred Init(taskA: Task) { 
	taskA = TE0.task
}

pred Existence(taskA: Task) { 
	some te: TaskEvent | te.task = taskA
}

pred Existence(taskA: Task, n: Int) {
	#{ te: TaskEvent | taskA in te.task } >= n
}

pred Absence(taskA: Task) { 
	no te: TaskEvent | te.task = taskA
}

pred Absence(taskA: Task, n: Int) {
	#{ te: TaskEvent | taskA in te.task } <= n
}

pred Exactly(taskA: Task, n: Int) {
	#{ te: TaskEvent | taskA in te.task } = n
}

pred Choice(taskA, taskB: Task) { 
	some te: TaskEvent | te.task = taskA or te.task = taskB
}

pred ExclusiveChoice(taskA, taskB: Task) { 
	some te: TaskEvent | te.task = taskA or te.task = taskB
	(no te: TaskEvent | taskA = te.task) or (no te: TaskEvent | taskB = te.task )
}

pred RespondedExistence(taskA, taskB: Task) {
	(some te: TaskEvent | taskA = te.task) implies (some ote: TaskEvent | taskB = ote.task)
}

pred Response(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | taskB = fte.task and After[te, fte])
}

pred AlternateResponse(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | taskB = fte.task and After[te, fte] and (no ite: TaskEvent | taskA = ite.task and After[te, ite] and After[ite, fte]))
}

pred ChainResponse(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | taskB = fte.task and Next[te, fte])
}

pred Precedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | taskB = fte.task and After[fte, te])
}

pred AlternatePrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | taskB = fte.task and After[fte, te] and (no ite: TaskEvent | taskA = ite.task and After[fte, ite] and After[ite, te]))
}

pred ChainPrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | taskB = fte.task and Next[fte, te])
}

pred NotRespondedExistence(taskA, taskB: Task) {
	(some te: TaskEvent | taskA = te.task) implies (no te: TaskEvent | taskB = te.task)
}

pred NotResponse(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | taskB = fte.task and After[te, fte])
}

pred NotPrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | taskB = fte.task and After[fte, te])
}

pred NotChainResponse(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | taskB = fte.task and Next[te, fte])
}

pred NotChainPrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | taskB = fte.task and Next[fte, te])
}
//-

pred example { }
run example

