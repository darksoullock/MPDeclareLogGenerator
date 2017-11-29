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

one sig TE0 extends TaskEvent {}
one sig TE1 extends TaskEvent {}
one sig TE2 extends TaskEvent {}
one sig TE3 extends TaskEvent {}
one sig TE4 extends TaskEvent {}
one sig TE5 extends TaskEvent {}
one sig TE6 extends TaskEvent {}
one sig TE7 extends TaskEvent {}
one sig TE8 extends TaskEvent {}
one sig TE9 extends TaskEvent {}
one sig TE10 extends TaskEvent {}
one sig TE11 extends TaskEvent {}
one sig TE12 extends TaskEvent {}
lone sig TE13 extends TaskEvent {}
lone sig TE14 extends TaskEvent {}
lone sig TE15 extends TaskEvent {}
lone sig TE16 extends TaskEvent {}
lone sig TE17 extends TaskEvent {}
lone sig TE18 extends TaskEvent {}
lone sig TE19 extends TaskEvent {}
pred Next(pre, next: TaskEvent){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4 or pre=TE4 and next=TE5 or pre=TE5 and next=TE6 or pre=TE6 and next=TE7 or pre=TE7 and next=TE8 or pre=TE8 and next=TE9 or pre=TE9 and next=TE10 or pre=TE10 and next=TE11 or pre=TE11 and next=TE12 or pre=TE12 and next=TE13 or pre=TE13 and next=TE14 or pre=TE14 and next=TE15 or pre=TE15 and next=TE16 or pre=TE16 and next=TE17 or pre=TE17 and next=TE18 or pre=TE18 and next=TE19}
pred After(b, a: TaskEvent){// b=before, a=after
b=TE0 or a=TE19 or b=TE1 and not (a=TE0) or b=TE2 and not (a=TE0 or a=TE1) or b=TE3 and not (a=TE0 or a=TE1 or a=TE2) or b=TE4 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3) or b=TE5 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4) or b=TE6 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5) or b=TE7 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6) or b=TE8 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7) or b=TE9 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7 or a=TE8) or b=TE10 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13 or a=TE12 or a=TE11) or b=TE11 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13 or a=TE12) or b=TE12 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13) or b=TE13 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14) or b=TE14 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15) or b=TE15 and (a=TE19 or a=TE18 or a=TE17 or a=TE16) or b=TE16 and (a=TE19 or a=TE18 or a=TE17) or b=TE17 and (a=TE19 or a=TE18)}
fact{
one TE14 implies one TE13
one TE15 implies one TE14
one TE16 implies one TE15
one TE17 implies one TE16
one TE18 implies one TE17
one TE19 implies one TE18
}
one sig x74dbf896x2bcfx48a9xa7ebx1120812f9008 extends Task {}
one sig x11161c40xb4a0x4f97xaf29xb507715cec43 extends Task {}
one sig x394e2891xba2fx4294x888fxfde080a59ea0 extends Task {}
one sig x06c60d1dx8057x4fb2xbe5bx73719cb7d2a0 extends Task {}
one sig xcf7c25e5x03cax4cd4xa7f6xe1a6e86fbd38 extends Task {}
one sig xe63161bcxaa72x47b0x9b01x49aaf53fcb25 extends Task {}
one sig xce568de4x6809x4260xb8ddx7bede33d6bb9 extends Task {}
one sig xd8a353e5x1010x4cd3x8342x2fdf63ff7898 extends Task {}
fact { all te: TaskEvent | te.task = x394e2891xba2fx4294x888fxfde080a59ea0 implies (one xdb119a88xb1a0x4818x9de1x51b562cae4cd & te.data and one x4d54d7d9x920ax4407xb56ex234a7f5b567c & te.data and one x95c3aba6xfa1dx4752x91bax8fae2fa87111 & te.data)}
fact { all te: TaskEvent | te.task = xce568de4x6809x4260xb8ddx7bede33d6bb9 implies (one xdb119a88xb1a0x4818x9de1x51b562cae4cd & te.data and one x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0 & te.data and one x4d54d7d9x920ax4407xb56ex234a7f5b567c & te.data)}
fact { all te: TaskEvent | te.task = xd8a353e5x1010x4cd3x8342x2fdf63ff7898 implies (one x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0 & te.data)}
fact { all te: TaskEvent | lone(xdb119a88xb1a0x4818x9de1x51b562cae4cd & te.data) }
fact { all te: TaskEvent | one (xdb119a88xb1a0x4818x9de1x51b562cae4cd & te.data) implies te.task in (x394e2891xba2fx4294x888fxfde080a59ea0 + xce568de4x6809x4260xb8ddx7bede33d6bb9) }
fact { all te: TaskEvent | lone(x4d54d7d9x920ax4407xb56ex234a7f5b567c & te.data) }
fact { all te: TaskEvent | one (x4d54d7d9x920ax4407xb56ex234a7f5b567c & te.data) implies te.task in (x394e2891xba2fx4294x888fxfde080a59ea0 + xce568de4x6809x4260xb8ddx7bede33d6bb9) }
fact { all te: TaskEvent | lone(x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0 & te.data) }
fact { all te: TaskEvent | one (x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0 & te.data) implies te.task in (xce568de4x6809x4260xb8ddx7bede33d6bb9 + xd8a353e5x1010x4cd3x8342x2fdf63ff7898) }
fact { all te: TaskEvent | lone(x95c3aba6xfa1dx4752x91bax8fae2fa87111 & te.data) }
fact { all te: TaskEvent | one (x95c3aba6xfa1dx4752x91bax8fae2fa87111 & te.data) implies te.task in (x394e2891xba2fx4294x888fxfde080a59ea0) }
fact {
Init[x74dbf896x2bcfx48a9xa7ebx1120812f9008]
Response[xcf7c25e5x03cax4cd4xa7f6xe1a6e86fbd38,xe63161bcxaa72x47b0x9b01x49aaf53fcb25]
Precedence[x394e2891xba2fx4294x888fxfde080a59ea0,x11161c40xb4a0x4f97xaf29xb507715cec43]
Precedence[x06c60d1dx8057x4fb2xbe5bx73719cb7d2a0,x11161c40xb4a0x4f97xaf29xb507715cec43]
Precedence[xcf7c25e5x03cax4cd4xa7f6xe1a6e86fbd38,x394e2891xba2fx4294x888fxfde080a59ea0]
Precedence[xcf7c25e5x03cax4cd4xa7f6xe1a6e86fbd38,x06c60d1dx8057x4fb2xbe5bx73719cb7d2a0]
Absence[x06c60d1dx8057x4fb2xbe5bx73719cb7d2a0,2]
Absence[x394e2891xba2fx4294x888fxfde080a59ea0,3]
Absence[x74dbf896x2bcfx48a9xa7ebx1120812f9008,1]
Existence[xcf7c25e5x03cax4cd4xa7f6xe1a6e86fbd38]
Existence[xe63161bcxaa72x47b0x9b01x49aaf53fcb25]
Absence[xe63161bcxaa72x47b0x9b01x49aaf53fcb25,1]
Absence[x11161c40xb4a0x4f97xaf29xb507715cec43,1]
ChainResponse[xd8a353e5x1010x4cd3x8342x2fdf63ff7898,xce568de4x6809x4260xb8ddx7bede33d6bb9]
Absence[xce568de4x6809x4260xb8ddx7bede33d6bb9,3]
Exactly[xd8a353e5x1010x4cd3x8342x2fdf63ff7898,3]
}
fact {
Existence[xcf7c25e5x03cax4cd4xa7f6xe1a6e86fbd38]
Existence[x394e2891xba2fx4294x888fxfde080a59ea0]
Existence[x06c60d1dx8057x4fb2xbe5bx73719cb7d2a0]
Existence[xd8a353e5x1010x4cd3x8342x2fdf63ff7898]
}
abstract sig xdb119a88xb1a0x4818x9de1x51b562cae4cd extends Payload {}
fact { all te: TaskEvent | (lone xdb119a88xb1a0x4818x9de1x51b562cae4cd & te.data)}
one sig x2807da6ex6527x461ex9a77xc3f3fb634df7 extends xdb119a88xb1a0x4818x9de1x51b562cae4cd{}
one sig x392aebcax5276x4bf2xa7cex0960cc88356e extends xdb119a88xb1a0x4818x9de1x51b562cae4cd{}
one sig xde4b0b04xc5cbx4d4fxbe8dxabbef233851b extends xdb119a88xb1a0x4818x9de1x51b562cae4cd{}
one sig xd8eb5a8ex25eax4e7dx8b4ex61be4e5a43d7 extends xdb119a88xb1a0x4818x9de1x51b562cae4cd{}
abstract sig x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0 extends Payload {}
fact { all te: TaskEvent | (lone x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0 & te.data)}
one sig x44dccc7dxe3f6x48f8xb03dx6cb2f7d4758b extends x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0{}
one sig xe3844050x354ex428bxac02x5e73faf5bc00 extends x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0{}
one sig x894b4534x8e8cx4ecbx81afxe0c17c2edba4 extends x3f53c9d6x663fx436fx8bd5xc1f6c951fdc0{}
abstract sig x4d54d7d9x920ax4407xb56ex234a7f5b567c extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x4d54d7d9x920ax4407xb56ex234a7f5b567c & te.data) }
pred Single(pl: x4d54d7d9x920ax4407xb56ex234a7f5b567c) {{pl.amount=1}}
fun Amount(pl: x4d54d7d9x920ax4407xb56ex234a7f5b567c): one Int {{pl.amount}}
one sig floatBetween25p0and50p0r100001 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=15}
one sig floatBetween80p0and90p0r100006 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=15}
one sig floatBetween50p0and65p0r100003 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=15}
one sig floatBetween65p0and80p0r100004 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=15}
one sig floatEqualsTo50p0r100002 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=1}
one sig floatBetween90p0and100p0r100007 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=15}
one sig floatBetween0p0and25p0r100000 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=15}
one sig floatEqualsTo80p0r100005 extends x4d54d7d9x920ax4407xb56ex234a7f5b567c{}{amount=1}
abstract sig x95c3aba6xfa1dx4752x91bax8fae2fa87111 extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x95c3aba6xfa1dx4752x91bax8fae2fa87111 & te.data) }
pred Single(pl: x95c3aba6xfa1dx4752x91bax8fae2fa87111) {{pl.amount=1}}
fun Amount(pl: x95c3aba6xfa1dx4752x91bax8fae2fa87111): one Int {{pl.amount}}
one sig intBetween50and176r100011 extends x95c3aba6xfa1dx4752x91bax8fae2fa87111{}{amount=15}
one sig intBetween175and301r100012 extends x95c3aba6xfa1dx4752x91bax8fae2fa87111{}{amount=15}
one sig intBetween24and50r100009 extends x95c3aba6xfa1dx4752x91bax8fae2fa87111{}{amount=15}
one sig intBetweenm1and25r100008 extends x95c3aba6xfa1dx4752x91bax8fae2fa87111{}{amount=15}
one sig intEqualsTo50r100010 extends x95c3aba6xfa1dx4752x91bax8fae2fa87111{}{amount=1}
fact { no te: TaskEvent | te.task = x394e2891xba2fx4294x888fxfde080a59ea0 and p100013[te] }
pred p100013(A: set TaskEvent) { { (A.data&x4d54d7d9x920ax4407xb56ex234a7f5b567c in (floatBetween80p0and90p0r100006 + floatBetween50p0and65p0r100003 + floatBetween65p0and80p0r100004 + floatBetween90p0and100p0r100007 + floatEqualsTo80p0r100005) and A.data&x95c3aba6xfa1dx4752x91bax8fae2fa87111 in (intBetween50and176r100011 + intBetween175and301r100012 + intEqualsTo50r100010)) } }
fact { all te: TaskEvent | (x394e2891xba2fx4294x888fxfde080a59ea0 = te.task and p100014[te]) implies (some ote: TaskEvent | UseasdTransport = ote.task and p100014c[te, ote]) }
pred p100014(A: set TaskEvent) { { A.data&x4d54d7d9x920ax4407xb56ex234a7f5b567c in (floatEqualsTo50p0r100002) } }
pred p100014c(A, B: set TaskEvent) { { B.data&x4d54d7d9x920ax4407xb56ex234a7f5b567c in (floatEqualsTo80p0r100005) } }
fact { some te: TaskEvent | te.task = x394e2891xba2fx4294x888fxfde080a59ea0 and p100014[te]} //vc

