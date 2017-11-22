abstract sig Task {}
abstract sig Payload {}

abstract sig TaskEvent{
	task: one Task,
	data: set Payload,
	tokens: set Token
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

// declare templates

pred Init(taskA: Task) { 
	one te: TaskEvent | taskA = te.task and te = TE0
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
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | After[te, fte] and taskB = fte.task )
}

pred AlternateResponse(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | After[te, fte] and taskB = fte.task and (no ite: TaskEvent | After[te, ite] and After[ite, fte] and taskA = ite.task))
}

pred ChainResponse(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | Next[te, fte] and taskB = fte.task)
}

pred Precedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | After[fte, te] and taskB = fte.task)
}

pred AlternatePrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | After[fte, te] and taskB = fte.task and (no ite: TaskEvent | After[fte, ite] and After[ite, te] and taskA = ite.task))
}

pred ChainPrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (some fte: TaskEvent | Next[fte, te] and taskB = fte.task)
}

pred NotRespondedExistence(taskA, taskB: Task) {
	(some te: TaskEvent | taskA = te.task) implies (no te: TaskEvent | taskB = te.task)
}

pred NotResponse(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | After[te, fte] and taskB = fte.task)
}

pred NotPrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | After[fte, te] and taskB = fte.task)
}

pred NotChainResponse(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | Next[te, fte] and taskB = fte.task)
}

pred NotChainPrecedence(taskA, taskB: Task) {
	all te: TaskEvent | taskA = te.task implies (no fte: TaskEvent | Next[fte, te] and taskB = fte.task)
}
//-

pred example { }
run example

one sig TE0 extends TaskEvent {}
one sig TE1 extends TaskEvent {}
one sig TE2 extends TaskEvent {}
one sig TE3 extends TaskEvent {}
one sig TE4 extends TaskEvent {}
lone sig TE5 extends TaskEvent {}
lone sig TE6 extends TaskEvent {}
lone sig TE7 extends TaskEvent {}
pred Next(pre, next: TaskEvent){
pre = TE0 and next = TE1 or pre = TE1 and next = TE2 or pre = TE2 and next = TE3 or pre = TE3 and next = TE4 or pre = TE4 and next = TE5 or pre = TE5 and next = TE6 or pre = TE6 and next = TE7}
pred After(b, a: TaskEvent){// b=before, a=after
b=TE0 or a=TE7 or b=TE1 and not (a=TE0) or b=TE2 and not (a=TE0 or a=TE1) or b=TE3 and not (a=TE0 or a=TE1 or a=TE2) or b=TE4 and (a=TE7 or a=TE6 or a=TE5) or b=TE5 and (a=TE7 or a=TE6)}
fact{
one TE6 implies one TE5
one TE7 implies one TE6
}
one sig x272111bcx5a52x4ab7x81acxa2d86fa77c44 extends Task {}
one sig xa47d9947x0cbex477ex81a2x02461098da2f extends Task {}
one sig xe829e492x7226x4ed5x815exbb17614aa050 extends Task {}
one sig x6ae64eedx0736x4f8bx98c9xe2f5b69f11fe extends Task {}
one sig xa1cfeb64x44ecx4488xa5c0x220fbb37ed06 extends Task {}
one sig x7eaf35acx299bx43faxb5b2x18534253d7b9 extends Task {}
one sig x947c79cbxe2bbx49f4x82f9xeddf26a92326 extends Task {}
one sig x1a35c21dx6120x477cx98c9x6532bc00a908 extends Task {}
fact { all te: TaskEvent | te.task = xe829e492x7226x4ed5x815exbb17614aa050 implies (one x89494567x32cfx4d3cx90e0x46d286fbcd40 & te.data and one x3f17c84axdd9cx4df9x866cx029cc82e5a29 & te.data and one x785843d9x2cc8x4076x80c2xaaa6480f4f1b & te.data)}
fact { all te: TaskEvent | te.task = x947c79cbxe2bbx49f4x82f9xeddf26a92326 implies (one x89494567x32cfx4d3cx90e0x46d286fbcd40 & te.data and one x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec & te.data and one x3f17c84axdd9cx4df9x866cx029cc82e5a29 & te.data)}
fact { all te: TaskEvent | te.task = x1a35c21dx6120x477cx98c9x6532bc00a908 implies (one x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec & te.data)}
fact { all te: TaskEvent | lone(x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec & te.data) }
fact { all te: TaskEvent | one (x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec & te.data) implies te.task in (x947c79cbxe2bbx49f4x82f9xeddf26a92326 + x1a35c21dx6120x477cx98c9x6532bc00a908) }
fact { all te: TaskEvent | lone(x785843d9x2cc8x4076x80c2xaaa6480f4f1b & te.data) }
fact { all te: TaskEvent | one (x785843d9x2cc8x4076x80c2xaaa6480f4f1b & te.data) implies te.task in (xe829e492x7226x4ed5x815exbb17614aa050) }
fact { all te: TaskEvent | lone(x89494567x32cfx4d3cx90e0x46d286fbcd40 & te.data) }
fact { all te: TaskEvent | one (x89494567x32cfx4d3cx90e0x46d286fbcd40 & te.data) implies te.task in (xe829e492x7226x4ed5x815exbb17614aa050 + x947c79cbxe2bbx49f4x82f9xeddf26a92326) }
fact { all te: TaskEvent | lone(x3f17c84axdd9cx4df9x866cx029cc82e5a29 & te.data) }
fact { all te: TaskEvent | one (x3f17c84axdd9cx4df9x866cx029cc82e5a29 & te.data) implies te.task in (xe829e492x7226x4ed5x815exbb17614aa050 + x947c79cbxe2bbx49f4x82f9xeddf26a92326) }
fact {
Init[x272111bcx5a52x4ab7x81acxa2d86fa77c44]
Response[xa1cfeb64x44ecx4488xa5c0x220fbb37ed06, x7eaf35acx299bx43faxb5b2x18534253d7b9]
Precedence[xe829e492x7226x4ed5x815exbb17614aa050, xa47d9947x0cbex477ex81a2x02461098da2f]
Precedence[x6ae64eedx0736x4f8bx98c9xe2f5b69f11fe, xa47d9947x0cbex477ex81a2x02461098da2f]
Precedence[xa1cfeb64x44ecx4488xa5c0x220fbb37ed06, xe829e492x7226x4ed5x815exbb17614aa050]
Precedence[xa1cfeb64x44ecx4488xa5c0x220fbb37ed06, x6ae64eedx0736x4f8bx98c9xe2f5b69f11fe] 
Absence[x6ae64eedx0736x4f8bx98c9xe2f5b69f11fe, 2]
Absence[xe829e492x7226x4ed5x815exbb17614aa050, 3]
Absence[x272111bcx5a52x4ab7x81acxa2d86fa77c44, 1]
Existence[xa1cfeb64x44ecx4488xa5c0x220fbb37ed06]
Existence[x7eaf35acx299bx43faxb5b2x18534253d7b9]
Absence[x7eaf35acx299bx43faxb5b2x18534253d7b9, 1]
Absence[xa47d9947x0cbex477ex81a2x02461098da2f, 1]
}
abstract sig x89494567x32cfx4d3cx90e0x46d286fbcd40 extends Payload {}
fact { all te: TaskEvent | (lone x89494567x32cfx4d3cx90e0x46d286fbcd40 & te.data)}
one sig xd29daa49x3b6dx4431x9cd1xb5bf732fced2 extends x89494567x32cfx4d3cx90e0x46d286fbcd40{}
one sig x771d27a5x50f1x4389x8eefxd8bc1620c180 extends x89494567x32cfx4d3cx90e0x46d286fbcd40{}
one sig xfa525bf9xf83fx4db3x8089x4d33ce0d9f38 extends x89494567x32cfx4d3cx90e0x46d286fbcd40{}
one sig xb0e00f88x9421x4af7xbfbcx7b9eea630253 extends x89494567x32cfx4d3cx90e0x46d286fbcd40{}
abstract sig x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec extends Payload {}
fact { all te: TaskEvent | (lone x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec & te.data)}
one sig xaf1bd2dfx976bx4453x8066xb1badad5cd25 extends x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec{}
one sig x1df40950x04b6x4f2ex9bfex9d451803f17f extends x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec{}
one sig x46e57e1fx9d42x4b4dxa64ax6c6a54e11863 extends x25b0a7a9xb9b9x45eexab33x34fa62a8c3ec{}
abstract sig x3f17c84axdd9cx4df9x866cx029cc82e5a29 extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x3f17c84axdd9cx4df9x866cx029cc82e5a29 & te.data) }
pred Single(pl: x3f17c84axdd9cx4df9x866cx029cc82e5a29) {{pl.amount=1}}
fun Amount(pl: x3f17c84axdd9cx4df9x866cx029cc82e5a29): one Int {{pl.amount}}
one sig floatBetween50p0and100p0r100212 extends x3f17c84axdd9cx4df9x866cx029cc82e5a29{}{amount=7}
one sig floatBetween0p0and50p0r100211 extends x3f17c84axdd9cx4df9x866cx029cc82e5a29{}{amount=7}
abstract sig x785843d9x2cc8x4076x80c2xaaa6480f4f1b extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x785843d9x2cc8x4076x80c2xaaa6480f4f1b & te.data) }
pred Single(pl: x785843d9x2cc8x4076x80c2xaaa6480f4f1b) {{pl.amount=1}}
fun Amount(pl: x785843d9x2cc8x4076x80c2xaaa6480f4f1b): one Int {{pl.amount}}
one sig intBetweenm1and150r100213 extends x785843d9x2cc8x4076x80c2xaaa6480f4f1b{}{amount=7}
one sig intBetween149and300r100214 extends x785843d9x2cc8x4076x80c2xaaa6480f4f1b{}{amount=7}
fact { all te: TaskEvent | (xe829e492x7226x4ed5x815exbb17614aa050 = te.task and p100215[te]) implies (some ote: TaskEvent | x947c79cbxe2bbx49f4x82f9xeddf26a92326 = ote.task and p100215c[te, ote]) }
pred p100215(A: set TaskEvent) { { (A.data&x89494567x32cfx4d3cx90e0x46d286fbcd40=x771d27a5x50f1x4389x8eefxd8bc1620c180) } }
pred p100215c(A, B: set TaskEvent) { { not (A.data&x89494567x32cfx4d3cx90e0x46d286fbcd40=B.data&x89494567x32cfx4d3cx90e0x46d286fbcd40) } }
fact { some te: TaskEvent | te.task = xe829e492x7226x4ed5x815exbb17614aa050 and p100216[te]}
pred p100216(A: set TaskEvent) { { (A.data&x89494567x32cfx4d3cx90e0x46d286fbcd40=x771d27a5x50f1x4389x8eefxd8bc1620c180) } }

