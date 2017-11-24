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
lone sig TE5 extends TaskEvent {}
lone sig TE6 extends TaskEvent {}
lone sig TE7 extends TaskEvent {}
pred Next(pre, next: TaskEvent){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4 or pre=TE4 and next=TE5 or pre=TE5 and next=TE6 or pre=TE6 and next=TE7}
pred After(b, a: TaskEvent){// b=before, a=after
b=TE0 or a=TE7 or b=TE1 and not (a=TE0) or b=TE2 and not (a=TE0 or a=TE1) or b=TE3 and not (a=TE0 or a=TE1 or a=TE2) or b=TE4 and (a=TE7 or a=TE6 or a=TE5) or b=TE5 and (a=TE7 or a=TE6)}
fact{
one TE6 implies one TE5
one TE7 implies one TE6
}
one sig xad750dcax4dafx4149x88c5x6e873e9e7796 extends Task {}
one sig xc75b1f2fxf096x48bfxbf8bx7245e3737e97 extends Task {}
one sig x0228024fx32bcx47e9xb8d7x2ba59b390776 extends Task {}
one sig x2556aa07xe3efx4476x8f00x7899de3b071e extends Task {}
one sig xf6c06288x4d74x42daxa7a0x9d9d45d6f8b3 extends Task {}
one sig x708b191dx7131x4dfbxa422x45e001565edd extends Task {}
one sig xf15019bcxb876x4a67x828dxcbcc15f0055b extends Task {}
one sig x9cf1ac49xccd6x4220x8bddx82f26f89d9bd extends Task {}
fact { all te: TaskEvent | te.task = x9cf1ac49xccd6x4220x8bddx82f26f89d9bd implies (one x49079df7xe2d9x41d5xb1e4xc9d33774a810 & te.data)}
fact { all te: TaskEvent | te.task = xf15019bcxb876x4a67x828dxcbcc15f0055b implies (one x49386c07xa6f7x433fx8645xd5b06c7934d0 & te.data and one x49079df7xe2d9x41d5xb1e4xc9d33774a810 & te.data and one x0ac3e8a2xfac9x4358x9cd3x941c7c43df66 & te.data)}
fact { all te: TaskEvent | te.task = x0228024fx32bcx47e9xb8d7x2ba59b390776 implies (one x49386c07xa6f7x433fx8645xd5b06c7934d0 & te.data and one x0ac3e8a2xfac9x4358x9cd3x941c7c43df66 & te.data and one x4ec753ecx0d76x421ax91b4xb14b03e67449 & te.data)}
fact { all te: TaskEvent | lone(x49386c07xa6f7x433fx8645xd5b06c7934d0 & te.data) }
fact { all te: TaskEvent | one (x49386c07xa6f7x433fx8645xd5b06c7934d0 & te.data) implies te.task in (x0228024fx32bcx47e9xb8d7x2ba59b390776 + xf15019bcxb876x4a67x828dxcbcc15f0055b) }
fact { all te: TaskEvent | lone(x49079df7xe2d9x41d5xb1e4xc9d33774a810 & te.data) }
fact { all te: TaskEvent | one (x49079df7xe2d9x41d5xb1e4xc9d33774a810 & te.data) implies te.task in (xf15019bcxb876x4a67x828dxcbcc15f0055b + x9cf1ac49xccd6x4220x8bddx82f26f89d9bd) }
fact { all te: TaskEvent | lone(x0ac3e8a2xfac9x4358x9cd3x941c7c43df66 & te.data) }
fact { all te: TaskEvent | one (x0ac3e8a2xfac9x4358x9cd3x941c7c43df66 & te.data) implies te.task in (x0228024fx32bcx47e9xb8d7x2ba59b390776 + xf15019bcxb876x4a67x828dxcbcc15f0055b) }
fact { all te: TaskEvent | lone(x4ec753ecx0d76x421ax91b4xb14b03e67449 & te.data) }
fact { all te: TaskEvent | one (x4ec753ecx0d76x421ax91b4xb14b03e67449 & te.data) implies te.task in (x0228024fx32bcx47e9xb8d7x2ba59b390776) }
fact {
Init[xad750dcax4dafx4149x88c5x6e873e9e7796]
Response[xf6c06288x4d74x42daxa7a0x9d9d45d6f8b3,x708b191dx7131x4dfbxa422x45e001565edd]
Precedence[x0228024fx32bcx47e9xb8d7x2ba59b390776,xc75b1f2fxf096x48bfxbf8bx7245e3737e97]
Precedence[x2556aa07xe3efx4476x8f00x7899de3b071e,xc75b1f2fxf096x48bfxbf8bx7245e3737e97]
Precedence[xf6c06288x4d74x42daxa7a0x9d9d45d6f8b3,x0228024fx32bcx47e9xb8d7x2ba59b390776]
Precedence[xf6c06288x4d74x42daxa7a0x9d9d45d6f8b3,x2556aa07xe3efx4476x8f00x7899de3b071e]
Absence[x2556aa07xe3efx4476x8f00x7899de3b071e,2]
Absence[x0228024fx32bcx47e9xb8d7x2ba59b390776,3]
Absence[xad750dcax4dafx4149x88c5x6e873e9e7796,1]
Existence[xf6c06288x4d74x42daxa7a0x9d9d45d6f8b3]
Existence[x708b191dx7131x4dfbxa422x45e001565edd]
Absence[x708b191dx7131x4dfbxa422x45e001565edd,1]
Absence[xc75b1f2fxf096x48bfxbf8bx7245e3737e97,1]
}
abstract sig x49386c07xa6f7x433fx8645xd5b06c7934d0 extends Payload {}
fact { all te: TaskEvent | (lone x49386c07xa6f7x433fx8645xd5b06c7934d0 & te.data)}
one sig x4f8c0e7fxbbcbx4a3dxbd1ex8c8db79aaed1 extends x49386c07xa6f7x433fx8645xd5b06c7934d0{}
one sig xc458e46axcf0ax4162xadffx8adf63f6ee67 extends x49386c07xa6f7x433fx8645xd5b06c7934d0{}
one sig xcbd83ef7x4b64x4a06xae86xe7c22faa249d extends x49386c07xa6f7x433fx8645xd5b06c7934d0{}
one sig xad8dbf9bx7c7fx4ad9xbf74x189470cac204 extends x49386c07xa6f7x433fx8645xd5b06c7934d0{}
abstract sig x49079df7xe2d9x41d5xb1e4xc9d33774a810 extends Payload {}
fact { all te: TaskEvent | (lone x49079df7xe2d9x41d5xb1e4xc9d33774a810 & te.data)}
one sig x63b679b5x057bx4986xbb8ex22c29ed421c3 extends x49079df7xe2d9x41d5xb1e4xc9d33774a810{}
one sig xf940d495x77fdx4501x9164x223286cbf477 extends x49079df7xe2d9x41d5xb1e4xc9d33774a810{}
one sig xc3f76bc5x69f4x446bxa830x9f7336b9d79a extends x49079df7xe2d9x41d5xb1e4xc9d33774a810{}
abstract sig x0ac3e8a2xfac9x4358x9cd3x941c7c43df66 extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x0ac3e8a2xfac9x4358x9cd3x941c7c43df66 & te.data) }
pred Single(pl: x0ac3e8a2xfac9x4358x9cd3x941c7c43df66) {{pl.amount=1}}
fun Amount(pl: x0ac3e8a2xfac9x4358x9cd3x941c7c43df66): one Int {{pl.amount}}
one sig floatBetween50p0and100p0r100212 extends x0ac3e8a2xfac9x4358x9cd3x941c7c43df66{}{amount=15}
one sig floatBetween0p0and50p0r100211 extends x0ac3e8a2xfac9x4358x9cd3x941c7c43df66{}{amount=15}
abstract sig x4ec753ecx0d76x421ax91b4xb14b03e67449 extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x4ec753ecx0d76x421ax91b4xb14b03e67449 & te.data) }
pred Single(pl: x4ec753ecx0d76x421ax91b4xb14b03e67449) {{pl.amount=1}}
fun Amount(pl: x4ec753ecx0d76x421ax91b4xb14b03e67449): one Int {{pl.amount}}
one sig intBetweenm1and150r100213 extends x4ec753ecx0d76x421ax91b4xb14b03e67449{}{amount=15}
one sig intBetween149and300r100214 extends x4ec753ecx0d76x421ax91b4xb14b03e67449{}{amount=15}
fact { all te: TaskEvent | (x0228024fx32bcx47e9xb8d7x2ba59b390776 = te.task and p100215[te]) implies (some ote: TaskEvent | xf15019bcxb876x4a67x828dxcbcc15f0055b = ote.task and p100215c[te, ote]) }
pred p100215(A: set TaskEvent) { { (A.data&x49386c07xa6f7x433fx8645xd5b06c7934d0=xc458e46axcf0ax4162xadffx8adf63f6ee67) } }
pred p100215c(A, B: set TaskEvent) { { not (A.data&x49386c07xa6f7x433fx8645xd5b06c7934d0=B.data&x49386c07xa6f7x433fx8645xd5b06c7934d0) } }
fact { some te: TaskEvent | te.task = x0228024fx32bcx47e9xb8d7x2ba59b390776 and p100216[te]}
pred p100216(A: set TaskEvent) { { (A.data&x49386c07xa6f7x433fx8645xd5b06c7934d0=xc458e46axcf0ax4162xadffx8adf63f6ee67) } }

