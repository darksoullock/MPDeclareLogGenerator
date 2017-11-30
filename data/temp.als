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
one sig x20cf77ecxee7fx45d3xbb51xa537d55445c8 extends Task {}
one sig xdc8811b1xf1a6x4ae0x90c7x486b373bd33d extends Task {}
one sig x9b38d72ex91adx42eaxaa65x211ca3c60271 extends Task {}
one sig x56608b33x21dfx4b0dx821cxa9d286b34b8d extends Task {}
one sig x52d3ddd9xec79x4e4dx9900xd2b3539fd2e6 extends Task {}
one sig xd233806cx6777x49cbx9d94xc5f23832d1ca extends Task {}
one sig xcb74c3a9xe2f7x48edxb3bcx06a2dd946513 extends Task {}
one sig xefe82cfdxe0cbx4d48xa35dxa3e37fcd847d extends Task {}
fact { all te: TaskEvent | te.task = xefe82cfdxe0cbx4d48xa35dxa3e37fcd847d implies (one x06707eebx1a05x4617xa8e4x9411d1a1ce24 & te.data)}
fact { all te: TaskEvent | te.task = xcb74c3a9xe2f7x48edxb3bcx06a2dd946513 implies (one x27d6c688xcc49x47fdx8bdfx0956f60916ff & te.data and one x06707eebx1a05x4617xa8e4x9411d1a1ce24 & te.data and one xda439f3fxae0dx4b58xb971x053c380c803c & te.data)}
fact { all te: TaskEvent | te.task = x9b38d72ex91adx42eaxaa65x211ca3c60271 implies (one x27d6c688xcc49x47fdx8bdfx0956f60916ff & te.data and one xda439f3fxae0dx4b58xb971x053c380c803c & te.data and one x02a80227xf7cax44c3x9fb6x64ad8eda1cb8 & te.data)}
fact { all te: TaskEvent | lone(xda439f3fxae0dx4b58xb971x053c380c803c & te.data) }
fact { all te: TaskEvent | one (xda439f3fxae0dx4b58xb971x053c380c803c & te.data) implies te.task in (x9b38d72ex91adx42eaxaa65x211ca3c60271 + xcb74c3a9xe2f7x48edxb3bcx06a2dd946513) }
fact { all te: TaskEvent | lone(x02a80227xf7cax44c3x9fb6x64ad8eda1cb8 & te.data) }
fact { all te: TaskEvent | one (x02a80227xf7cax44c3x9fb6x64ad8eda1cb8 & te.data) implies te.task in (x9b38d72ex91adx42eaxaa65x211ca3c60271) }
fact { all te: TaskEvent | lone(x06707eebx1a05x4617xa8e4x9411d1a1ce24 & te.data) }
fact { all te: TaskEvent | one (x06707eebx1a05x4617xa8e4x9411d1a1ce24 & te.data) implies te.task in (xcb74c3a9xe2f7x48edxb3bcx06a2dd946513 + xefe82cfdxe0cbx4d48xa35dxa3e37fcd847d) }
fact { all te: TaskEvent | lone(x27d6c688xcc49x47fdx8bdfx0956f60916ff & te.data) }
fact { all te: TaskEvent | one (x27d6c688xcc49x47fdx8bdfx0956f60916ff & te.data) implies te.task in (x9b38d72ex91adx42eaxaa65x211ca3c60271 + xcb74c3a9xe2f7x48edxb3bcx06a2dd946513) }
fact {
Init[x20cf77ecxee7fx45d3xbb51xa537d55445c8]
Response[x52d3ddd9xec79x4e4dx9900xd2b3539fd2e6,xd233806cx6777x49cbx9d94xc5f23832d1ca]
Precedence[x9b38d72ex91adx42eaxaa65x211ca3c60271,xdc8811b1xf1a6x4ae0x90c7x486b373bd33d]
Precedence[x56608b33x21dfx4b0dx821cxa9d286b34b8d,xdc8811b1xf1a6x4ae0x90c7x486b373bd33d]
Precedence[x52d3ddd9xec79x4e4dx9900xd2b3539fd2e6,x9b38d72ex91adx42eaxaa65x211ca3c60271]
Precedence[x52d3ddd9xec79x4e4dx9900xd2b3539fd2e6,x56608b33x21dfx4b0dx821cxa9d286b34b8d]
Absence[x56608b33x21dfx4b0dx821cxa9d286b34b8d,2]
Absence[x9b38d72ex91adx42eaxaa65x211ca3c60271,3]
Absence[x20cf77ecxee7fx45d3xbb51xa537d55445c8,1]
Existence[x52d3ddd9xec79x4e4dx9900xd2b3539fd2e6]
Existence[xd233806cx6777x49cbx9d94xc5f23832d1ca]
Absence[xd233806cx6777x49cbx9d94xc5f23832d1ca,1]
Absence[xdc8811b1xf1a6x4ae0x90c7x486b373bd33d,1]
}
abstract sig x27d6c688xcc49x47fdx8bdfx0956f60916ff extends Payload {}
fact { all te: TaskEvent | (lone x27d6c688xcc49x47fdx8bdfx0956f60916ff & te.data)}
one sig xe64eedd5x74b3x4774xbfc9x2f1fbb8a15ce extends x27d6c688xcc49x47fdx8bdfx0956f60916ff{}
one sig x8677c3d7x7bfdx488exaeb8x6e0637cde4d0 extends x27d6c688xcc49x47fdx8bdfx0956f60916ff{}
one sig x8ec990d2xb407x459fxb650xbb2a21f05e3e extends x27d6c688xcc49x47fdx8bdfx0956f60916ff{}
one sig x02db93c0x3c95x43ecx9709x3dc0a4c5f130 extends x27d6c688xcc49x47fdx8bdfx0956f60916ff{}
abstract sig x06707eebx1a05x4617xa8e4x9411d1a1ce24 extends Payload {}
fact { all te: TaskEvent | (lone x06707eebx1a05x4617xa8e4x9411d1a1ce24 & te.data)}
one sig xdb8f25dbxb848x4e7dx9d5ex73ddb27ff3a0 extends x06707eebx1a05x4617xa8e4x9411d1a1ce24{}
one sig xddb1a766x1039x4824x872bxe12bd33dc9a8 extends x06707eebx1a05x4617xa8e4x9411d1a1ce24{}
one sig xa17cd722x4f83x47c0xa006x835031dea5dc extends x06707eebx1a05x4617xa8e4x9411d1a1ce24{}
abstract sig xda439f3fxae0dx4b58xb971x053c380c803c extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone xda439f3fxae0dx4b58xb971x053c380c803c & te.data) }
pred Single(pl: xda439f3fxae0dx4b58xb971x053c380c803c) {{pl.amount=1}}
fun Amount(pl: xda439f3fxae0dx4b58xb971x053c380c803c): one Int {{pl.amount}}
one sig floatBetween50p0and100p0r100212 extends xda439f3fxae0dx4b58xb971x053c380c803c{}{amount=15}
one sig floatBetween0p0and50p0r100211 extends xda439f3fxae0dx4b58xb971x053c380c803c{}{amount=15}
abstract sig x02a80227xf7cax44c3x9fb6x64ad8eda1cb8 extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone x02a80227xf7cax44c3x9fb6x64ad8eda1cb8 & te.data) }
pred Single(pl: x02a80227xf7cax44c3x9fb6x64ad8eda1cb8) {{pl.amount=1}}
fun Amount(pl: x02a80227xf7cax44c3x9fb6x64ad8eda1cb8): one Int {{pl.amount}}
one sig intBetweenm1and150r100213 extends x02a80227xf7cax44c3x9fb6x64ad8eda1cb8{}{amount=15}
one sig intBetween149and300r100214 extends x02a80227xf7cax44c3x9fb6x64ad8eda1cb8{}{amount=15}
fact { all te: TaskEvent | (x9b38d72ex91adx42eaxaa65x211ca3c60271 = te.task and p100215[te]) implies (some ote: TaskEvent | xcb74c3a9xe2f7x48edxb3bcx06a2dd946513 = ote.task and p100215c[te, ote]) }
pred p100215(A: set TaskEvent) { { (A.data&x27d6c688xcc49x47fdx8bdfx0956f60916ff=x8677c3d7x7bfdx488exaeb8x6e0637cde4d0) } }
pred p100215c(A, B: set TaskEvent) { { not (A.data&x27d6c688xcc49x47fdx8bdfx0956f60916ff=B.data&x27d6c688xcc49x47fdx8bdfx0956f60916ff) } }
fact { some te: TaskEvent | te.task = x9b38d72ex91adx42eaxaa65x211ca3c60271 and p100216[te]}
pred p100216(A: set TaskEvent) { { (A.data&x27d6c688xcc49x47fdx8bdfx0956f60916ff=x8677c3d7x7bfdx488exaeb8x6e0637cde4d0) } }

