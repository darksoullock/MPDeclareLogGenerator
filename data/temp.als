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
one sig x7e58a2a9xa52dx4318xbde8x5c414e178fac extends Task {}
one sig x01933d8cx41e0x41e5x8a95x7d967fc6cfaa extends Task {}
one sig x8f79cecfxb4bex46eax9d54xcd46b70eb90c extends Task {}
one sig xa2daf4dex0bcax4ec2xaf56x768ea6b5e88a extends Task {}
one sig x9f5ed38cx6c20x44f1x845cx09c63489447b extends Task {}
one sig xd4ac1a44xf46cx4fd7xbff4xd65a620aeff5 extends Task {}
one sig x48d86a07x374bx46ecxa2a8x8ac64e812ebe extends Task {}
one sig xc39016eexe728x4398x8210xf84655f3803d extends Task {}
fact { all te: TaskEvent | te.task = x8f79cecfxb4bex46eax9d54xcd46b70eb90c implies (one xbae42616x7903x4c7dxa993xc41b08090aeb & te.data and one xe488a0b0x4591x4b4bxa798x0bfc242d99ee & te.data and one xa567056exbd3ax4681xa06axe37f92f4984e & te.data)}
fact { all te: TaskEvent | te.task = xc39016eexe728x4398x8210xf84655f3803d implies (one x3f92d4c9x67c5x4e71x8975x0509c38e673c & te.data)}
fact { all te: TaskEvent | te.task = x48d86a07x374bx46ecxa2a8x8ac64e812ebe implies (one xbae42616x7903x4c7dxa993xc41b08090aeb & te.data and one x3f92d4c9x67c5x4e71x8975x0509c38e673c & te.data and one xe488a0b0x4591x4b4bxa798x0bfc242d99ee & te.data)}
fact { all te: TaskEvent | lone(xa567056exbd3ax4681xa06axe37f92f4984e & te.data) }
fact { all te: TaskEvent | one (xa567056exbd3ax4681xa06axe37f92f4984e & te.data) implies te.task in (x8f79cecfxb4bex46eax9d54xcd46b70eb90c) }
fact { all te: TaskEvent | lone(xbae42616x7903x4c7dxa993xc41b08090aeb & te.data) }
fact { all te: TaskEvent | one (xbae42616x7903x4c7dxa993xc41b08090aeb & te.data) implies te.task in (x8f79cecfxb4bex46eax9d54xcd46b70eb90c + x48d86a07x374bx46ecxa2a8x8ac64e812ebe) }
fact { all te: TaskEvent | lone(x3f92d4c9x67c5x4e71x8975x0509c38e673c & te.data) }
fact { all te: TaskEvent | one (x3f92d4c9x67c5x4e71x8975x0509c38e673c & te.data) implies te.task in (x48d86a07x374bx46ecxa2a8x8ac64e812ebe + xc39016eexe728x4398x8210xf84655f3803d) }
fact { all te: TaskEvent | lone(xe488a0b0x4591x4b4bxa798x0bfc242d99ee & te.data) }
fact { all te: TaskEvent | one (xe488a0b0x4591x4b4bxa798x0bfc242d99ee & te.data) implies te.task in (x8f79cecfxb4bex46eax9d54xcd46b70eb90c + x48d86a07x374bx46ecxa2a8x8ac64e812ebe) }
fact {
Init[x7e58a2a9xa52dx4318xbde8x5c414e178fac]
Response[x9f5ed38cx6c20x44f1x845cx09c63489447b, xd4ac1a44xf46cx4fd7xbff4xd65a620aeff5]
Precedence[x8f79cecfxb4bex46eax9d54xcd46b70eb90c, x01933d8cx41e0x41e5x8a95x7d967fc6cfaa]
Precedence[xa2daf4dex0bcax4ec2xaf56x768ea6b5e88a, x01933d8cx41e0x41e5x8a95x7d967fc6cfaa]
Precedence[x9f5ed38cx6c20x44f1x845cx09c63489447b, x8f79cecfxb4bex46eax9d54xcd46b70eb90c]
Precedence[x9f5ed38cx6c20x44f1x845cx09c63489447b, xa2daf4dex0bcax4ec2xaf56x768ea6b5e88a] 
Absence[xa2daf4dex0bcax4ec2xaf56x768ea6b5e88a, 2]
Absence[x8f79cecfxb4bex46eax9d54xcd46b70eb90c, 3]
Absence[x7e58a2a9xa52dx4318xbde8x5c414e178fac, 1]
Existence[x9f5ed38cx6c20x44f1x845cx09c63489447b]
Existence[xd4ac1a44xf46cx4fd7xbff4xd65a620aeff5]
Absence[xd4ac1a44xf46cx4fd7xbff4xd65a620aeff5, 1]
Absence[x01933d8cx41e0x41e5x8a95x7d967fc6cfaa, 1]
}
abstract sig xbae42616x7903x4c7dxa993xc41b08090aeb extends Payload {}
fact { all te: TaskEvent | (lone xbae42616x7903x4c7dxa993xc41b08090aeb & te.data)}
one sig x8c9c1e21x3618x4933xa938xb1f6dc353e82 extends xbae42616x7903x4c7dxa993xc41b08090aeb{}
one sig x86b8bd8dx9b96x4b1cx92ebx7d7a66eb9175 extends xbae42616x7903x4c7dxa993xc41b08090aeb{}
one sig x0456e06axa85ex42cfxbf86xc3e9ce86db7e extends xbae42616x7903x4c7dxa993xc41b08090aeb{}
one sig x663613acxe449x48c2x9a20xdf36d20b7418 extends xbae42616x7903x4c7dxa993xc41b08090aeb{}
abstract sig x3f92d4c9x67c5x4e71x8975x0509c38e673c extends Payload {}
fact { all te: TaskEvent | (lone x3f92d4c9x67c5x4e71x8975x0509c38e673c & te.data)}
one sig xcb5767ddx6ae8x4fddx97b2x25d0357d079f extends x3f92d4c9x67c5x4e71x8975x0509c38e673c{}
one sig xff94ab07x9ec3x43c4x81bax2948db9f8310 extends x3f92d4c9x67c5x4e71x8975x0509c38e673c{}
one sig x2ab2b0faxf494x4d41xb549x032b55aa3331 extends x3f92d4c9x67c5x4e71x8975x0509c38e673c{}
abstract sig xe488a0b0x4591x4b4bxa798x0bfc242d99ee extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone xe488a0b0x4591x4b4bxa798x0bfc242d99ee & te.data) }
pred Single(pl: xe488a0b0x4591x4b4bxa798x0bfc242d99ee) {{pl.amount=1}}
fun Amount(pl: xe488a0b0x4591x4b4bxa798x0bfc242d99ee): one Int {{pl.amount}}
one sig floatBetween50p0and100p0r100212 extends xe488a0b0x4591x4b4bxa798x0bfc242d99ee{}{amount=7}
one sig floatBetween0p0and50p0r100211 extends xe488a0b0x4591x4b4bxa798x0bfc242d99ee{}{amount=7}
abstract sig xa567056exbd3ax4681xa06axe37f92f4984e extends Payload {
amount: Int
}
fact { all te: TaskEvent | (lone xa567056exbd3ax4681xa06axe37f92f4984e & te.data) }
pred Single(pl: xa567056exbd3ax4681xa06axe37f92f4984e) {{pl.amount=1}}
fun Amount(pl: xa567056exbd3ax4681xa06axe37f92f4984e): one Int {{pl.amount}}
one sig intBetweenm1and150r100213 extends xa567056exbd3ax4681xa06axe37f92f4984e{}{amount=7}
one sig intBetween149and300r100214 extends xa567056exbd3ax4681xa06axe37f92f4984e{}{amount=7}
fact { all te: TaskEvent | (x8f79cecfxb4bex46eax9d54xcd46b70eb90c = te.task and p100215[te]) implies (some ote: TaskEvent | x48d86a07x374bx46ecxa2a8x8ac64e812ebe = ote.task and p100215c[te, ote]) }
pred p100215(A: set TaskEvent) { { (A.data&xbae42616x7903x4c7dxa993xc41b08090aeb=x86b8bd8dx9b96x4b1cx92ebx7d7a66eb9175) } }
pred p100215c(A, B: set TaskEvent) { { not (A.data&xbae42616x7903x4c7dxa993xc41b08090aeb=B.data&xbae42616x7903x4c7dxa993xc41b08090aeb) } }
fact { some te: TaskEvent | te.task = x8f79cecfxb4bex46eax9d54xcd46b70eb90c and p100216[te]}
pred p100216(A: set TaskEvent) { { (A.data&xbae42616x7903x4c7dxa993xc41b08090aeb=x86b8bd8dx9b96x4b1cx92ebx7d7a66eb9175) } }

