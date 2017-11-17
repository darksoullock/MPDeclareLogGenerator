abstract sig Task {}
abstract sig Payload {}

abstract sig TaskEvent{
	pos: disj Int,
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

pred ExclusiveChoice(taskA, taskB: Task) { // remove cardinality
	some te: TaskEvent | te.task = taskA or te.task = taskB
	#{ te: TaskEvent | taskA = te.task } = 0 or #{ te: TaskEvent | taskB = te.task } = 0 
}

pred RespondedExistence(taskA, taskB: Task) { // remove cardinality
	#{ te: TaskEvent | taskA = te.task } > 0 implies #{ ote: TaskEvent | taskB = ote.task } > 0
}

pred Response(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task } > 0
}

pred AlternateResponse(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task and #{ ite: TaskEvent | ite.pos > te.pos and ite.pos < fte.pos and taskA = ite.task} = 0 } > 0
}

pred ChainResponse(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos = int[te.pos + 1] and taskB = fte.task } > 0
}

pred Precedence(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task } > 0
}

pred AlternatePrecedence(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task and #{ ite: TaskEvent | ite.pos > te.pos and ite.pos < fte.pos and taskA = ite.task} = 0 } > 0
}

pred ChainPrecedence(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | int[fte.pos + 1] = te.pos and taskB = fte.task } > 0
}

pred NotRespondedExistence(taskA, taskB: Task) { // remove cardinality
	#{ te: TaskEvent | taskA = te.task } > 0 implies #{ te: TaskEvent | taskB = te.task } = 0
}

pred NotResponse(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task } = 0
}

pred NotPrecedence(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task } = 0
}

pred NotChainResponse(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos = int[te.pos + 1] and taskB = fte.task } = 0
}

pred NotChainPrecedence(taskA, taskB: Task) { // remove cardinality
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | int[fte.pos + 1] = te.pos and taskB = fte.task } = 0
}
//-

pred example { }
run example

one sig TE0 extends TaskEvent {} {pos=-8}
one sig TE1 extends TaskEvent {} {pos=-7}
one sig TE2 extends TaskEvent {} {pos=-6}
one sig TE3 extends TaskEvent {} {pos=-5}
one sig TE4 extends TaskEvent {} {pos=-4}
one sig TE5 extends TaskEvent {} {pos=-3}
one sig TE6 extends TaskEvent {} {pos=-2}
one sig TE7 extends TaskEvent {} {pos=-1}
one sig TE8 extends TaskEvent {} {pos=0}
one sig TE9 extends TaskEvent {} {pos=1}
lone sig TE10 extends TaskEvent {} {pos=2}
lone sig TE11 extends TaskEvent {} {pos=3}
lone sig TE12 extends TaskEvent {} {pos=4}
fact{
one TE11 implies one TE10
one TE12 implies one TE11
}
one sig ApplyForTrip extends Task {}
one sig ApproveApplication extends Task {}
one sig BookMeansOfTransport extends Task {}
one sig BookAccomodation extends Task {}
one sig CollectTickets extends Task {}
one sig ArchiveDocuments extends Task {}
one sig UseTransport extends Task {}
one sig DoSomething extends Task {}
fact { all te: TaskEvent | te.task = DoSomething implies #{(Something) & te.data} = 1 }
fact { all te: TaskEvent | te.task = BookMeansOfTransport implies #{(TransportType + Price + Speed) & te.data} = 3 }
fact { all te: TaskEvent | te.task = UseTransport implies #{(TransportType + Something + Price) & te.data} = 3 }
fact { all te: TaskEvent | lone(Speed & te.data) }
fact { all te: TaskEvent | one (Speed & te.data) implies te.task in (BookMeansOfTransport) }
fact { all te: TaskEvent | lone(Price & te.data) }
fact { all te: TaskEvent | one (Price & te.data) implies te.task in (BookMeansOfTransport + UseTransport) }
fact { all te: TaskEvent | lone(TransportType & te.data) }
fact { all te: TaskEvent | one (TransportType & te.data) implies te.task in (BookMeansOfTransport + UseTransport) }
fact { all te: TaskEvent | lone(Something & te.data) }
fact { all te: TaskEvent | one (Something & te.data) implies te.task in (UseTransport + DoSomething) }
fact {
Init[ApplyForTrip]
Response[CollectTickets, ArchiveDocuments]
Precedence[BookMeansOfTransport, ApproveApplication]
Precedence[BookAccomodation, ApproveApplication]
Precedence[CollectTickets, BookMeansOfTransport]
Precedence[CollectTickets, BookAccomodation] 
Absence[BookAccomodation, 2]
Absence[BookMeansOfTransport, 3]
ChainResponse[UseTransport, DoSomething]
Existence[DoSomething]
Absence[ApplyForTrip, 1]
Existence[CollectTickets]
Existence[ArchiveDocuments]
Absence[ArchiveDocuments, 1]
Absence[ApproveApplication, 1]
}
abstract sig TransportType extends Payload {}
fact { all te: TaskEvent | #{TransportType & te.data} <= 1 }
one sig Car extends TransportType{}
one sig Plane extends TransportType{}
one sig Train extends TransportType{}
one sig Bus extends TransportType{}
abstract sig Something extends Payload {}
fact { all te: TaskEvent | #{Something & te.data} <= 1 }
one sig One extends Something{}
one sig None extends Something{}
one sig Another extends Something{}
abstract sig Price extends Payload {
amount: Int
}
fact { all te: TaskEvent | #{Price & te.data} <= 1 }
pred Single(pl: Price) {{pl.amount=1}}
fun Amount(pl: Price): one Int {{pl.amount}}
one sig intBetweenm1and25r100000 extends Price{}{amount=7}
one sig intBetween124and199r100004 extends Price{}{amount=7}
one sig intBetween200and251r100006 extends Price{}{amount=7}
one sig intBetween250and301r100007 extends Price{}{amount=7}
one sig intEqualsTo200r100005 extends Price{}{amount=1}
one sig intEqualsTo50r100002 extends Price{}{amount=1}
one sig intBetween24and50r100001 extends Price{}{amount=7}
one sig intBetween50and125r100003 extends Price{}{amount=7}
abstract sig Speed extends Payload {
amount: Int
}
fact { all te: TaskEvent | #{Speed & te.data} <= 1 }
pred Single(pl: Speed) {{pl.amount=1}}
fun Amount(pl: Speed): one Int {{pl.amount}}
one sig intBetween50and176r100011 extends Speed{}{amount=7}
one sig intBetween175and301r100012 extends Speed{}{amount=7}
one sig intBetween24and50r100009 extends Speed{}{amount=7}
one sig intBetweenm1and25r100008 extends Speed{}{amount=7}
one sig intEqualsTo50r100010 extends Speed{}{amount=1}
fact { no te: TaskEvent | te.task = BookMeansOfTransport and p100013[te] }
pred p100013(A: set TaskEvent) { { (A.data&Price in (intBetween124and199r100004 + intBetween200and251r100006 + intBetween250and301r100007 + intEqualsTo200r100005 + intBetween50and125r100003) and A.data&Speed in (intBetween50and176r100011 + intBetween175and301r100012 + intEqualsTo50r100010)) } }
fact { all te: TaskEvent | (BookMeansOfTransport = te.task and p100014[te]) implies #{ ote: TaskEvent | UseTransport = ote.task and p100014c[te, ote]} > 0 }
pred p100014(A: set TaskEvent) { { A.data&Price in (intEqualsTo50r100002) } }
pred p100014c(A, B: set TaskEvent) { { B.data&Price in (intEqualsTo200r100005) } }

