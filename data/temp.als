abstract sig Task {}
abstract sig Payload {}

abstract sig TaskEvent{
	pos: disj Int,
	task: one Task,
	data: set Payload,
	tokens: set Token
}

one sig DummyPayload extends Payload {}
fact { #{te:TaskEvent | DummyPayload in te.data} <= 0 }

abstract sig Token {}
abstract sig SameToken extends Token {}
abstract sig DiffToken extends Token {}
lone sig DummySToken extends SameToken{}
lone sig DummyDToken extends DiffToken{}
fact { 
	#{DummySToken} <= 0 
	#{DummyDToken} <= 0 
	all te:TaskEvent| #{te.tokens & SameToken}=0 or #{te.tokens & DiffToken}=0
}

// declare templates

pred Init(taskA: Task) { 
	one te: TaskEvent | taskA = te.task and te.pos = TE0.pos
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
	#{ te: TaskEvent | taskA = te.task } = 0 or #{ te: TaskEvent | taskB = te.task } = 0 
}

pred RespondedExistence(taskA, taskB: Task) { 
	#{ te: TaskEvent | taskA = te.task } > 0 implies #{ ote: TaskEvent | taskB = ote.task } > 0
}

pred Response(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task } > 0
}

pred AlternateResponse(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task and #{ ite: TaskEvent | ite.pos > te.pos and ite.pos < fte.pos and taskA = ite.task} = 0 } > 0
}

pred ChainResponse(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos = int[te.pos + 1] and taskB = fte.task } > 0
}

pred Precedence(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task } > 0
}

pred AlternatePrecedence(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task and #{ ite: TaskEvent | ite.pos > te.pos and ite.pos < fte.pos and taskA = ite.task} = 0 } > 0
}

pred ChainPrecedence(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | int[fte.pos + 1] = te.pos and taskB = fte.task } > 0
}

pred NotRespondedExistence(taskA, taskB: Task) { 
	#{ te: TaskEvent | taskA = te.task } > 0 implies #{ te: TaskEvent | taskB = te.task } = 0
}

pred NotResponse(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task } = 0
}

pred NotPrecedence(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task } = 0
}

pred NotChainResponse(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos = int[te.pos + 1] and taskB = fte.task } = 0
}

pred NotChainPrecedence(taskA, taskB: Task) { 
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
fact { all te: TaskEvent | te.task = BookMeansOfTransport implies #{(TransportType + Price) & te.data} = 2 }
fact { all te: TaskEvent | te.task = UseTransport implies #{(TransportType + Something + Price) & te.data} = 3 }
fact { all te: TaskEvent | #{Price & te.data} <= 1 }
fact { all te: TaskEvent | #{Price & te.data} = 1 implies te.task in (BookMeansOfTransport + UseTransport) }
fact { all te: TaskEvent | #{TransportType & te.data} <= 1 }
fact { all te: TaskEvent | #{TransportType & te.data} = 1 implies te.task in (BookMeansOfTransport + UseTransport) }
fact { all te: TaskEvent | #{Something & te.data} <= 1 }
fact { all te: TaskEvent | #{Something & te.data} = 1 implies te.task in (UseTransport + DoSomething) }
fact {
Init[ApplyForTrip]
Response[CollectTickets, ArchiveDocuments]
Precedence[BookMeansOfTransport, ApproveApplication]
Precedence[BookAccomodation, ApproveApplication]
Precedence[CollectTickets, BookMeansOfTransport]
Precedence[CollectTickets, BookAccomodation] 
Absence[BookAccomodation, 2]
Existence[DoSomething]
Absence[ApplyForTrip, 1]
Existence[CollectTickets]
Existence[ArchiveDocuments]
Absence[ArchiveDocuments, 1]
Absence[ApproveApplication, 1]
Exactly[BookMeansOfTransport, 1]
Absence[UseTransport, 2]
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
one sig intEqualsTo0r100000 extends Price{}{amount=1}
one sig intBetween0and3r100001 extends Price{}{amount=2}
one sig intEqualsTo3r100002 extends Price{}{amount=1}
abstract sig Speed extends Payload {
amount: Int
}
fact { all te: TaskEvent | #{Speed & te.data} <= 1 }
pred Single(pl: Speed) {{pl.amount=1}}
one sig intBetween0and300r100004 extends Speed{}{amount=-1}
one sig intEqualsTo300r100005 extends Speed{}{amount=1}
one sig intEqualsTo0r100003 extends Speed{}{amount=1}
fact { no te: TaskEvent | te.task = BookMeansOfTransport and p100006[te] }
pred p100006(B: set TaskEvent) { { (B.data&Price in (intEqualsTo3r100002) or B.data&Price in (intEqualsTo0r100000)) } }
fact { all te: TaskEvent | (BookMeansOfTransport = te.task and p100007[te]) implies #{ fte: TaskEvent | fte.pos = int[te.pos + 1] and UseTransport = fte.task and p100007c[te, fte] } > 0 }
pred p100007(A: set TaskEvent) { { 1=1 } }
pred p100007c(A, B: set TaskEvent) { { (A.data&Price=B.data&Price and ((one (SamePrice100008 & A.tokens)  and (SamePrice100008 & A.tokens) = (SamePrice100008 & B.tokens)) )) } }
abstract sig SamePrice100008 extends SameToken {}
one sig SamePrice100008i0 extends SamePrice100008 {}
fact {
#{te: TaskEvent | SamePrice100008i0 in te.tokens}=0 or #{te: TaskEvent | SamePrice100008i0 in te.tokens } = 2 }
one sig SamePrice100008i1 extends SamePrice100008 {}
fact {
#{te: TaskEvent | SamePrice100008i1 in te.tokens}=0 or #{te: TaskEvent | SamePrice100008i1 in te.tokens } = 2 }
one sig SamePrice100008i2 extends SamePrice100008 {}
fact {
#{te: TaskEvent | SamePrice100008i2 in te.tokens}=0 or #{te: TaskEvent | SamePrice100008i2 in te.tokens } = 2 }
one sig SamePrice100008i3 extends SamePrice100008 {}
fact {
#{te: TaskEvent | SamePrice100008i3 in te.tokens}=0 or #{te: TaskEvent | SamePrice100008i3 in te.tokens } = 2 }
one sig SamePrice100008i4 extends SamePrice100008 {}
fact {
#{te: TaskEvent | SamePrice100008i4 in te.tokens}=0 or #{te: TaskEvent | SamePrice100008i4 in te.tokens } = 2 }
one sig SamePrice100008i5 extends SamePrice100008 {}
fact {
#{te: TaskEvent | SamePrice100008i5 in te.tokens}=0 or #{te: TaskEvent | SamePrice100008i5 in te.tokens } = 2 }
fact {
all te: TaskEvent | (te.task = BookMeansOfTransport or te.task = UseTransport or #{SamePrice100008 & te.tokens}<=0)
some te: TaskEvent | SamePrice100008 in te.tokens implies (all ote: TaskEvent| SamePrice100008 in ote.tokens implies ote.data&Price = te.data&Price)
}
fact { all te: TaskEvent | (BookMeansOfTransport = te.task and p100009[te]) implies #{ fte: TaskEvent | fte.pos > te.pos and UseTransport = fte.task and p100009c[te, fte] } > 0 }
pred p100009(A: set TaskEvent) { { 1=1 } }
pred p100009c(A, B: set TaskEvent) { { (not A.data&Price=B.data&Price) or (A.data&Price=B.data&Price and one (DiffPrice100010 & B.tokens) and (DiffPrice100010 & A.tokens) = (DiffPrice100010 & B.tokens))  } }
abstract sig DiffPrice100010 extends DiffToken {}
fact { all te:TaskEvent | #{DiffPrice100010 & te.tokens}>0 implies #{Price&te.data}>0 and not Single[Price&te.data] }
one sig DiffPrice100010i0 extends DiffPrice100010 {}
fact { #{te: TaskEvent | DiffPrice100010i0 in te.tokens}=0 or #{te: TaskEvent | DiffPrice100010i0 in te.tokens } = 2}
one sig DiffPrice100010i1 extends DiffPrice100010 {}
fact { #{te: TaskEvent | DiffPrice100010i1 in te.tokens}=0 or #{te: TaskEvent | DiffPrice100010i1 in te.tokens } = 2}
one sig DiffPrice100010i2 extends DiffPrice100010 {}
fact { #{te: TaskEvent | DiffPrice100010i2 in te.tokens}=0 or #{te: TaskEvent | DiffPrice100010i2 in te.tokens } = 2}
one sig DiffPrice100010i3 extends DiffPrice100010 {}
fact { #{te: TaskEvent | DiffPrice100010i3 in te.tokens}=0 or #{te: TaskEvent | DiffPrice100010i3 in te.tokens } = 2}
one sig DiffPrice100010i4 extends DiffPrice100010 {}
fact { #{te: TaskEvent | DiffPrice100010i4 in te.tokens}=0 or #{te: TaskEvent | DiffPrice100010i4 in te.tokens } = 2}
one sig DiffPrice100010i5 extends DiffPrice100010 {}
fact { #{te: TaskEvent | DiffPrice100010i5 in te.tokens}=0 or #{te: TaskEvent | DiffPrice100010i5 in te.tokens } = 2}

