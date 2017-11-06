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
lone sig DummyToken extends Token {}
fact { #{DummyToken} <= 0 }

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

one sig TE0 extends TaskEvent {} {pos=-16}
one sig TE1 extends TaskEvent {} {pos=-15}
one sig TE2 extends TaskEvent {} {pos=-14}
one sig TE3 extends TaskEvent {} {pos=-13}
one sig TE4 extends TaskEvent {} {pos=-12}
one sig TE5 extends TaskEvent {} {pos=-11}
one sig TE6 extends TaskEvent {} {pos=-10}
one sig TE7 extends TaskEvent {} {pos=-9}
one sig TE8 extends TaskEvent {} {pos=-8}
one sig TE9 extends TaskEvent {} {pos=-7}
one sig TE10 extends TaskEvent {} {pos=-6}
one sig TE11 extends TaskEvent {} {pos=-5}
one sig TE12 extends TaskEvent {} {pos=-4}
one sig TE13 extends TaskEvent {} {pos=-3}
one sig TE14 extends TaskEvent {} {pos=-2}
lone sig TE15 extends TaskEvent {} {pos=-1}
lone sig TE16 extends TaskEvent {} {pos=0}
lone sig TE17 extends TaskEvent {} {pos=1}
lone sig TE18 extends TaskEvent {} {pos=2}
lone sig TE19 extends TaskEvent {} {pos=3}
fact{
one TE16 implies one TE15
one TE17 implies one TE16
one TE18 implies one TE17
one TE19 implies one TE18
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
fact { all te: TaskEvent | #{Speed & te.data} <= 1 }
fact { all te: TaskEvent | #{Speed & te.data} = 1 implies te.task in (BookMeansOfTransport) }
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
Existence[BookMeansOfTransport, 5]
Absence[BookMeansOfTransport, 5]
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
fact { no te: TaskEvent | te.task = UseTransport and p100007[te] }
pred p100007(B: set TaskEvent) { { (B.data&Price in (intEqualsTo3r100002) or B.data&Price in (intEqualsTo0r100000)) } }
fact { all te: TaskEvent | (BookMeansOfTransport = te.task and p100008[te]) implies #{ fte: TaskEvent | fte.pos = int[te.pos + 1] and UseTransport = fte.task and p100008c[te, fte] } > 0 }
pred p100008(A: set TaskEvent) { { 1=1 } }
pred p100008c(A, B: set TaskEvent) { { (not A.data&Price=B.data&Price) or (A.data&Price=B.data&Price and one (DifPrice100009 & B.tokens) and (DifPrice100009 & A.tokens) = (DifPrice100009 & B.tokens))  } }
abstract sig DifPrice100009 extends Token {}
fact { all te:TaskEvent | #{DifPrice100009 & te.tokens}>0 implies #{Price&te.data}>0 and not Single[Price&te.data] }
one sig DifPrice100009i0 extends DifPrice100009 {}
fact { #{te: TaskEvent | DifPrice100009i0 in te.tokens}=0 or #{te: TaskEvent | DifPrice100009i0 in te.tokens } = 2}
one sig DifPrice100009i1 extends DifPrice100009 {}
fact { #{te: TaskEvent | DifPrice100009i1 in te.tokens}=0 or #{te: TaskEvent | DifPrice100009i1 in te.tokens } = 2}
one sig DifPrice100009i2 extends DifPrice100009 {}
fact { #{te: TaskEvent | DifPrice100009i2 in te.tokens}=0 or #{te: TaskEvent | DifPrice100009i2 in te.tokens } = 2}
one sig DifPrice100009i3 extends DifPrice100009 {}
fact { #{te: TaskEvent | DifPrice100009i3 in te.tokens}=0 or #{te: TaskEvent | DifPrice100009i3 in te.tokens } = 2}
one sig DifPrice100009i4 extends DifPrice100009 {}
fact { #{te: TaskEvent | DifPrice100009i4 in te.tokens}=0 or #{te: TaskEvent | DifPrice100009i4 in te.tokens } = 2}
one sig DifPrice100009i5 extends DifPrice100009 {}
fact { #{te: TaskEvent | DifPrice100009i5 in te.tokens}=0 or #{te: TaskEvent | DifPrice100009i5 in te.tokens } = 2}

