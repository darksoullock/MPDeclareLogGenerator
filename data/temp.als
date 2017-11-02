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

one sig TE0 extends TaskEvent {} {pos=-8}
one sig TE1 extends TaskEvent {} {pos=-7}
one sig TE2 extends TaskEvent {} {pos=-6}
one sig TE3 extends TaskEvent {} {pos=-5}
one sig TE4 extends TaskEvent {} {pos=-4}
one sig TE5 extends TaskEvent {} {pos=-3}
one sig TE6 extends TaskEvent {} {pos=-2}
lone sig TE7 extends TaskEvent {} {pos=-1}
lone sig TE8 extends TaskEvent {} {pos=0}
lone sig TE9 extends TaskEvent {} {pos=1}
lone sig TE10 extends TaskEvent {} {pos=2}
lone sig TE11 extends TaskEvent {} {pos=3}
fact{
one TE8 implies one TE7
one TE9 implies one TE8
one TE10 implies one TE9
one TE11 implies one TE10
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
Absence[BookMeansOfTransport, 3]
Existence[DoSomething]
Absence[ApplyForTrip, 1]
Existence[CollectTickets]
Existence[ArchiveDocuments]
Absence[ArchiveDocuments, 1]
Absence[ApproveApplication, 1]
Exactly[BookMeansOfTransport, 2]
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
abstract sig Price extends Payload {}
fact { all te: TaskEvent | #{Price & te.data} <= 1 }
one sig intBetween0and300r100001 extends Price{}
abstract sig Speed extends Payload {}
fact { all te: TaskEvent | #{Speed & te.data} <= 1 }
one sig intBetween0and300r100004 extends Speed{}
one sig intEqualsTo300r100005 extends Speed{}
one sig intEqualsTo0r100003 extends Speed{}
fact { all te: TaskEvent | (BookMeansOfTransport = te.task and p100006[te]) implies #{ fte: TaskEvent | fte.pos > te.pos and UseTransport = fte.task and p100006c[te, fte] } > 0 }
pred p100006(A: set TaskEvent) { { 1=1 } }
pred p100006c(A, B: set TaskEvent) { { (A.data&Price=B.data&Price and one (GetPrice100007 & A.tokens) and one (SetPrice100007 & B.tokens) and (GetPrice100007 & A.tokens).id = (SetPrice100007 & B.tokens).id) } }
abstract sig GetPrice100007 extends Token {
id: disj Int
}
abstract sig SetPrice100007 extends Token {
id: disj Int
}
one sig GetPrice100007i0 extends GetPrice100007 {} {id=-8}
one sig SetPrice100007i0 extends SetPrice100007 {} {id=-8}
fact {
#{te: TaskEvent | GetPrice100007i0 in te.tokens}<=1
#{te: TaskEvent | GetPrice100007i0 in te.tokens } = #{te: TaskEvent | SetPrice100007i0 in te.tokens }
}
one sig GetPrice100007i1 extends GetPrice100007 {} {id=-7}
one sig SetPrice100007i1 extends SetPrice100007 {} {id=-7}
fact {
#{te: TaskEvent | GetPrice100007i1 in te.tokens}<=1
#{te: TaskEvent | GetPrice100007i1 in te.tokens } = #{te: TaskEvent | SetPrice100007i1 in te.tokens }
}
one sig GetPrice100007i2 extends GetPrice100007 {} {id=-6}
one sig SetPrice100007i2 extends SetPrice100007 {} {id=-6}
fact {
#{te: TaskEvent | GetPrice100007i2 in te.tokens}<=1
#{te: TaskEvent | GetPrice100007i2 in te.tokens } = #{te: TaskEvent | SetPrice100007i2 in te.tokens }
}
one sig GetPrice100007i3 extends GetPrice100007 {} {id=-5}
one sig SetPrice100007i3 extends SetPrice100007 {} {id=-5}
fact {
#{te: TaskEvent | GetPrice100007i3 in te.tokens}<=1
#{te: TaskEvent | GetPrice100007i3 in te.tokens } = #{te: TaskEvent | SetPrice100007i3 in te.tokens }
}
fact {
all te: TaskEvent | (te.task = BookMeansOfTransport or #{GetPrice100007 & te.tokens}<=0) and (te.task = UseTransport or #{SetPrice100007 & te.tokens}<=0)
some te: TaskEvent | GetPrice100007 in te.tokens implies (all ote: TaskEvent| GetPrice100007 in ote.tokens or SetPrice100007 in ote.tokens implies ote.data&Price = te.data&Price)
}

