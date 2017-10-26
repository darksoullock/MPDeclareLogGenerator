abstract sig Task {}
abstract sig Payload {}

abstract sig TaskEvent{
	pos: disj Int,
	task: one Task,
	data: set Payload
}

one sig Dummy extends Task {}
fact {all te:TaskEvent | te.task=Dummy implies #{dte:TaskEvent | (not dte.task=Dummy) and dte.pos>te.pos} = 0  }

one sig DummyPayload extends Payload {}
fact { #{te:TaskEvent | DummyPayload in te.data} <= 0 }

fun getHTEventAtPos(givenPos : Int) : one TaskEvent{
	{ e: TaskEvent | e.pos = givenPos }
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

fact {#{te:TaskEvent | te.task=Dummy } <= 15}
lone sig TE0 extends TaskEvent {} {pos=-16}
lone sig TE1 extends TaskEvent {} {pos=-15}
lone sig TE2 extends TaskEvent {} {pos=-14}
lone sig TE3 extends TaskEvent {} {pos=-13}
lone sig TE4 extends TaskEvent {} {pos=-12}
lone sig TE5 extends TaskEvent {} {pos=-11}
lone sig TE6 extends TaskEvent {} {pos=-10}
lone sig TE7 extends TaskEvent {} {pos=-9}
lone sig TE8 extends TaskEvent {} {pos=-8}
lone sig TE9 extends TaskEvent {} {pos=-7}
lone sig TE10 extends TaskEvent {} {pos=-6}
lone sig TE11 extends TaskEvent {} {pos=-5}
lone sig TE12 extends TaskEvent {} {pos=-4}
lone sig TE13 extends TaskEvent {} {pos=-3}
lone sig TE14 extends TaskEvent {} {pos=-2}
lone sig TE15 extends TaskEvent {} {pos=-1}
lone sig TE16 extends TaskEvent {} {pos=0}
lone sig TE17 extends TaskEvent {} {pos=1}
lone sig TE18 extends TaskEvent {} {pos=2}
lone sig TE19 extends TaskEvent {} {pos=3}
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
fact { all te: TaskEvent | te.task = UseTransport implies #{(TransportType + Something) & te.data} = 2 }
fact { all te: TaskEvent | #{Speed & te.data} <= 1 }
fact { all te: TaskEvent | #{Speed & te.data} = 1 implies te.task in (BookMeansOfTransport) }
fact { all te: TaskEvent | #{Price & te.data} <= 1 }
fact { all te: TaskEvent | #{Price & te.data} = 1 implies te.task in (BookMeansOfTransport) }
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
abstract sig Price extends Payload {}
fact { all te: TaskEvent | #{Price & te.data} <= 1 }
one sig intBetween50and200r100003 extends Price{}
one sig intBetween0and50r100001 extends Price{}
one sig intEqualsTo200r100004 extends Price{}
one sig intEqualsTo50r100002 extends Price{}
one sig intBetween200and300r100005 extends Price{}
one sig intEqualsTo300r100006 extends Price{}
one sig intEqualsTo0r100000 extends Price{}
abstract sig Speed extends Payload {}
fact { all te: TaskEvent | #{Speed & te.data} <= 1 }
one sig intEqualsTo0r100007 extends Speed{}
one sig intBetween50and300r100010 extends Speed{}
one sig intEqualsTo50r100009 extends Speed{}
one sig intEqualsTo300r100011 extends Speed{}
one sig intBetween0and50r100008 extends Speed{}
fact { no te: TaskEvent | te.task = BookMeansOfTransport and p100012[te.data] }
pred p100012(A: set Payload) { { (A&Price in (intBetween50and200r100003 + intEqualsTo200r100004 + intBetween200and300r100005 + intEqualsTo300r100006) and A&Speed in (intBetween50and300r100010 + intEqualsTo50r100009 + intEqualsTo300r100011)) } }
fact { all te: TaskEvent | (BookMeansOfTransport = te.task and p100013[te.data]) implies #{ ote: TaskEvent | UseTransport = ote.task and p100013c[te.data, ote.data]} > 0 }
pred p100013(A: set Payload) { { A&Price in (intEqualsTo50r100002) } }
pred p100013c(A, B: set Payload) { { B&Price in (intEqualsTo200r100004) } }

