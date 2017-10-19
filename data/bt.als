abstract sig TaskEvent{
	pos: disj Int,
	task: one Task,
	data: set Payload
}

pred example { }
run example

one sig TE0 extends TaskEvent {} {pos=-32}
one sig TE1 extends TaskEvent {} {pos=-31}
one sig TE2 extends TaskEvent {} {pos=-30}
one sig TE3 extends TaskEvent {} {pos=-29}
one sig TE4 extends TaskEvent {} {pos=-28}
one sig TE5 extends TaskEvent {} {pos=-27}
one sig TE6 extends TaskEvent {} {pos=-26}
one sig TE7 extends TaskEvent {} {pos=-25}
one sig TE8 extends TaskEvent {} {pos=-24}
one sig TE9 extends TaskEvent {} {pos=-23}
one sig TE10 extends TaskEvent {} {pos=-22}
one sig TE11 extends TaskEvent {} {pos=-21}
one sig TE12 extends TaskEvent {} {pos=-20}
one sig TE13 extends TaskEvent {} {pos=-19}
one sig TE14 extends TaskEvent {} {pos=-18}
one sig TE15 extends TaskEvent {} {pos=-17}
one sig TE16 extends TaskEvent {} {pos=-16}
one sig TE17 extends TaskEvent {} {pos=-15}
one sig TE18 extends TaskEvent {} {pos=-14}
one sig TE19 extends TaskEvent {} {pos=-13}
/*
one sig TE20 extends TaskEvent {} {pos=-12}
one sig TE21 extends TaskEvent {} {pos=-11}
one sig TE22 extends TaskEvent {} {pos=-10}
one sig TE23 extends TaskEvent {} {pos=-9}
one sig TE24 extends TaskEvent {} {pos=-8}
one sig TE25 extends TaskEvent {} {pos=-7}
one sig TE26 extends TaskEvent {} {pos=-6}
one sig TE27 extends TaskEvent {} {pos=-5}
one sig TE28 extends TaskEvent {} {pos=-4}
one sig TE29 extends TaskEvent {} {pos=-3}
one sig TE30 extends TaskEvent {} {pos=-2}
one sig TE31 extends TaskEvent {} {pos=-1}
one sig TE32 extends TaskEvent {} {pos=-0}
one sig TE33 extends TaskEvent {} {pos=1}
one sig TE34 extends TaskEvent {} {pos=2}
one sig TE35 extends TaskEvent {} {pos=3}
one sig TE36 extends TaskEvent {} {pos=4}
one sig TE37 extends TaskEvent {} {pos=5}
one sig TE38 extends TaskEvent {} {pos=6}
one sig TE39 extends TaskEvent {} {pos=7}
one sig TE40 extends TaskEvent {} {pos=8}
one sig TE51 extends TaskEvent {} {pos=9}
one sig TE52 extends TaskEvent {} {pos=10}
one sig TE53 extends TaskEvent {} {pos=11}
one sig TE54 extends TaskEvent {} {pos=12}
one sig TE55 extends TaskEvent {} {pos=13}
one sig TE56 extends TaskEvent {} {pos=14}
one sig TE57 extends TaskEvent {} {pos=15}
one sig TE58 extends TaskEvent {} {pos=16}
one sig TE59 extends TaskEvent {} {pos=17}
one sig TE50 extends TaskEvent {} {pos=18}
*/

abstract sig Task {}

one sig Dummy extends Task {}
fact {all te:TaskEvent | te.task=Dummy implies #{dte:TaskEvent | (not dte.task=Dummy) and dte.pos>te.pos} = 0  }
fact {#{te:TaskEvent | te.task=Dummy }<=0}


fun getHTEventAtPos(givenPos : Int) : one TaskEvent{
	{ e: TaskEvent | e.pos = givenPos }
}


// -----------------------------------------------------------

pred Existence(taskA: Task) { 
	some te: TaskEvent | te.task = taskA
}

pred Response(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos > te.pos and taskB = fte.task } > 0
}

pred Precedence(taskA, taskB: Task) { 
	all te: TaskEvent | taskA = te.task implies #{ fte: TaskEvent | fte.pos < te.pos and taskB = fte.task } > 0
}



one sig ApplyForTrip extends Task {}
one sig ApproveApplication extends Task {}
one sig BookMeansOfTransport extends Task {}
one sig BookAccomodation extends Task {}
one sig CollectTickets extends Task {}
one sig ArchiveDocuments extends Task {}
one sig UseTransport extends Task {}
one sig DoSomething extends Task {}


//init
pred Init(taskA: Task) { 
	one te: TaskEvent | taskA = te.task
	one te: TaskEvent | taskA = te.task and te.pos = TE0.pos
}

fact {Init[ApplyForTrip] }



fact { Response[CollectTickets, ArchiveDocuments] }

////

abstract sig Payload {}

//data def
abstract sig TransportType extends Payload {}

one sig Car extends TransportType{}
one sig Plane extends TransportType{}
fact { all hte: TaskEvent | #{TransportType & hte.data} <= 1 }

fact { all hte: TaskEvent | #{TransportType & hte.data} = 1 iff hte.task in (BookMeansOfTransport + UseTransport) }

//-

//numeric data def
abstract sig Price extends Payload {}

one sig LessThan101 extends Price {}
one sig Equal101 extends Price {}
one sig Between101And204 extends Price {}
one sig Equal204 extends Price {}
one sig MoreThan204 extends Price {}
one sig LessThan103 extends Price {}
one sig Equal103 extends Price {}
one sig Between103And202 extends Price {}
one sig Equal202 extends Price {}
one sig MoreThan202 extends Price {}
one sig LessThan100 extends Price {}
one sig Equal100 extends Price {}
one sig Between100And120 extends Price {}
one sig Equal120 extends Price {}
one sig Between120And150 extends Price {}
one sig Equal150 extends Price {}
one sig Between150And200 extends Price {}
one sig Equal200 extends Price {}
one sig MoreThan200 extends Price {}

fact { all hte: TaskEvent | #{Price & hte.data} <= 1 }
fact { all hte: TaskEvent | #{Price & hte.data} = 1 iff hte.task in (BookMeansOfTransport + BookAccomodation) }

fact { all hte: TaskEvent | hte.task in BookMeansOfTransport and Car in hte.data implies hte.data & Price in LessThan101 + Equal101 + Between101And204 + Equal204 + MoreThan204 }
fact { all hte: TaskEvent | hte.task in BookMeansOfTransport and Plane in hte.data implies hte.data & Price in LessThan103 + Equal103 + Between103And202 + Equal202 + MoreThan202 }
fact { all hte: TaskEvent | BookAccomodation = hte.task implies hte.data & Price in LessThan100 + Equal100 + Between100And120 + Equal120 + Between120And150 + Equal150 + Between150And200 + Equal200 + MoreThan200 }

//-



fact {
	#{ hte: TaskEvent | BookAccomodation = hte.task } <3
}


fact {
	#{ hte: TaskEvent | BookMeansOfTransport = hte.task } < 4
}

fact {
	//#{ hte: TaskEvent | UseTransport = hte.task } = #{ hte: TaskEvent | BookMeansOfTransport = hte.task }
}


fact {
	all te: TaskEvent | UseTransport = te.task implies #{ fte: TaskEvent | (fte.pos = int[te.pos + 1]) and DoSomething = fte.task } > 0
}


fact {
	Existence[DoSomething]
}

fact {
	//all hte: TaskEvent | BookMeansOfTransport = hte.task implies #existsInAfter[hte, UseTransport] > 0
}

pred OneIn(oneset: set Payload, otherset: set Payload) {
	{ #{oneset & otherset} = 1 }
}

pred NIn(oneset: set Payload, otherset: set Payload, n: Int) {
	{ #{oneset & otherset} = n }
}

fun existsInAfterData(currentEvent: TaskEvent, futureTask: Task, _data: Payload) : set TaskEvent {
	{ hte: TaskEvent | hte.pos > currentEvent.pos and hte.task = futureTask and #{_data& hte.data}>0 }
}
fun existsData(currentEvent: TaskEvent, otherEvent: Task, _data: Payload) : set TaskEvent {
	{ hte: TaskEvent | hte.task = otherEvent and #{_data& hte.data}>0 }
}

fact { 
	all hte: TaskEvent | hte.task = BookMeansOfTransport and Car in hte.data and #{hte.data&(Between101And204 + Equal204 + MoreThan204)}>0 implies #existsData[hte,BookAccomodation,(Between100And120 + Equal120 + Between120And150 + Equal150 + Between150And200 + Equal200 + MoreThan200)] > 0 
}

fact { 
	all hte: TaskEvent | hte.task = BookMeansOfTransport and Plane in hte.data and #{hte.data&(LessThan103 + Equal103 + Between103And202)}>0 implies #existsData[hte,BookAccomodation,(LessThan100 + Equal100 + Between100And120 + Equal120 + Between120And150)] > 0 
}


fact { 
	all hte: TaskEvent | hte.task = BookMeansOfTransport and Plane in hte.data and #{hte.data&(Between103And202 + Equal202 + MoreThan202)}>0 implies #existsData[hte,BookAccomodation,(Between120And150 + Equal150 + Between150And200 + Equal200 + MoreThan200)] > 0 
}


fact { 
	all hte: TaskEvent | hte.task = BookMeansOfTransport and Car in hte.data and #{hte.data&(MoreThan204)}>0 implies #existsData[hte,BookAccomodation,(MoreThan200)] > 0 
}


fact { 
	all hte: TaskEvent | hte.task = BookMeansOfTransport and Car in hte.data and #{hte.data&(LessThan101 + Equal101)}>0 implies #existsData[hte,BookAccomodation,(LessThan100 + Equal100)] > 0 
}






fact {
	Precedence[BookMeansOfTransport, ApproveApplication]
	Precedence[BookAccomodation, ApproveApplication]
	Precedence[CollectTickets, BookMeansOfTransport]
	Precedence[CollectTickets, BookAccomodation] 
}

fact { lone te: TaskEvent | ApproveApplication = te.task }
fact { one te: TaskEvent | CollectTickets = te.task }
fact { one te: TaskEvent | ArchiveDocuments = te.task }

fun exists(asso: Task) : set TaskEvent {
	{ hte: TaskEvent | asso = hte.task }
}



