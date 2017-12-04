abstract sig Event{
	pos: disj Int,
	task: one Activity,
	data: set Payload
}

pred example { }
run example

one sig TE0 extends Event {} {pos=-32}
one sig TE1 extends Event {} {pos=-31}
one sig TE2 extends Event {} {pos=-30}
one sig TE3 extends Event {} {pos=-29}
one sig TE4 extends Event {} {pos=-28}
one sig TE5 extends Event {} {pos=-27}
one sig TE6 extends Event {} {pos=-26}
one sig TE7 extends Event {} {pos=-25}
one sig TE8 extends Event {} {pos=-24}
one sig TE9 extends Event {} {pos=-23}
one sig TE10 extends Event {} {pos=-22}
one sig TE11 extends Event {} {pos=-21}
one sig TE12 extends Event {} {pos=-20}
one sig TE13 extends Event {} {pos=-19}
one sig TE14 extends Event {} {pos=-18}
one sig TE15 extends Event {} {pos=-17}
one sig TE16 extends Event {} {pos=-16}
one sig TE17 extends Event {} {pos=-15}
one sig TE18 extends Event {} {pos=-14}
one sig TE19 extends Event {} {pos=-13}
/*
one sig TE20 extends Event {} {pos=-12}
one sig TE21 extends Event {} {pos=-11}
one sig TE22 extends Event {} {pos=-10}
one sig TE23 extends Event {} {pos=-9}
one sig TE24 extends Event {} {pos=-8}
one sig TE25 extends Event {} {pos=-7}
one sig TE26 extends Event {} {pos=-6}
one sig TE27 extends Event {} {pos=-5}
one sig TE28 extends Event {} {pos=-4}
one sig TE29 extends Event {} {pos=-3}
one sig TE30 extends Event {} {pos=-2}
one sig TE31 extends Event {} {pos=-1}
one sig TE32 extends Event {} {pos=-0}
one sig TE33 extends Event {} {pos=1}
one sig TE34 extends Event {} {pos=2}
one sig TE35 extends Event {} {pos=3}
one sig TE36 extends Event {} {pos=4}
one sig TE37 extends Event {} {pos=5}
one sig TE38 extends Event {} {pos=6}
one sig TE39 extends Event {} {pos=7}
one sig TE40 extends Event {} {pos=8}
one sig TE51 extends Event {} {pos=9}
one sig TE52 extends Event {} {pos=10}
one sig TE53 extends Event {} {pos=11}
one sig TE54 extends Event {} {pos=12}
one sig TE55 extends Event {} {pos=13}
one sig TE56 extends Event {} {pos=14}
one sig TE57 extends Event {} {pos=15}
one sig TE58 extends Event {} {pos=16}
one sig TE59 extends Event {} {pos=17}
one sig TE50 extends Event {} {pos=18}
*/

abstract sig Activity {}

one sig Dummy extends Activity {}
fact {all te:Event | te.task=Dummy implies #{dte:Event | (not dte.task=Dummy) and dte.pos>te.pos} = 0  }
fact {#{te:Event | te.task=Dummy }<=0}


fun getHTEventAtPos(givenPos : Int) : one Event{
	{ e: Event | e.pos = givenPos }
}


// -----------------------------------------------------------

pred Existence(taskA: Activity) {
	some te: Event | te.task = taskA
}

pred Response(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos > te.pos and taskB = fte.task } > 0
}

pred Precedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos < te.pos and taskB = fte.task } > 0
}



one sig ApplyForTrip extends Activity {}
one sig ApproveApplication extends Activity {}
one sig BookMeansOfTransport extends Activity {}
one sig BookAccomodation extends Activity {}
one sig CollectTickets extends Activity {}
one sig ArchiveDocuments extends Activity {}
one sig UseTransport extends Activity {}
one sig DoSomething extends Activity {}


//init
pred Init(taskA: Activity) {
	one te: Event | taskA = te.task
	one te: Event | taskA = te.task and te.pos = TE0.pos
}

fact {Init[ApplyForTrip] }



fact { Response[CollectTickets, ArchiveDocuments] }

////

abstract sig Payload {}

//data def
abstract sig TransportType extends Payload {}

one sig Car extends TransportType{}
one sig Plane extends TransportType{}
fact { all hte: Event | #{TransportType & hte.data} <= 1 }

fact { all hte: Event | #{TransportType & hte.data} = 1 iff hte.task in (BookMeansOfTransport + UseTransport) }

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

fact { all hte: Event | #{Price & hte.data} <= 1 }
fact { all hte: Event | #{Price & hte.data} = 1 iff hte.task in (BookMeansOfTransport + BookAccomodation) }

fact { all hte: Event | hte.task in BookMeansOfTransport and Car in hte.data implies hte.data & Price in LessThan101 + Equal101 + Between101And204 + Equal204 + MoreThan204 }
fact { all hte: Event | hte.task in BookMeansOfTransport and Plane in hte.data implies hte.data & Price in LessThan103 + Equal103 + Between103And202 + Equal202 + MoreThan202 }
fact { all hte: Event | BookAccomodation = hte.task implies hte.data & Price in LessThan100 + Equal100 + Between100And120 + Equal120 + Between120And150 + Equal150 + Between150And200 + Equal200 + MoreThan200 }

//-



fact {
	#{ hte: Event | BookAccomodation = hte.task } <3
}


fact {
	#{ hte: Event | BookMeansOfTransport = hte.task } < 4
}

fact {
	//#{ hte: Event | UseTransport = hte.task } = #{ hte: Event | BookMeansOfTransport = hte.task }
}


fact {
	all te: Event | UseTransport = te.task implies #{ fte: Event | (fte.pos = int[te.pos + 1]) and DoSomething = fte.task } > 0
}


fact {
	Existence[DoSomething]
}

fact {
	//all hte: Event | BookMeansOfTransport = hte.task implies #existsInAfter[hte, UseTransport] > 0
}

pred OneIn(oneset: set Payload, otherset: set Payload) {
	{ #{oneset & otherset} = 1 }
}

pred NIn(oneset: set Payload, otherset: set Payload, n: Int) {
	{ #{oneset & otherset} = n }
}

fun existsInAfterData(currentEvent: Event, futureActivity: Activity, _data: Payload) : set Event {
	{ hte: Event | hte.pos > currentEvent.pos and hte.task = futureActivity and #{_data& hte.data}>0 }
}
fun existsData(currentEvent: Event, otherEvent: Activity, _data: Payload) : set Event {
	{ hte: Event | hte.task = otherEvent and #{_data& hte.data}>0 }
}

fact { 
	all hte: Event | hte.task = BookMeansOfTransport and Car in hte.data and #{hte.data&(Between101And204 + Equal204 + MoreThan204)}>0 implies #existsData[hte,BookAccomodation,(Between100And120 + Equal120 + Between120And150 + Equal150 + Between150And200 + Equal200 + MoreThan200)] > 0
}

fact { 
	all hte: Event | hte.task = BookMeansOfTransport and Plane in hte.data and #{hte.data&(LessThan103 + Equal103 + Between103And202)}>0 implies #existsData[hte,BookAccomodation,(LessThan100 + Equal100 + Between100And120 + Equal120 + Between120And150)] > 0
}


fact { 
	all hte: Event | hte.task = BookMeansOfTransport and Plane in hte.data and #{hte.data&(Between103And202 + Equal202 + MoreThan202)}>0 implies #existsData[hte,BookAccomodation,(Between120And150 + Equal150 + Between150And200 + Equal200 + MoreThan200)] > 0
}


fact { 
	all hte: Event | hte.task = BookMeansOfTransport and Car in hte.data and #{hte.data&(MoreThan204)}>0 implies #existsData[hte,BookAccomodation,(MoreThan200)] > 0
}


fact { 
	all hte: Event | hte.task = BookMeansOfTransport and Car in hte.data and #{hte.data&(LessThan101 + Equal101)}>0 implies #existsData[hte,BookAccomodation,(LessThan100 + Equal100)] > 0
}






fact {
	Precedence[BookMeansOfTransport, ApproveApplication]
	Precedence[BookAccomodation, ApproveApplication]
	Precedence[CollectTickets, BookMeansOfTransport]
	Precedence[CollectTickets, BookAccomodation] 
}

fact { lone te: Event | ApproveApplication = te.task }
fact { one te: Event | CollectTickets = te.task }
fact { one te: Event | ArchiveDocuments = te.task }

fun exists(asso: Activity) : set Event {
	{ hte: Event | asso = hte.task }
}



