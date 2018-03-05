abstract sig Activity {}
abstract sig Payload {}

abstract sig Event{
	task: one Activity,
	data: set Payload,
	tokens: set Token
}

one sig DummyPayload extends Payload {}
fact { no te:Event | DummyPayload in te.data }

one sig DummyActivity extends Activity {}

abstract sig Token {}
abstract sig SameToken extends Token {}
abstract sig DiffToken extends Token {}
lone sig DummySToken extends SameToken{}
lone sig DummyDToken extends DiffToken{}
fact { 
	no DummySToken
	no DummyDToken
	all te:Event| no (te.tokens & SameToken) or no (te.tokens & DiffToken)
}

pred True[]{some TE0}

// declare templates

pred Init(taskA: Activity) { 
	taskA = TE0.task
}

pred Existence(taskA: Activity) { 
	some te: Event | te.task = taskA
}

pred Existence(taskA: Activity, n: Int) {
	#{ te: Event | taskA = te.task } >= n
}

pred Absence(taskA: Activity) { 
	no te: Event | te.task = taskA
}

pred Absence(taskA: Activity, n: Int) {
	#{ te: Event | taskA = te.task } <= n
}

pred Exactly(taskA: Activity, n: Int) {
	#{ te: Event | taskA = te.task } = n
}

pred Choice(taskA, taskB: Activity) { 
	some te: Event | te.task = taskA or te.task = taskB
}

pred ExclusiveChoice(taskA, taskB: Activity) { 
	some te: Event | te.task = taskA or te.task = taskB
	(no te: Event | taskA = te.task) or (no te: Event | taskB = te.task )
}

pred RespondedExistence(taskA, taskB: Activity) {
	(some te: Event | taskA = te.task) implies (some ote: Event | taskB = ote.task)
}

pred Response(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte])
}

pred AlternateResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[te, fte] and (no ite: Event | taskA = ite.task and After[te, ite] and After[ite, fte]))
}

pred ChainResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[te, fte])
}

pred Precedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te])
}

pred AlternatePrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and After[fte, te] and (no ite: Event | taskA = ite.task and After[fte, ite] and After[ite, te]))
}

pred ChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (some fte: Event | taskB = fte.task and Next[fte, te])
}

pred NotRespondedExistence(taskA, taskB: Activity) {
	(some te: Event | taskA = te.task) implies (no te: Event | taskB = te.task)
}

pred NotResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[te, fte])
}

pred NotPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | taskB = fte.task and After[fte, te])
}

pred NotChainResponse(taskA, taskB: Activity) { 
	all te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[te, fte])
}

pred NotChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies (no fte: Event | (DummyActivity = fte.task or taskB = fte.task) and Next[fte, te])
}
//-

pred example { }
run example

---------------------- end of static code block ----------------------

--------------------- generated code starts here ---------------------

one sig TE0 extends Event {}{not task=DummyActivity}
one sig TE1 extends Event {}{not task=DummyActivity}
one sig TE2 extends Event {}{not task=DummyActivity}
one sig TE3 extends Event {}{not task=DummyActivity}
one sig TE4 extends Event {}{not task=DummyActivity}
one sig TE5 extends Event {}
one sig TE6 extends Event {}
one sig TE7 extends Event {}
one sig TE8 extends Event {}
one sig TE9 extends Event {}
one sig TE10 extends Event {}
one sig TE11 extends Event {}
one sig TE12 extends Event {}
one sig TE13 extends Event {}
one sig TE14 extends Event {}
one sig TE15 extends Event {}
one sig TE16 extends Event {}
one sig TE17 extends Event {}
one sig TE18 extends Event {}
one sig TE19 extends Event {}
one sig TE20 extends Event {}
one sig TE21 extends Event {}
one sig TE22 extends Event {}
one sig TE23 extends Event {}
one sig TE24 extends Event {}
pred Next(pre, next: Event){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4 or pre=TE4 and next=TE5 or pre=TE5 and next=TE6 or pre=TE6 and next=TE7 or pre=TE7 and next=TE8 or pre=TE8 and next=TE9 or pre=TE9 and next=TE10 or pre=TE10 and next=TE11 or pre=TE11 and next=TE12 or pre=TE12 and next=TE13 or pre=TE13 and next=TE14 or pre=TE14 and next=TE15 or pre=TE15 and next=TE16 or pre=TE16 and next=TE17 or pre=TE17 and next=TE18 or pre=TE18 and next=TE19 or pre=TE19 and next=TE20 or pre=TE20 and next=TE21 or pre=TE21 and next=TE22 or pre=TE22 and next=TE23 or pre=TE23 and next=TE24}
pred After(b, a: Event){// b=before, a=after
b=TE0 or a=TE24 or b=TE1 and not (a=TE0) or b=TE2 and not (a=TE0 or a=TE1) or b=TE3 and not (a=TE0 or a=TE1 or a=TE2) or b=TE4 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3) or b=TE5 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4) or b=TE6 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5) or b=TE7 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6) or b=TE8 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7) or b=TE9 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7 or a=TE8) or b=TE10 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7 or a=TE8 or a=TE9) or b=TE11 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7 or a=TE8 or a=TE9 or a=TE10) or b=TE12 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13) or b=TE13 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14) or b=TE14 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15) or b=TE15 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19 or a=TE18 or a=TE17 or a=TE16) or b=TE16 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19 or a=TE18 or a=TE17) or b=TE17 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19 or a=TE18) or b=TE18 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20 or a=TE19) or b=TE19 and (a=TE24 or a=TE23 or a=TE22 or a=TE21 or a=TE20) or b=TE20 and (a=TE24 or a=TE23 or a=TE22 or a=TE21) or b=TE21 and (a=TE24 or a=TE23 or a=TE22) or b=TE22 and (a=TE24 or a=TE23)}
one sig ApplyForTrip extends Activity {}
one sig ApproveApplication extends Activity {}
one sig BookTransport extends Activity {}
one sig BookAccomodation extends Activity {}
one sig CollectTickets extends Activity {}
one sig ArchiveDocuments extends Activity {}
one sig UseTransport extends Activity {}
one sig DoSomething extends Activity {}
fact { all te: Event | te.task = DoSomething implies (one Something & te.data)}
fact { all te: Event | te.task = UseTransport implies (one TransportType & te.data and one Something & te.data and one Price & te.data)}
fact { all te: Event | te.task = BookTransport implies (one TransportType & te.data and one Price & te.data and one Speed & te.data)}
fact { all te: Event | lone(Speed & te.data) }
fact { all te: Event | some (Speed & te.data) implies te.task in (BookTransport) }
fact { all te: Event | lone(Price & te.data) }
fact { all te: Event | some (Price & te.data) implies te.task in (BookTransport + UseTransport) }
fact { all te: Event | lone(TransportType & te.data) }
fact { all te: Event | some (TransportType & te.data) implies te.task in (BookTransport + UseTransport) }
fact { all te: Event | lone(Something & te.data) }
fact { all te: Event | some (Something & te.data) implies te.task in (UseTransport + DoSomething) }
abstract sig TransportType extends Payload {}
fact { all te: Event | (lone TransportType & te.data)}
one sig Car extends TransportType{}
one sig Plane extends TransportType{}
one sig Train extends TransportType{}
one sig Bus extends TransportType{}
abstract sig Something extends Payload {}
fact { all te: Event | (lone Something & te.data)}
one sig One extends Something{}
one sig None extends Something{}
one sig Another extends Something{}
abstract sig Price extends Payload {
amount: Int
}
fact { all te: Event | (lone Price & te.data) }
pred Single(pl: Price) {{pl.amount=1}}
fun Amount(pl: Price): one Int {{pl.amount}}
one sig floatBetween0p0and50p0r100000 extends Price{}{amount=15}
one sig floatBetween50p0and100p0r100001 extends Price{}{amount=15}
abstract sig Speed extends Payload {
amount: Int
}
fact { all te: Event | (lone Speed & te.data) }
pred Single(pl: Speed) {{pl.amount=1}}
fun Amount(pl: Speed): one Int {{pl.amount}}
one sig intBetweenm1and150r100002 extends Speed{}{amount=15}
one sig intBetween149and300r100003 extends Speed{}{amount=15}
fact {
Init[ApplyForTrip]
Response[CollectTickets,ArchiveDocuments]
Precedence[BookTransport,ApproveApplication]
Precedence[BookAccomodation,ApproveApplication]
Precedence[CollectTickets,BookTransport]
Precedence[CollectTickets,BookAccomodation]
Absence[BookAccomodation,2]
Absence[BookTransport,3]
Absence[ApplyForTrip,1]
Existence[CollectTickets]
Existence[ArchiveDocuments]
Absence[ArchiveDocuments,1]
Absence[ApproveApplication,1]
NotChainPrecedence[DoSomething,UseTransport]
Existence[UseTransport,10]
Exactly[DoSomething,3]
}

