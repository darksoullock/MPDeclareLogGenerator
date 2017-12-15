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
one sig TE5 extends Event {}{not task=DummyActivity}
one sig TE6 extends Event {}{not task=DummyActivity}
one sig TE7 extends Event {}{not task=DummyActivity}
one sig TE8 extends Event {}{not task=DummyActivity}
one sig TE9 extends Event {}{not task=DummyActivity}
one sig TE10 extends Event {}{not task=DummyActivity}
one sig TE11 extends Event {}{not task=DummyActivity}
one sig TE12 extends Event {}{not task=DummyActivity}
one sig TE13 extends Event {}{not task=DummyActivity}
one sig TE14 extends Event {}{not task=DummyActivity}
one sig TE15 extends Event {}{not task=DummyActivity}
one sig TE16 extends Event {}{not task=DummyActivity}
one sig TE17 extends Event {}{not task=DummyActivity}
one sig TE18 extends Event {}{not task=DummyActivity}
one sig TE19 extends Event {}{not task=DummyActivity}
pred Next(pre, next: Event){pre=TE0 and next=TE1 or pre=TE1 and next=TE2 or pre=TE2 and next=TE3 or pre=TE3 and next=TE4 or pre=TE4 and next=TE5 or pre=TE5 and next=TE6 or pre=TE6 and next=TE7 or pre=TE7 and next=TE8 or pre=TE8 and next=TE9 or pre=TE9 and next=TE10 or pre=TE10 and next=TE11 or pre=TE11 and next=TE12 or pre=TE12 and next=TE13 or pre=TE13 and next=TE14 or pre=TE14 and next=TE15 or pre=TE15 and next=TE16 or pre=TE16 and next=TE17 or pre=TE17 and next=TE18 or pre=TE18 and next=TE19}
pred After(b, a: Event){// b=before, a=after
b=TE0 or a=TE19 or b=TE1 and not (a=TE0) or b=TE2 and not (a=TE0 or a=TE1) or b=TE3 and not (a=TE0 or a=TE1 or a=TE2) or b=TE4 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3) or b=TE5 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4) or b=TE6 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5) or b=TE7 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6) or b=TE8 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7) or b=TE9 and not (a=TE0 or a=TE1 or a=TE2 or a=TE3 or a=TE4 or a=TE5 or a=TE6 or a=TE7 or a=TE8) or b=TE10 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13 or a=TE12 or a=TE11) or b=TE11 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13 or a=TE12) or b=TE12 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14 or a=TE13) or b=TE13 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15 or a=TE14) or b=TE14 and (a=TE19 or a=TE18 or a=TE17 or a=TE16 or a=TE15) or b=TE15 and (a=TE19 or a=TE18 or a=TE17 or a=TE16) or b=TE16 and (a=TE19 or a=TE18 or a=TE17) or b=TE17 and (a=TE19 or a=TE18)}
one sig receive extends Activity {}
one sig hotel extends Activity {}
one sig compensation extends Activity {}
one sig airline extends Activity {}
one sig failedHotel extends Activity {}
one sig failedAirline extends Activity {}
one sig notifyFailure extends Activity {}
one sig bookedHotel extends Activity {}
one sig bookedAirline extends Activity {}
one sig notifyBooked extends Activity {}
one sig creditCard extends Activity {}
fact {
	Exactly[receive, 1]
	Response[receive, hotel] or Response[receive, airline] 
	Precedence[hotel, receive]
	Precedence[airline, receive]
	Absence[compensation, 1]
	NotResponse[compensation, hotel]
	NotResponse[compensation, airline]
	Precedence[compensation, failedHotel] or Precedence[compensation, failedAirline]
	Response[hotel, failedHotel] or Response[hotel, bookedHotel]
	Precedence[bookedHotel, hotel]
	Precedence[failedHotel, hotel]
	Response[airline, failedAirline] or Response[airline, bookedAirline]
	Precedence[bookedAirline, airline]
	Precedence[failedAirline, airline]
	Absence[notifyFailure, 1]
	Absence[notifyBooked, 1]
	Absence[creditCard, 1]
	Precedence[notifyFailure, compensation]
	NotRespondedExistence[notifyFailure, creditCard]
	ExclusiveChoice[notifyFailure, creditCard]
	NotResponse[creditCard, airline]
	NotResponse[creditCard, hotel]
	Precedence[creditCard, bookedHotel] or Precedence[creditCard, bookedAirline]
	Precedence[notifyBooked, creditCard]
	Response[creditCard, notifyBooked]
}

