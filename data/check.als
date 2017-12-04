abstract sig Activity {}
abstract sig Payload {}

abstract sig Event{
	pos: disj Int,
	task: one Activity,
}

fun getHTEventAtPos(givenPos : Int) : one Event{
	{ e: Event | e.pos = givenPos }
}

// declare templates

pred Init(taskA: Activity) {
	one te: Event | taskA = te.task
	one te: Event | taskA = te.task and te.pos = TE0.pos
}

pred Existence(taskA: Activity) {
	some te: Event | te.task = taskA
}

pred Absence(taskA: Activity) {
	no te: Event | te.task = taskA
}

pred Absence(taskA: Activity, n: Int) {
	#{ te: Event | taskA in te.task} <= n
}

// existence(n,A)
//fact {
//	#{ hte: Event | \Activity\ in hte.assoEl } >= n		//tested
//}

// exactly(n,A)
//fact {
//	#{ hte: Event | \Activity\ in hte.assoEl } = n	//tested
//}

pred Choice(taskA, taskB: Activity) {
	some te: Event | te.task = taskA or te.task = taskB
}

pred ExclusiveChoice(taskA, taskB: Activity) {
	some te: Event | te.task = taskA or te.task = taskB
	#{ te: Event | taskA = te.task } = 0 or #{ te: Event | taskB = te.task } = 0
}

pred RespondedExistence(taskA, taskB: Activity) {
	#{ te: Event | taskA = te.task } > 0 implies #{ ote: Event | taskB = ote.task } > 0
}

pred Response(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos > te.pos and taskB = fte.task } > 0
}

pred AlternateResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos > te.pos and taskB = fte.task and #{ ite: Event | ite.pos > te.pos and ite.pos < fte.pos and taskA = ite.task} = 0 } > 0
}

pred ChainResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos = int[te.pos + 1] and taskB = fte.task } > 0
}

pred Precedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos < te.pos and taskB = fte.task } > 0
}

pred AlternatePrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos < te.pos and taskB = fte.task and #{ ite: Event | ite.pos > te.pos and ite.pos < fte.pos and taskA = ite.task} = 0 } > 0
}

pred ChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | int[fte.pos + 1] = te.pos and taskB = fte.task } > 0
}

pred NotRespondedExistence(taskA, taskB: Activity) {
	#{ te: Event | taskA = te.task } > 0 implies #{ te: Event | taskB = te.task } = 0
}

pred NotResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos > te.pos and taskB = fte.task } = 0
}

pred NotPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos < te.pos and taskB = fte.task } = 0
}

pred NotChainResponse(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | fte.pos = int[te.pos + 1] and taskB = fte.task } = 0
}

pred NotChainPrecedence(taskA, taskB: Activity) {
	all te: Event | taskA = te.task implies #{ fte: Event | int[fte.pos + 1] = te.pos and taskB = fte.task } = 0
}
//-

one sig TE0 extends Event {} {pos=-16 task=ApplyForTrip}
one sig TE1 extends Event {} {pos=-15 task=BookMeansOfTransport}
one sig TE2 extends Event {} {pos=-14 task=BookAccomodation}
one sig TE3 extends Event {} {pos=-13 task=ArchiveDocuments}

one sig ApplyForTrip extends Activity {}
one sig BookMeansOfTransport extends Activity {}
one sig BookAccomodation extends Activity {}
one sig ArchiveDocuments extends Activity {}


assert a{ Init[ApplyForTrip]}
assert b{ Precedence[BookMeansOfTransport, ApplyForTrip]}
assert c{ Precedence[BookAccomodation, ApplyForTrip]}
assert d{ Precedence[ArchiveDocuments, BookMeansOfTransport]}
assert e{ Precedence[ArchiveDocuments, BookAccomodation] }
assert f{ Existence[ArchiveDocuments]}

check a for 5 Int
check b for 5 Int
check c for 5 Int
check d for 5 Int
check e for 5 Int
check f for 5 Int

