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
one sig administratieftariefeerstepol extends Task {}
one sig vervolgconsultpoliklinisch extends Task {}
one sig aannamelaboratoriumonderzoek extends Task {}
one sig ordertarief extends Task {}
one sig albumine extends Task {}
one sig alkalischefosfatasekinetisch extends Task {}
one sig telefonischconsult extends Task {}
one sig bacteriologisconderzoekmetkweeknie extends Task {}
one sig cytologischonderzoekectocervix extends Task {}
one sig histologischonderzoekbioptennno extends Task {}
fact { all te: TaskEvent | te.task = histologischonderzoekbioptennno implies #{(Group) & te.data} = 1 }
fact { all te: TaskEvent | te.task = bacteriologisconderzoekmetkweeknie implies #{(Group) & te.data} = 1 }
fact { all te: TaskEvent | te.task = aannamelaboratoriumonderzoek implies #{(Group + SpecialismCode + Section) & te.data} = 3 }
fact { all te: TaskEvent | te.task = administratieftariefeerstepol implies #{(ProducerCode + DiagnosisCode) & te.data} = 2 }
fact { all te: TaskEvent | te.task = cytologischonderzoekectocervix implies #{(Group) & te.data} = 1 }
fact { all te: TaskEvent | #{Group & te.data} <= 1 }
fact { all te: TaskEvent | #{Group & te.data} = 1 implies te.task in (bacteriologisconderzoekmetkweeknie + cytologischonderzoekectocervix + histologischonderzoekbioptennno + aannamelaboratoriumonderzoek) }
fact { all te: TaskEvent | #{DiagnosisCode & te.data} <= 1 }
fact { all te: TaskEvent | #{DiagnosisCode & te.data} = 1 implies te.task in (administratieftariefeerstepol) }
fact { all te: TaskEvent | #{SpecialismCode & te.data} <= 1 }
fact { all te: TaskEvent | #{SpecialismCode & te.data} = 1 implies te.task in (aannamelaboratoriumonderzoek) }
fact { all te: TaskEvent | #{Section & te.data} <= 1 }
fact { all te: TaskEvent | #{Section & te.data} = 1 implies te.task in (aannamelaboratoriumonderzoek) }
fact { all te: TaskEvent | #{ProducerCode & te.data} <= 1 }
fact { all te: TaskEvent | #{ProducerCode & te.data} = 1 implies te.task in (administratieftariefeerstepol) }
fact {
Response[aannamelaboratoriumonderzoek, ordertarief]
RespondedExistence[administratieftariefeerstepol, aannamelaboratoriumonderzoek]
NotResponse[aannamelaboratoriumonderzoek, vervolgconsultpoliklinisch]
AlternatePrecedence[vervolgconsultpoliklinisch, administratieftariefeerstepol]
RespondedExistence[vervolgconsultpoliklinisch, administratieftariefeerstepol]
}
abstract sig ProducerCode extends Payload {}
fact { all te: TaskEvent | #{ProducerCode & te.data} <= 1 }
one sig SIOG extends ProducerCode{}
one sig SGAL extends ProducerCode{}
one sig SGNA extends ProducerCode{}
abstract sig Group extends Payload {}
fact { all te: TaskEvent | #{Group & te.data} <= 1 }
one sig MedicalMicrobiology extends Group{}
one sig Pathology extends Group{}
one sig GeneralLabClinicalChemistry extends Group{}
abstract sig SpecialismCode extends Payload {}
fact { all te: TaskEvent | #{SpecialismCode & te.data} <= 1 }
one sig c86 extends SpecialismCode{}
one sig scDEF extends SpecialismCode{}
abstract sig DiagnosisCode extends Payload {}
fact { all te: TaskEvent | #{DiagnosisCode & te.data} <= 1 }
one sig c106 extends DiagnosisCode{}
one sig dcDEF extends DiagnosisCode{}
abstract sig Section extends Payload {}
fact { all te: TaskEvent | #{Section & te.data} <= 1 }
one sig Section4 extends Section{}
one sig sDEF extends Section{}
fact { all te: TaskEvent | (administratieftariefeerstepol = te.task and p100000[te]) implies #{ fte: TaskEvent | fte.pos > te.pos and albumine = fte.task and p100000c[te, fte] } > 0 }
pred p100000(A: set TaskEvent) { { ((A.data&ProducerCode=SIOG) or (A.data&DiagnosisCode=c106)) } }
pred p100000c(A, T: set TaskEvent) { { 1=1 } }
fact { no te: TaskEvent | te.task = bacteriologisconderzoekmetkweeknie and p100001[te] }
pred p100001(A: set TaskEvent) { { (not A.data&Group=MedicalMicrobiology) } }
fact { no te: TaskEvent | te.task = cytologischonderzoekectocervix and p100002[te] }
pred p100002(A: set TaskEvent) { { (not A.data&Group=Pathology) } }
fact { no te: TaskEvent | te.task = histologischonderzoekbioptennno and p100003[te] }
pred p100003(A: set TaskEvent) { { (not A.data&Group=Pathology) } }
fact { all te: TaskEvent | (telefonischconsult = te.task and p100004[te]) implies #{ ote: TaskEvent | alkalischefosfatasekinetisch = ote.task and p100004c[te, ote]} = 0 }
pred p100004(A: set TaskEvent) { { ((A.data&ProducerCode=SGAL) or (A.data&ProducerCode=SGNA)) } }
pred p100004c(A, T: set TaskEvent) { { 1=1 } }
fact { no te: TaskEvent | te.task = aannamelaboratoriumonderzoek and p100005[te] }
pred p100005(A: set TaskEvent) { { ((A.data&Section=Section4) and ((A.data&SpecialismCode=c86) and (not A.data&Group=GeneralLabClinicalChemistry))) } }

