-- 1
-- a) enum ou one sig com abstract Light
/*
Example:
enum Time {Morning, Noon, Night}
-- ou
abstract sig Time {}
one sig Morning, Noon, Night extends Time {
  time: Time
}
*/

-- b) teachers some -> one rooms

-- c) R = {(a,b), (b,c), (c,b)}
-- ^R = {(a,b), (b,c), (c,b), (a,c), (b,b), (c, c)}

-- d) R1 = {(a,a), (a,b), (b,c)} e R2 = {(a,a), (a,c)}
-- R1.R2 = {(a,a), (a,c)}

-- e)
-- R1={(a,b),(b,b),(c,b)}, R2={(a,a)} e R3={(b)}
-- (R1 ++ R2) :> R3 = {(a,a), (b,b), (c,b)} :> {(b)} = {(b,b), (c,b)}

-- f) sig Task{precendences: set Task}
-- fact acyclic {no t: Task | t in t.^precedences}
-- fact acyclic {no t: Task | t->t in ^precedences}
-- fact acyclic {no ^precedences & iden}

-- g) sig Exam { grades: Student -> lone Int }
/*
fun results(s: Student): Exam->Int {
  {e: Exam, g: e.s.grades}
}
*/

-- 2
sig Medicin {
  incompatibilities: set Medicin - this // other medicins incompatible with this one
}

fact incompatibilities_symmetry {
  -- if m1 is incompatible with m2, then the opposite also holds
  incompatibilities = ~incompatibilities
}

sig Doctor { }
sig Patient {
  doctors: some Doctor, -- doctors (1 or more) of this patient (only them can prescribe medicins)
  alergies: set Medicin, -- medicins (0 or more) that this patient is alergic to
  prescriptions: Doctor lone -> set Medicin -- current (active) prescriptions, as a set
  -- of pairs (doctor, medicin prescribed), with each medicin prescribed by at most one doctor
}

fun medicins[p: Patient] : set Medicin {
  Doctor.(p.prescriptions)
}

pred safety_invariants[p: Patient] {
  -- a patient cannot be prescribed a medicin to which he/she is alergic
  no p.medicins & p.alergies
  -- a patient cannot be prescribed mutually incompatible medicins
  no m1, m2: p.medicins | m1 in m2.incompatibilities
  -- medicins can be prescribed only by the patient's doctors
  p.prescriptions.Medicin in p.doctors
}

-- doctor d prescribes medicin m to patient p, resulting in a new patient state p'
pred prescribe[d: Doctor, m: Medicin, p, p': Patient] {
  -- pre-conditions (don't use predicate safety_invariants!)
  d in p.doctors -- (can be removed by using +d in post-condition)
  not m in p.alergies + p.medicins.incompatibilities
  not m in p.medicins -- (can be removed using -Doctor->m in post-condition)

  -- post-conditions (don't use predicate safety_invariants!)
  p'.doctors = p.doctors -- (or: + d)
  p'.alergies = p.alergies
  p'.prescriptions = p.prescriptions + d->m -- (or: p'.prescriptions = (p.prescriptions - Doctor->m) + d->m
}
