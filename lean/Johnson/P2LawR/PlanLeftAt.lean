-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/PlanLeftAt.lean: TESTS WITH CODE, EACH WITH ITS LAW, FOR THE CLAUSES OF THE LAST
TABLE's TEST ON THE PLAN PlanAt (Johnson/LLT25R/LastFive.lean) THAT HAD NONE: "the radius fits" ·
"the IOP as written in Lean tells a tree at the member's seat" · "no column of the frame at that
tree is deeper than it"; AND SO FOR PlanOk₃'s FIELD planAt (Johnson/LLT25R/LastOwedCore.lean), in
its own text. So that whoever evaluates the test evaluates the clause itself. STATED AND
PROVED. GENERAL IN EVERY LETTER: no fixed value stands here: no kernel bears a size.
  aOf_eq_B      the library's aOf (Johnson/Pack/Port.lean) IS the test's aOfB
                (Johnson/Desc/K12/Law/MeetsOk.lean): rfl.
  radB · radB_iff          clause 2.
  toldB · toldB_iff        clause 4. told_of_seatFits: it also follows from clause 3.
  fitsAtB · fitsAtB_iff    clause 5, with its "for every o": over fitsB_iff.
  noDeeperB · noDeeperB_iff   clause 6.
  planAt5B · **planAt_iff**   the five as one Bool (clause 1 by tieB | tie_iff): under
                clause 3 its yes is PlanAt, both ways.
  planAtAllB · **planAtAll_law**   over a list of members and a list of stages: the field's text:
                ∀ x ∈ mine, ∀ st rest, stages = st :: rest → PlanAt cs G Fr r st x.
Limits. CLAUSE 3 (SeatFits) STAYS A PREMISE: it has a test with laws in other files
(seatsFitB, Johnson/Desc/PlanMem.lean; Johnson/Top/H0/K2Caller/SeatFitsB.lean): not called here. A
law "the test says yes → the clause holds" is empty where the test never says yes: NO VALUE IS
EVALUATED HERE. The tests have code wherever the letters r, G and Fr have. Nothing on soundness or
on hiding.

-/
import Johnson.LLT25R.LastFive
import Johnson.LLT25R.PlanAtB
import Johnson.ToldDescR.TieB
import Johnson.Desc.K12.Law.MeetsOk

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P2Law.PlanLeft
open OnBytes OnBytes.Slice Johnson.Pack
open VerifiableInference.Desc VerifiableInference.Desc.K12.Coin VerifiableInference.Desc.Sound
open H2K.Pub (sgOf)
open H2K.Pin (aOfB)
open LLT25 (PlanAt fitsB fitsB_iff)
open ToldDesc (tieB tie_iff)

/-- The library's logarithm of the long positions is the test's. -/
theorem aOf_eq_B (cs : Codes) (s : OracleShape) : aOf cs s = aOfB cs s := rfl

/-- Clause 2, "the radius fits", as a test. -/
def radB (cs : Codes) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage) (x : Mem) : Bool :=
  decide (r (sgOf st).st <
    ((x.1.l.get x.2).2 + 1) * 2 ^ ((sgOf st).C.a - aOfB cs (x.1.l.get x.2).1))

theorem radB_iff (cs : Codes) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage) (x : Mem) :
    radB cs r st x = true ↔ r (sgOf st).st <
      ((x.1.l.get x.2).2 + 1) * 2 ^ ((sgOf st).C.a - aOf cs (x.1.l.get x.2).1) := by
  unfold radB
  rw [decide_eq_true_eq, aOf_eq_B]

variable {Xi : Type} (G : FileDescription Xi)

/-- Clause 4, "a tree is told at the member's seat", as a test. -/
def toldB (x : Mem) : Bool := (G.oracleAt (seatOf x).1).isSome

theorem toldB_iff (x : Mem) : toldB G x = true ↔ ∃ o, G.oracleAt (seatOf x).1 = some o :=
  Option.isSome_iff_exists

/-- Clause 4 follows from clause 3. -/
theorem told_of_seatFits (cs : Codes) (x : Mem) (h : SeatFits G cs x.1.l x.1.seat) :
    ∃ o, G.oracleAt (seatOf x).1 = some o := by
  obtain ⟨o, _, ho, _⟩ := h x.2
  exact ⟨o, ho⟩

/-- Clause 5, as a test: fitsB at the told tree's depth. -/
def fitsAtB (cs : Codes) (st : Fmt.M1.Stage) (x : Mem) : Bool :=
  match G.oracleAt (seatOf x).1 with
  | some o => fitsB cs st (x.1.l.get x.2).1 o.logLength
  | none => true

theorem fitsAtB_iff (cs : Codes) (st : Fmt.M1.Stage) (x : Mem) :
    fitsAtB G cs st x = true ↔
      ∀ o, G.oracleAt (seatOf x).1 = some o → ShapeFits cs st (x.1.l.get x.2).1 o.logLength := by
  unfold fitsAtB
  cases h : G.oracleAt (seatOf x).1 with
  | none =>
    constructor
    · intro _ o ho
      cases ho
    · intro _
      rfl
  | some o =>
    constructor
    · intro hb o' ho'
      obtain rfl := Option.some.inj ho'
      exact (fitsB_iff cs st _ _).1 hb
    · intro hp
      exact (fitsB_iff cs st _ _).2 (hp o rfl)

/-- Clause 6, "no deeper column", as a test. -/
def noDeeperB (Fr : Frame) (x : Mem) : Bool :=
  match G.oracleAt (seatOf x).1 with
  | some o => Fr.all.all fun e => decide (e.no = (seatOf x).1 → e.a ≤ o.logLength)
  | none => true

theorem noDeeperB_iff (Fr : Frame) (x : Mem) :
    noDeeperB G Fr x = true ↔
      ∀ o, G.oracleAt (seatOf x).1 = some o →
        ∀ e ∈ Fr.all, e.no = (seatOf x).1 → e.a ≤ o.logLength := by
  unfold noDeeperB
  cases h : G.oracleAt (seatOf x).1 with
  | none =>
    constructor
    · intro _ o ho
      cases ho
    · intro _
      rfl
  | some o =>
    constructor
    · intro hb o' ho' e he
      obtain rfl := Option.some.inj ho'
      exact of_decide_eq_true (List.all_eq_true.1 hb e he)
    · intro hp
      exact List.all_eq_true.2 fun e he => decide_eq_true (hp o rfl e he)

/-- The five clauses beside SeatFits, as one test. -/
def planAt5B (cs : Codes) (Fr : Frame) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage) (x : Mem) :
    Bool :=
  tieB cs (x.1.l.get x.2).1 && radB cs r st x && toldB G x && fitsAtB G cs st x &&
    noDeeperB G Fr x

/-- **Under clause 3 the test's yes is PlanAt, both ways.** -/
theorem planAt_iff (cs : Codes) (Fr : Frame) (r : Fmt.M1.Stage → ℕ) (st : Fmt.M1.Stage) (x : Mem)
    (hF : SeatFits G cs x.1.l x.1.seat) :
    planAt5B G cs Fr r st x = true ↔ PlanAt cs G Fr r st x := by
  unfold planAt5B PlanAt
  simp only [Bool.and_eq_true]
  rw [tie_iff, radB_iff, toldB_iff, fitsAtB_iff, noDeeperB_iff]
  exact ⟨fun h => ⟨h.1.1.1.1, h.1.1.1.2, hF, h.1.1.2, h.1.2, h.2⟩,
    fun h => ⟨⟨⟨⟨h.1, h.2.1⟩, h.2.2.2.1⟩, h.2.2.2.2.1⟩, h.2.2.2.2.2⟩⟩

/-- The field's test: at every one of mine, at the first of the stages. -/
def planAtAllB (cs : Codes) (Fr : Frame) (r : Fmt.M1.Stage → ℕ) (stages : List Fmt.M1.Stage)
    (mine : List Mem) : Bool :=
  match stages with
  | st :: _ => mine.all fun x => planAt5B G cs Fr r st x
  | [] => true

/-- **THE FIELD planAt, IN ITS OWN TEXT, FROM THE TEST AND CLAUSE 3 AT EVERY ONE OF MINE.** -/
theorem planAtAll_law (cs : Codes) (Fr : Frame) (r : Fmt.M1.Stage → ℕ)
    (stages : List Fmt.M1.Stage) (mine : List Mem)
    (hF : ∀ x ∈ mine, SeatFits G cs x.1.l x.1.seat)
    (h : planAtAllB G cs Fr r stages mine = true) :
    ∀ x ∈ mine, ∀ st rest, stages = st :: rest → PlanAt cs G Fr r st x := by
  intro x hx st rest e
  subst e
  exact (planAt_iff G cs Fr r st x (hF x hx)).1 (List.all_eq_true.1 h x hx)

end P2Law.PlanLeft

#print axioms P2Law.PlanLeft.aOf_eq_B
#print axioms P2Law.PlanLeft.radB_iff
#print axioms P2Law.PlanLeft.toldB_iff
#print axioms P2Law.PlanLeft.told_of_seatFits
#print axioms P2Law.PlanLeft.fitsAtB_iff
#print axioms P2Law.PlanLeft.noDeeperB_iff
#print axioms P2Law.PlanLeft.planAt_iff
#print axioms P2Law.PlanLeft.planAtAll_law
