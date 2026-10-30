-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/EqAllToy.lean: THE SMALLNESS TEST: THE PREMISES OF `eqAll_returns`
(Johnson/Desc/K8/Honest/EqAllReturns.lean) AS TESTS WITH CODE, THEOREMS THAT THEIR YES GIVES THEM,
AND `#guard` LINES AT THE LIBRARY's SMALL EXAMPLE (OnBytes/Model/TestTailRun.lean), IN FRONT OF THE
LIST. Lemmas and tests; none of the library's goals.

  `allReadyB front tl funs F cs`   the eight premises on numbers, flags, marks and lengths
  `allReady_of_B`     a yes gives `AllReady`
  `liveColsB`, `liveCols_of_B`   the third test on values
  `tailReady_size`    of the claims in front the seventeen read the number alone
What the lines show. 1 At the example the eight hold, the three tests on values hold, and the list
itself returns: the law is not empty. 2 With one thing spoiled among numbers, flags and marks the
test says no AND the list refuses, under the name of the guard that is meant: the list of tables
open; nothing heard; a row of the lookup's lacking; the padding's places; an index's point too
short; the sumcheck's row made already; one of its slots filled; another number of tables; the
sumcheck not started; no challenge for its variable; no variable; a ledger without a slot. 3 With
one VALUE spoiled the eight still hold, that test on values fails and the list refuses under its
guard's name: a table's weight moved; a coefficient on the test's own slots; a column of the drawn
matrix laid to 0.
Limits. One example. The padding key (`key`) is not spoiled, nor the clause that each of the
sumcheck's variables has a degree of at least 1. Nor is the clause that the ledger's lists on the
slots have their size: no guard of the list asks it of the shown values and the factors, and at a
shorter list the text would write beyond its end, which a compiled run reports aloud: so no line
runs it there. THE TEST GOES ONE WAY: a yes gives the premises; a no is not shown to deny them. The
list of tables open also breaks the first test on values; another number of tables also breaks that
test and, among the seventeen, `table` and `tile1`; a ledger without a slot breaks two of the
sumcheck's clauses at once. At "no variable" two fields are turned for one clause, so that the
clause on the sizes holds and that one alone fails. The names "internal-f-exist", "pscRow:198" and
"internal-f-table-read" are shared by several tests. What the seventeen's own lines show and do not
show: Johnson/Desc/K8/Honest/EqTailToy.lean.
Nothing is claimed on completeness, soundness or hiding.

-/
import Johnson.Desc.K8.Honest.EqAllReturns
import Johnson.Desc.K8.Honest.EqTailToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims
open VerifiableInference.Desc.First.TailClaims.Law (St idxOk)
open VerifiableInference.Desc.First.Shape
open VerifiableInference.Desc.First.Look (laidDigits padKeyDigits)
open OnBytes.Tie.Pv.Tail.Port (readsList)

/-- Of the claims in front the seventeen read the number alone. -/
theorem tailReady_size {before front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs cs' : Array Claim} {rd : Array (Array Bool)} {s1 s3 : Nat} (e : cs'.size = cs.size)
    (h : TailReady before front tl funs F cs rd s1 s3) :
    TailReady before front tl funs F cs' rd s1 s3 :=
  ⟨by rw [e]; exact h.four, h.drawn, h.plan, h.one, h.fresh, h.fits, h.table, h.reads, h.marks,
    h.allSet, h.inList, h.tile1, h.tile3, h.kinds, h.sum, h.count, h.apart⟩

/-- The eight premises on numbers, flags, marks and lengths. -/
def allReadyB (front : Nat) (tl : HTailF2) (funs : Array HFun) (F : Fork) (cs : Array Claim) :
    Bool :=
  match tl.heard with
  | none => false
  | some g =>
    tl.funClosed && funs.size == tl.funs.size && g.rows.size == lookRows tl && padKeyDigits tl &&
      ([0, 1].all fun q => (tl.zOf q).pieces.toList.all fun p => idxOk tl g q p) &&
      laidDigits tl == some g.shape.pub && openB (pscSh g.leaves) (ledSh F) &&
      tailReadyB (front + cs.size) front tl funs F (cs ++ Array.replicate 4 {})

/-- A yes gives the eight premises. -/
theorem allReady_of_B {front : Nat} {tl : HTailF2} {funs : Array HFun} {F : Fork}
    {cs : Array Claim} (h : allReadyB front tl funs F cs = true) :
    ∃ g rd s1 s3, AllReady front tl funs F cs g rd s1 s3 := by
  unfold allReadyB at h
  cases hg : tl.heard with
  | none => rw [hg] at h; cases h
  | some g =>
    rw [hg] at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩ := h
    obtain ⟨rd, s1, s3, hT⟩ := tailReady_of_B a8
    refine ⟨g, rd, s1, s3, ⟨a1, beq_iff_eq.1 a2⟩, hg, beq_iff_eq.1 a3, a4, fun q hq p hp => ?_,
      beq_iff_eq.1 a6, open_of_B a7, fun c4 e => tailReady_size (by simp [e]) hT⟩
    exact List.all_eq_true.1 (List.all_eq_true.1 a5 q hq) p hp

/-- At chi no column of a matrix on which a read lies has the weight 0. -/
def liveColsB (tl : HTailF2) (funs : Array HFun) (chi : E) : Bool :=
  (readsList tl funs).all fun x =>
    (List.range (tl.mats.getD x.1.mat {}).k).all fun c =>
      !isZeroE (foldColumn tl.cfF ((tl.cfFirst.getD x.1.mat 0 + c) * tl.tau) tl.tau
        (powers chi tl.tau))

theorem liveCols_of_B {tl : HTailF2} {funs : Array HFun} {chi : E}
    (h : liveColsB tl funs chi = true) : LiveCols tl funs chi := by
  intro x hx c hc
  have := List.all_eq_true.1 (List.all_eq_true.1 h x hx) c (List.mem_range.2 hc)
  simpa using this

namespace AllToy
open TailToy (funs start)

/-- What the test with code says at the example in front of the list. -/
def ready (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) (fs : Array HFun := funs) :
    Option Bool :=
  (start turnT turnF).map fun y => allReadyB (lookRows y.1) y.1 fs y.2 #[]

/-- What the list itself says there: none: it returns; some: the name under which it refuses. -/
def refusal (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) (fs : Array HFun := funs) :
    Option (Option String) :=
  (start turnT turnF).map fun y =>
    match eqAll y.1 fs (lookRows y.1) (y.2, #[]) with
    | .ok _ => none
    | .error e => some e

/-- The three tests on values there. -/
def values (turnT : HTailF2 → HTailF2) (turnF : Fork → Fork) (fs : Array HFun := funs) :
    Option (Bool × Bool × Bool) :=
  (start turnT turnF).map fun y =>
    (y.1.funsHeld fs, (y.2.LS.extract y.1.slotA y.1.slotB).all isZeroE,
      liveColsB y.1 fs y.2.theta)

/-- What the lookup heard, turned. -/
def heardBy (f : Forest.Heard → Forest.Heard) (t : HTailF2) : HTailF2 :=
  { t with heard := t.heard.map f }

-- 1 the member
#guard (start id id).isSome
#guard ready id id == some true
#guard values id id == some (true, true, true)
#guard refusal id id == some none
-- 2 one number, flag or mark spoiled: the test says no; the list refuses under the guard's name
#guard ready (fun t => { t with funClosed := false }) id == some false &&
  refusal (fun t => { t with funClosed := false }) id == some (some "internal-f-fun-closed")
#guard ready (fun t => { t with heard := none }) id == some false &&
  refusal (fun t => { t with heard := none }) id == some (some "objectsF:1048")
#guard ready (heardBy fun g => { g with rows := g.rows.pop }) id == some false &&
  refusal (heardBy fun g => { g with rows := g.rows.pop }) id == some (some "internal-f-exist")
#guard ready (heardBy fun g => { g with shape := { g.shape with pub := g.shape.pub.push 1 } }) id ==
    some false &&
  refusal (heardBy fun g => { g with shape := { g.shape with pub := g.shape.pub.push 1 } }) id ==
    some (some "internal-forest-padding-places")
#guard ready (heardBy fun g => { g with zk := #[#[], #[]] }) id == some false &&
  refusal (heardBy fun g => { g with zk := #[#[], #[]] }) id == some (some "internal-eq-index")
#guard ready (heardBy fun g => { g with leaves := { g.leaves with rowMade := true } }) id ==
    some false &&
  refusal (heardBy fun g => { g with leaves := { g.leaves with rowMade := true } }) id ==
    some (some "pscRow:198")
#guard ready id (fun F => { F with gotF := F.gotF.set! 0 true }) == some false &&
  refusal id (fun F => { F with gotF := F.gotF.set! 0 true }) == some (some "pscRow:199")
#guard ready id id (funs.push {}) == some false &&
  refusal id id (funs.push {}) == some (some "internal-f-fun-closed")
#guard ready (heardBy fun g => { g with leaves := { g.leaves with started := false } }) id ==
    some false &&
  refusal (heardBy fun g => { g with leaves := { g.leaves with started := false } }) id ==
    some (some "pscRow:198")
#guard ready (heardBy fun g => { g with leaves := { g.leaves with r := #[] } }) id == some false &&
  refusal (heardBy fun g => { g with leaves := { g.leaves with r := #[] } }) id ==
    some (some "pscRow:198")
#guard ready (heardBy fun g => { g with leaves := { g.leaves with vars := #[], r := #[] } }) id ==
    some false &&
  refusal (heardBy fun g => { g with leaves := { g.leaves with vars := #[], r := #[] } }) id ==
    some (some "pscRow:198")
#guard ready id (fun F => { F with ns := 0 }) == some false &&
  refusal id (fun F => { F with ns := 0 }) == some (some "pscRow:199")
-- 3 one value spoiled: the eight hold; that test on values fails; the list refuses under its name
#guard ready id id (funs.map fun f => { f with phi := f.phi.set! 0 zeroE }) == some true &&
  values id id (funs.map fun f => { f with phi := f.phi.set! 0 zeroE }) ==
    some (false, true, true) &&
  refusal id id (funs.map fun f => { f with phi := f.phi.set! 0 zeroE }) ==
    some (some "internal-f-fun-moved")
#guard ready id (fun F => { F with LS := F.LS.set! 0 oneE }) == some true &&
  values id (fun F => { F with LS := F.LS.set! 0 oneE }) == some (true, false, true) &&
  refusal id (fun F => { F with LS := F.LS.set! 0 oneE }) == some (some "internal-f-tail-slot")
#guard ready (fun t => { t with cfF := t.cfF.mapIdx fun i x => if i < 160 then 0 else x }) id ==
    some true &&
  values (fun t => { t with cfF := t.cfF.mapIdx fun i x => if i < 160 then 0 else x }) id ==
    some (true, true, false) &&
  refusal (fun t => { t with cfF := t.cfF.mapIdx fun i x => if i < 160 then 0 else x }) id ==
    some (some "internal-f-table-read")

end AllToy

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.tailReady_size
#print axioms VerifiableInference.Desc.First.K8.Honest.allReady_of_B
#print axioms VerifiableInference.Desc.First.K8.Honest.liveCols_of_B
