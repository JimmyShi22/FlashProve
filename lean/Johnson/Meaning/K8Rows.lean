-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/K8Rows.lean: what a yes of the batching kind's door
(Johnson/Desc/First/Batch/Text.lean: door) says of the numbers of a segment's equations: all the
plan's claims have been added, and the rows that were owed since the draw are the plan's number of
claims and the indices that the smallness test's equations take. With what the list "K8.equations"
leaves in the tail's record: the number of reads that were laid is the plan's.

Why. The exponents of a segment's equations are to differ and to be at most d. With pc the plan's
number of claims and d + 1 the rows of the batching element's round, the exponents of the smallness
test's single equations lie from pc to pc + topOf tl funs − 1 (EquationsForms.lean: K08Claims). The
planner is told rows = pc + equationsF n, n the plan's number of reads
(OnBytes/Tie/Pv/Lookup/Ends/BatRows.lean). That the reads which a run lays are n in number is said
by no earlier library file (FoTopOf.lean's head). Here it follows from two tests of the door.

  door_counts       where door owed laid L F d returns: laid = some n, F.planClaimsF ≠ 0,
                    F.nClaim = F.planClaimsF, and owed = some (F.planClaimsF + n).
  eq_laid           where equations front tl funs F returns tl': if laidOf tl' = some n (the number
                    that the lens at the carried record hands the door: Batch/AtS.lean), then
                    n = topOf tl' funs; and, if tl'.NM = tl'.mats.size,
                    n = tl'.equationsF (readsList tl' funs).length. After Fo.objectsF_laid
                    (FoTopOf.lean), of the list's own text. ρ and W are the letters of
                    eqTail_total; the statement does not read them.
  K08Rows (a closed Prop) · k08_rows   both together: where the list was made and left tl', and the
                    door returns at owed = some rows and laid = laidOf tl': all F.planClaimsF claims
                    are added, and rows = F.planClaimsF + topOf tl' funs. If besides
                    rows = F.planClaimsF + tl'.equationsF n and tl'.NM = tl'.mats.size:
                    (readsList tl' funs).length = n.

What is not claimed. That the record tl' which the list left is the record at the door; that the
rows owed at the door are the rows of the plan's entry (the draw lays them: Batch/Kind.lean: drawn;
who keeps them in between is not said); that F.planClaimsF is the plan's nLin. One direction, from a
yes. THE YES LIES BEHIND THE DRAW of the batching element; the numbers that it ties (the matrices,
tau, the closed list of tables, the plan's n) are fixed before it: that is not stated here. Nothing
on soundness.
-/
import Johnson.Desc.First.TailClaims.EquationsCover
import Johnson.Desc.First.Batch.AtS
import OnBytes.Tie.Pv.Lookup.Ends.FoTopOf
import OnBytes.Tie.Pv.Lookup.Ends.FoTailCore

set_option autoImplicit false

namespace Meaning.K8

open OnBytes OnBytes.Model OnBytes.Model.HTailF2 VerifiableInference.Desc
open VerifiableInference.Desc.First.TailClaims VerifiableInference.Desc.First.TailClaims.Law
open OnBytes.Tie.Pv.Tail.Port (topOf readsList Powered)

theorem bindA {α β : Type} {x : K9.Ans α} {f : α → K9.Ans β} {b : β} (h : (x >>= f) = .ok b) :
    ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

theorem need_ok {n : String} {b : Bool} {u : Unit} (h : K9.need n b = .ok u) : b = true := by
  unfold K9.need at h
  split at h
  · assumption
  · cases h

theorem there_ok {α : Type} {n : String} {o : Option α} {a : α} (h : K9.there n o = .ok a) :
    o = some a := by
  cases o with
  | none => cases h
  | some x => exact congrArg some (Except.ok.inj h)

/-- What the one equation's text has tested and keeps: all the plan's claims are added. -/
theorem equation_counts {L : LinkCtx} {F : Fork} {x : K9.Equation × Fork}
    (h : K9.equation L F = .ok x) :
    F.planClaimsF ≠ 0 ∧ F.nClaim = F.planClaimsF ∧ x.2.nClaim = F.nClaim := by
  unfold K9.equation at h
  obtain ⟨_, _, h⟩ := bindA h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, h3, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain ⟨_, _, h⟩ := bindA h
  obtain rfl := Except.ok.inj h
  have t := need_ok h3
  simp only [Bool.and_eq_true, bne_iff_ne, beq_iff_eq] at t
  exact ⟨t.1, t.2, rfl⟩

/-- **What a yes of the door says of the numbers.** -/
theorem door_counts {X : Type} {owed : K9.RowsOwed} {laid : Option ℕ} {L : LinkCtx} {F : Fork}
    {d : K9.St X} {o : K9.Out X} (h : K9.door owed laid L F d = .ok o) :
    ∃ n, laid = some n ∧ F.planClaimsF ≠ 0 ∧ F.nClaim = F.planClaimsF ∧
      owed = some (F.planClaimsF + n) := by
  unfold K9.door at h
  obtain ⟨n, h1, h⟩ := bindA h
  obtain ⟨x, h2, h⟩ := bindA h
  obtain ⟨_, h3, _⟩ := bindA h
  obtain ⟨a, b, c⟩ := equation_counts h2
  have t := need_ok h3
  rw [beq_iff_eq, c, b] at t
  exact ⟨n, there_ok h1, a, b, t⟩

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)
include ρ W

/-- **The number that the list leaves for the door.** -/
theorem eq_laid {front : ℕ} {tl tl' : HTailF2} {funs : Array HFun} {F F1 : Fork}
    {cls : List Claim} (h : equations front tl funs F = .ok (tl', F1, cls)) {n : ℕ}
    (hn : K9.laidOf tl' = some n) :
    n = topOf tl' funs ∧
      (tl'.NM = tl'.mats.size → n = tl'.equationsF (readsList tl' funs).length) := by
  obtain ⟨before, tla, tlb, s1, s2, arr, -, -, h3, -⟩ := eq_parts h
  obtain ⟨tl1, hW, -, hlaid, etl, -, -⟩ := eqTail_total ρ W F before tlb tl' funs front s2 _ h3
  obtain ⟨hP1, -, -⟩ := eqWeights_spec tlb tl1 front s2 s2 hW
  have hP : Powered tl' s2.1.theta := by
    rw [etl]
    exact ⟨hP1.vp, hP1.vt, hP1.rowX, hP1.loX, hP1.eqFirst, hP1.shape⟩
  have eL : readsList tl1 funs = readsList tl' funs :=
    ((congrArg (fun t => readsList t funs) etl).trans rfl).symm
  have e : n = topOf tl' funs := by
    unfold K9.laidOf at hn
    split at hn
    · cases hn
    · rw [← Option.some.inj hn, hP.eqFirst_val tl'.NM hP.NM_le_shp, hlaid, eL]
      rfl
  exact ⟨e, fun hN => e.trans (Fo.topOf_powered hP funs hN)⟩

end

/-- **The list and the door together.** -/
def K08Rows : Prop :=
  ∀ (K : Type) [CommRing K] (_ : Reading K) (_ : World K) (X : Type) (front rows : ℕ)
    (tl tl' : HTailF2) (funs : Array HFun) (F0 F1 F : Fork) (cls : List Claim) (L : LinkCtx)
    (d : K9.St X) (o : K9.Out X),
    equations front tl funs F0 = .ok (tl', F1, cls) →
    K9.door (some rows) (K9.laidOf tl') L F d = .ok o →
    F.planClaimsF ≠ 0 ∧ F.nClaim = F.planClaimsF ∧ rows = F.planClaimsF + topOf tl' funs ∧
      ∀ n, rows = F.planClaimsF + tl'.equationsF n → tl'.NM = tl'.mats.size →
        (readsList tl' funs).length = n

theorem k08_rows : K08Rows := by
  intro K _ ρ W X front rows tl tl' funs F0 F1 F cls L d o h hd
  obtain ⟨m, hm, a, b, c⟩ := door_counts hd
  obtain ⟨e1, e2⟩ := eq_laid ρ W h hm
  have hr : rows = F.planClaimsF + m := Option.some.inj c
  refine ⟨a, b, by rw [hr, e1], fun n hn hN => ?_⟩
  have : tl'.equationsF (readsList tl' funs).length = tl'.equationsF n := by
    have := e2 hN
    omega
  exact Fo.equationsF_inj tl' this

end Meaning.K8

#print axioms Meaning.K8.door_counts
#print axioms Meaning.K8.eq_laid
#print axioms Meaning.K8.k08_rows
