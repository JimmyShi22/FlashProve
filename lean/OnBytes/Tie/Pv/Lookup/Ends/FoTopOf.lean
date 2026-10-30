-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoTopOf.lean.
The number of indices of the smallness test's equations, as the statements on its ties and reads
count it (topOf), is the number that the plan adds to its claims (equationsF), under two premises.

The statements on the ties and reads (OnBytes/Tie/Pv/Tail/EndSpread.lean) bound every exponent by
the plan's number of claims plus topOf tl funs. The planner is told the plan's number of claims plus
HTailF2.equationsF at the number of reads. This file says that the two numbers are one.

Main names:
  `foldl_add_sum`, `arrayFoldl_add_sum`: a fold that adds up f over a list or an array is the sum
    of f over the indices.
  `equationsF_sum`: equationsF written as a sum over the matrices' numbers.
  `topOf_eq`: topOf tl funs = tl.equationsF (readsList tl funs).length.
  `topOf_powered`: the same where the second premise comes from Port.Powered, which says what
    HTailF2.powersF has set and tested.
  `objectsF_laid`: behind a run of objectsF that returns tl': if tl'.equationsLaidF = some n (the
    number that the sub-proofs hand to doorH), then n = topOf tl' funs, and, if
    tl'.NM = tl'.mats.size, n = tl'.equationsF (readsList tl' funs).length. ρ and W are the letters
    of Port.objectsF_total; the statement does not read them.
Under (topOf_eq): tl.NM = tl.mats.size; each matrix's shape has (m + 2) / 3 rows of symbols.
Needs: OnBytes/Tie/Pv/Tail/EndSpread.lean and what it imports.
Does not say: that the number of reads that a run lays, (readsList tl' funs).length, is the number
of reads in the plan; that tl.NM = tl.mats.size at a run's record; that a run's record has the
matrices and the tau of the record from which the plan is made.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Tail.EndSpread

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Tie.Pv.Tail.Port

theorem foldl_add_sum {α : Type} (f : α → ℕ) (d : α) : ∀ (l : List α) (z : ℕ),
    l.foldl (fun n a => n + f a) z = z + ∑ i ∈ Finset.range l.length, f (l.getD i d)
  | [], z => by simp
  | a :: l, z => by
    rw [List.foldl_cons, foldl_add_sum f d l, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    omega

theorem arrayFoldl_add_sum {α : Type} (f : α → ℕ) (d : α) (l : Array α) :
    l.foldl (fun n a => n + f a) 0 = ∑ i ∈ Finset.range l.size, f (l.getD i d) := by
  rw [← Array.foldl_toList, foldl_add_sum f d, Nat.zero_add, Array.length_toList]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD]

theorem equationsF_sum (tl : HTailF2) (n : ℕ) :
    tl.equationsF n = (∑ nu ∈ Finset.range tl.mats.size,
      tl.stepF * 2 ^ clog2 (((tl.mats.getD nu {}).m + 2) / 3)) + n * tl.stepF := by
  unfold HTailF2.equationsF
  rw [arrayFoldl_add_sum (fun M : TMat => tl.stepF * 2 ^ clog2 ((M.m + 2) / 3)) {}]

theorem topOf_eq (tl : HTailF2) (funs : Array HFun) (hN : tl.NM = tl.mats.size)
    (hS : ∀ mu < tl.NM, (tl.shp.getD mu {}).mS = ((tl.mats.getD mu {}).m + 2) / 3) :
    topOf tl funs = tl.equationsF (readsList tl funs).length := by
  rw [equationsF_sum, ← hN]
  unfold topOf firstOf
  congr 1
  exact Finset.sum_congr rfl fun nu h => by rw [hS nu (Finset.mem_range.mp h)]

/-- With what powersF has set and tested. -/
theorem topOf_powered {tl : HTailF2} {theta : E} (hP : Powered tl theta) (funs : Array HFun)
    (hN : tl.NM = tl.mats.size) : topOf tl funs = tl.equationsF (readsList tl funs).length :=
  topOf_eq tl funs hN fun mu hmu => (hP.shape mu hmu).2.2.2.2

section
variable {K : Type} [CommRing K] (ρ : Reading K) (W : World K)
include ρ W

/-- Behind objectsF: the number that the run hands to doorH. -/
theorem objectsF_laid (tl tl' : HTailF2) (funs : Array HFun) (F G : Fork) (c c' : Ctx)
    (h : tl.objectsF funs F c = .ok ((tl', G), c')) (n : ℕ) (hn : tl'.equationsLaidF = some n) :
    n = topOf tl' funs ∧
      (tl'.NM = tl'.mats.size → n = tl'.equationsF (readsList tl' funs).length) := by
  obtain ⟨g, Fa, ca, tla, Fb, cb, tlb, Fc, cc, tl1, F1, c1, -, -, -, -, hWt, hlaid, etl, -, -, -⟩ :=
    objectsF_total ρ W tl tl' funs F G c c' h
  obtain ⟨-, -, hP1, -⟩ := weightsF_spec tlb tl1 Fc F1 cc c1 hWt
  have hP : Powered tl' Fc.theta := by
    rw [etl]
    exact ⟨hP1.vp, hP1.vt, hP1.rowX, hP1.loX, hP1.eqFirst, hP1.shape⟩
  have eL : readsList tl1 funs = readsList tl' funs :=
    ((congrArg (fun t => readsList t funs) etl).trans rfl).symm
  have e : n = topOf tl' funs := by
    unfold HTailF2.equationsLaidF at hn
    split at hn
    · cases hn
    · rw [← Option.some.inj hn, hP.eqFirst_val tl'.NM hP.NM_le_shp, hlaid, eL]
      rfl
  exact ⟨e, fun hN => e.trans (topOf_powered hP funs hN)⟩

end
end Fo
