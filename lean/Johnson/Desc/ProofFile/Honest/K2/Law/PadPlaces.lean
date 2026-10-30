-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/PadPlaces.lean: THREE TEXTS FOR THE PAD's PLACES IN A MAIN ROW,
HELD AGAINST EACH OTHER: the list `padInMain` (Honest/RowData.lean): the fence of
Honest/K2/Law/MainTxt.lean; the places "last main row, ell - T.pad + i, i below T.pad", T :=
`K1.stepsOf` (Honest/K1/Coins.lean): those of Honest/K2/Law/PadTxt.lean; the library's test `padB`
(Johnson/Desc/SeatAt.lean), by which a witness's table and the lots' texts for pads are split. On a
shape and codes alone: public. Statements with their proofs; no definition.

  `stepsPad_plain`, `stepsPad_zero`   T.pad at a shape without a mask row; with one
  `mem_padInMain_iff`   (r, j) is a member of `padInMain` just where it is such a place: AT ANY
                        COUNT OF ANSWERS
  `padB_main_iff`       `padB` says yes at a main row's (r, j), j below ell, just where it is such a
                        place: AT ONE ANSWER
  `padInMain_iff_padB`  so, at one answer and j below ell, the list and the test are one

SO THE TWO FILES' FENCES ON (r, j) ARE COMPLEMENTS, at one shape with a main row and one ell: by
`mem_padInMain_iff` (r, j) is off `padInMain` or it is such a place, and not both. EACH FILE's OTHER
PREMISES STAND BESIDE ITS FENCE: whether a law of either file speaks at an entry hangs on these too.

Kin. `no_pad` (Honest/K1/DataLaw.lean, of other authors): off `padInMain` the shared sending's four
tests for a pad's place do not all hold: one way of `mem_padInMain_iff`, in another form. `pad_has`
(Honest/Law/LaidLaw.lean) and `padInMain_pad` (Honest/Law/LaysRoom.lean), of other authors, and the
library's `padB_of_pad`, `pad_of_padB` (Johnson/Goal/Meaning/LaidInside.lean) tie the list and the
test, each, to the main places of the programs' pad (`OnBytes.Send.pad`) by their index: a road over
a third text, not taken here. `pad_count` and `pad_facts_main` (Johnson/SendSim/At/PadAt.lean, of
other authors; a file that is not in this library): the first is `stepsPad_plain`'s count, written
through `K1.Msg.e`, at a plan's message with an answer; the second tells at which row and place the
shared sending's rows hold the pad's coins.

Limits. The shape has a main row (a premise). `padB` is written for one answer (its own docstring):
at another count of answers nothing is said of it here. `padB` has no bound above on the place: at j
from ell on it may say yes: outside these laws. Of the pad's place in a mask row nothing is said. No
coin, no data, no text of a lot. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K1.Coins
import Johnson.Desc.ProofFile.Honest.RowData
import Johnson.Desc.SeatAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (padB)

variable (codes : OnBytes.Codes) (s : OnBytes.OracleShape) (R : Option K1.Ride)

/-- T.pad at a shape without a mask row. -/
theorem stepsPad_plain (hz : s.maskRows = 0) :
    (K1.stepsOf codes s R).pad = (if s.mainDeg == 3 then 1 else 3) * s.answers := by
  show (if s.maskRows == 0 && s.answers != 0 then (if s.mainDeg == 3 then 1 else 3) * s.answers
    else 0) = _
  by_cases ha : s.answers = 0
  · simp [ha]
  · simp [hz, ha]

/-- With one. -/
theorem stepsPad_zero (hz : s.maskRows ≠ 0) : (K1.stepsOf codes s R).pad = 0 := by
  show (if s.maskRows == 0 && s.answers != 0 then (if s.mainDeg == 3 then 1 else 3) * s.answers
    else 0) = 0
  simp [hz]

/-- **THE LIST AND THE PLACES**, at any count of answers. -/
theorem mem_padInMain_iff (ell : Nat) (hm : 0 < s.mainRows) (r j : Nat) :
    (r, j) ∈ padInMain ell s ↔
      ∃ i, i < (K1.stepsOf codes s R).pad ∧ r = s.mainRows - 1 ∧
        j = ell - (K1.stepsOf codes s R).pad + i := by
  unfold padInMain
  by_cases hz : s.maskRows = 0
  · rw [stepsPad_plain codes s R hz]
    have h1 : ¬ ((s.maskRows != 0 || s.mainRows == 0) = true) := by
      simp [hz]
      omega
    rw [if_neg h1]
    simp only [List.mem_map, List.mem_range, Prod.mk.injEq]
    constructor
    · rintro ⟨i, hi, e1, e2⟩
      exact ⟨i, hi, e1.symm, e2.symm⟩
    · rintro ⟨i, hi, e1, e2⟩
      exact ⟨i, hi, e1.symm, e2.symm⟩
  · rw [stepsPad_zero codes s R hz, if_pos (by simp [hz])]
    simp

/-- **THE TEST AND THE PLACES**, at one answer. -/
theorem padB_main_iff (ha : s.answers = 1) (hm : 0 < s.mainRows)
    (hp : (K1.stepsOf codes s R).pad ≤ (codes.base.getD s.code default).ell) (r j : Nat)
    (hj : j < (codes.base.getD s.code default).ell) :
    padB codes s false r j = true ↔
      ∃ i, i < (K1.stepsOf codes s R).pad ∧ r = s.mainRows - 1 ∧
        j = (codes.base.getD s.code default).ell - (K1.stepsOf codes s R).pad + i := by
  unfold padB
  by_cases hz : s.maskRows = 0
  · rw [stepsPad_plain codes s R hz, ha, Nat.mul_one] at hp ⊢
    have hc : (if s.mainDeg == 3 then 1 else 3) = (if s.mainDeg = 3 then 1 else 3 : Nat) := by
      by_cases h3 : s.mainDeg = 3 <;> simp [h3]
    rw [hc] at hp ⊢
    generalize (if s.mainDeg = 3 then 1 else 3 : Nat) = c at hp ⊢
    simp only [Bool.false_eq_true, if_false, hz, beq_self_eq_true, Bool.true_and,
      Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq]
    constructor
    · rintro ⟨e1, e2⟩
      exact ⟨j - ((codes.base.getD s.code default).ell - c), by omega, by omega, by omega⟩
    · rintro ⟨i, hi, e1, e2⟩
      exact ⟨by omega, by omega⟩
  · rw [stepsPad_zero codes s R hz]
    simp [hz]

/-- So the list and the test are one, at one answer and j below ell. -/
theorem padInMain_iff_padB (ha : s.answers = 1) (hm : 0 < s.mainRows)
    (hp : (K1.stepsOf codes s R).pad ≤ (codes.base.getD s.code default).ell) (r j : Nat)
    (hj : j < (codes.base.getD s.code default).ell) :
    (r, j) ∈ padInMain (codes.base.getD s.code default).ell s ↔ padB codes s false r j = true :=
  (mem_padInMain_iff codes s R _ hm r j).trans (padB_main_iff codes s R ha hm hp r j hj).symm

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.stepsPad_plain
#print axioms ProofFile.Honest.K2.Law.stepsPad_zero
#print axioms ProofFile.Honest.K2.Law.mem_padInMain_iff
#print axioms ProofFile.Honest.K2.Law.padB_main_iff
#print axioms ProofFile.Honest.K2.Law.padInMain_iff_padB
