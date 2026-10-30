-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4PinsIndex.lean: THE GUARD OF THE VALUE's READING OF THE INDEX MASKS. `PinPlan.idx`
(Johnson/Road/K4/K4PinsRead.lean) reads entry j of the index-mask message as the table at the seat
`N.index`, at the place posI j. WHERE NO MEMBER OF ms SITS AT THAT SEAT IT READS THE ZERO TABLE, AND
WHERE posI j LIES OUTSIDE THE MEMBER's RANGES A CUT 0, IN SILENCE; and nothing in `AllFit`,
`K4PlanFit` or `SitsIn` asks otherwise (by reading). Here: the condition that
shuts both, a test with code, and the theorem that spends it. THE TEST STANDS IN NO
`noncomputable section`.

  `IndexFit cs posI ms N n`: A CONDITION ON PUBLIC LETTERS: a member of ms sits at `N.index`, and at
    every j < n the place posI j lies inside that member's ranges.
  `indexFitB`, `indexFit_of_B`: the test; a yes gives the condition.
  **`idx_of_fit`**: under `IndexFit`, at every j < n: `A.idx N (partOf … w) j` is the entry of the
    witness's own table of that member at posI j (the one accessor `memTab`): no silent 0.
  `indexFitB_no_member`: the test can fail: where ms is empty it says no.

OBJECT: none of its own. USER: Johnson/Road/K4/K4PinsIndexAt.lean; meant: WHOEVER PAYS THE LINES
forms AND wo OF `K4Lines` (Johnson/Road/K4/CloseAtTable.lean): of the nine lines these two alone can
spend the value's letter idxAt: it enters the value through its message alone, at the entries ix n,
n ≤ nx (Johnson/Road/K4/Value.lean, ValueMasks.lean: `msg_ix`; c7 is idxAt at v7): so n := nx + 1
covers what the value reads; the seven that
`k4_own_end` (Johnson/Road/K4/K4PinsEnd.lean) exchanges do not read it. LETTERS, filled by nobody:
cs, posI, ms, N, n (how many index masks the value reads).

Limits. K04_law IS NOT PROVED BY THIS. `IndexFit` IS A PREMISE; NOTHING IS EVALUATED HERE. THAT posI
j IS THE PLACE AT WHICH THE PROGRAMS LAY INDEX MASK j IS NOT ASKED: the condition shuts the silent
0, not a wrong place. n is a letter: that it covers every j that the value reads is not shown. One
direction.
-/
import Johnson.Road.K4.K4PinsRead

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4
open Johnson.Pack
open VerifiableInference.Desc (Wit)
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem MsgT InMsg memTab seatOf)

/-- **The condition**: a member sits at the index masks' seat, and the places read lie inside it. -/
def IndexFit (cs : OnBytes.Codes) (posI : ℕ → Bool × ℕ × ℕ) (ms : List Mem) (N : Numbers)
    (n : ℕ) : Prop :=
  ∃ u, memAt ms N.index = some u ∧
    ∀ j, j < n → InMsg cs (u.1.l.get u.2).1 (posI j).1 (posI j).2.1 (posI j).2.2

/-- The test. -/
def indexFitB (cs : OnBytes.Codes) (posI : ℕ → Bool × ℕ × ℕ) (ms : List Mem) (N : Numbers)
    (n : ℕ) : Bool :=
  match ms.find? fun y => decide (seatOf y = N.index) with
  | some u =>
    (List.range n).all fun j =>
      if (posI j).1 = true then
        decide ((posI j).2.1 < (u.1.l.get u.2).1.maskRows) &&
          decide ((posI j).2.2 < (pMask cs (u.1.l.get u.2).1).ell)
      else
        decide ((posI j).2.1 < (u.1.l.get u.2).1.mainRows) &&
          decide ((posI j).2.2 < (pMain cs (u.1.l.get u.2).1).ell)
  | none => false

theorem indexFit_of_B {cs : OnBytes.Codes} {posI : ℕ → Bool × ℕ × ℕ} {ms : List Mem}
    {N : Numbers} {n : ℕ} (h : indexFitB cs posI ms N n = true) : IndexFit cs posI ms N n := by
  unfold indexFitB at h
  cases hu : ms.find? fun y => decide (seatOf y = N.index) with
  | none =>
    rw [hu] at h
    exact absurd h Bool.false_ne_true
  | some u =>
    rw [hu] at h
    refine ⟨u, hu, fun j hj => ?_⟩
    have h0 := List.all_eq_true.1 h j (List.mem_range.2 hj)
    unfold InMsg
    by_cases hm : (posI j).1 = true
    · rw [if_pos hm] at h0 ⊢
      simpa using h0
    · rw [if_neg hm] at h0 ⊢
      simpa using h0

/-- **Under `IndexFit` an index mask is an entry of the witness's own table**: no silent 0. -/
theorem idx_of_fit {Cells Tok : Type} (A : PinPlan Cells) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
    (N : Numbers) (m n : ℕ) (cs : OnBytes.Codes) (h : IndexFit cs A.posI ms N n) :
    ∃ u, memAt ms N.index = some u ∧ ∀ (w : Wit Cells Tok MsgT) j, j < n →
      A.idx N (partOf cs arr ms N m w) j =
        memTab cs arr w u (A.posI j).1 (A.posI j).2.1 (A.posI j).2.2 := by
  obtain ⟨u, hu, hin⟩ := h
  exact ⟨u, hu, fun w j hj => A.idx_part arr ms N m cs hu w j (hin j hj)⟩

/-- **The test can fail**: no member, no yes. -/
theorem indexFitB_no_member (cs : OnBytes.Codes) (posI : ℕ → Bool × ℕ × ℕ) (N : Numbers)
    (n : ℕ) : indexFitB cs posI [] N n = false := rfl

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.indexFit_of_B
#print axioms OnBytes.Road.K4.idx_of_fit
#print axioms OnBytes.Road.K4.indexFitB_no_member
