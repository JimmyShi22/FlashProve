-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/MergeLaw/LedgerBehind.lean: what the merge's accepting step does to the open
segment's ledger of slots; so the table's two public tests on that ledger stay true across it, and
no slot below the next free number turns. Theorems with their proofs.

Why. The second tie owes the table's condition behind the merge. The merge WRITES the ledger, so the
rule that is general in the kind (KeepsAt.lean) carries no item that reads it: these are kept by
hand.

Main names:
  `merge_ledger`: where the ledger's three arrays have one entry a slot: the next free number moves
    by 2 lk + 3; the number of slots and the sizes stay; the mark "filled" turns at ONE slot alone:
    number next + 2 lk + 2, the last of that window (the slot of the value that the prover sends at
    the merge's end). Both states stand in the output head's part, opened. By `decide_inv`
    (Says.lean), `mergeHear_inv` (Hear.lean) and the library's `hideRun_fills`, `hideRun_keeps`
    (OnBytes/Tie/Pv/Psc/).
  `merge_trees`: the step leaves the ledger's list of arrays (the library's `hideRun_ok`: the ledger
    behind differs from the one in front at most in what lies under the slots).
  `merge_keeps_ledger`: `ledgerB` and `freeAboveB n` (Johnson/Desc/First/FillKeeper.lean) stay true
    across the merge.
  `merge_below_next`: no slot below the next free number turns: neither is a free one filled nor a
    filled one freed.

Limits. Nothing on what lies under the slots (that is `decide_later`, Keeps.lean). Nothing on
soundness.
-/
import Johnson.Top.H0.MergeLaw.Keeps
import Johnson.Desc.First.FillKeeper
import OnBytes.Tie.Pv.Psc.PscRoom

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.MergeLaw
open OnBytes OnBytes.Model
open OnBytes.PscRun (Sized Filled Later)
open VerifiableInference.Desc.First (S HeadOwn ledgerB freeAboveB)
open Johnson.Desc.First.ForkMerge (HeadMergeP headMergeDecide)

/-- **WHAT THE MERGE's ACCEPTING STEP DOES TO THE OPEN SEGMENT's LEDGER**, where its three arrays
have one entry a slot: the next free number moves by 2 lk + 3; the number of slots and the sizes
stay; and the mark "filled" turns at ONE slot alone, the last of that window. -/
theorem merge_ledger (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') :
    ∃ a a', s.here = .head a ∧ s'.here = .head a' ∧ a.opened = true ∧ a'.opened = true ∧
      (Sized a.F → a'.F.next = a.F.next + 2 * P.lay.lk + 3 ∧ a'.F.ns = a.F.ns ∧ Sized a'.F ∧
        ∀ j, j ≠ a.F.next + 2 * P.lay.lk + 2 → (Filled a'.F j ↔ Filled a.F j)) := by
  obtain ⟨a, a', tp, G, claim, x, wo, ha, ha', _, _, _, _, hm, hF, _⟩ := decide_inv h
  obtain ⟨_, _, _, _, _, v, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsF, hhide, _⟩ :=
    mergeHear_inv hm
  obtain ⟨a₁, a₁', e1, e1', e, ea, _⟩ := isLocal P s rs s' h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hop : a₁.opened = true := by
    by_contra hn
    simp [headMergeDecide, ha, hn, VerifiableInference.Desc.need, bind, Except.bind] at h
  refine ⟨a₁, a₁', ha, ha', hop, by rw [ea]; exact hop, fun hz => ?_⟩
  have hz1 : Sized ({ a₁.F with next := a₁.F.next + 1 + 2 * P.lay.lk + 2 } : Fork) := hz
  obtain ⟨hn, hw⟩ := OnBytes.PscRun.hideRun_fills hz1 hhide
  have hL := OnBytes.PscRun.hideRun_keeps hhide
  rw [hF]
  refine ⟨?_, hL.ns, hL.sized hz1, fun j hj => ?_⟩
  · show G.next = _
    rw [hn]
    show a₁.F.next + 1 + 2 * P.lay.lk + 2 = _
    omega
  · show Filled G j ↔ _
    refine hw j ?_
    rw [hsF]
    simp only [List.size_toArray, List.length_cons, List.length_nil]
    omega

/-- **The merge's accepting step leaves the ledger's list of arrays.** -/
theorem merge_trees (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') {a a' : HeadOwn} (ha : s.here = .head a)
    (ha' : s'.here = .head a') (hz : Sized a.F) : a'.F.trees = a.F.trees := by
  obtain ⟨a₁, a₁', tp, G, claim, x, wo, e1, e1', _, _, _, _, hm, hF, _⟩ := decide_inv h
  obtain ⟨_, _, _, _, _, v, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hsF, hhide, _⟩ :=
    mergeHear_inv hm
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  have hz1 : Sized ({ a₁.F with next := a₁.F.next + 1 + 2 * P.lay.lk + 2 } : Fork) := hz
  have hs := (OnBytes.PscRun.hideRun_ok _ G _ _ _ hz1 hhide).1
  rw [hF]
  show G.trees = _
  unfold OnBytes.PscRun.Same at hs
  rw [hs]

/-- **THE TWO TESTS ON THE LEDGER STAY TRUE ACROSS THE MERGE**: "a ledger is open, with one entry a
slot in its three arrays"; "every slot from the next free number on is free, and there are n slots".
-/
theorem merge_keeps_ledger (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') (n : ℕ) (hl : ledgerB s = true)
    (hf : freeAboveB n s = true) : ledgerB s' = true ∧ freeAboveB n s' = true := by
  obtain ⟨a, a', ha, ha', ho, ho', H⟩ := merge_ledger P h
  have eF : s.fork? = some a.F := by
    unfold S.fork?
    rw [ha]
    simp only [ho, if_true]
  have eF' : s'.fork? = some a'.F := by
    unfold S.fork?
    rw [ha']
    simp only [ho', if_true]
  unfold ledgerB at hl ⊢
  unfold freeAboveB at hf ⊢
  rw [eF] at hl hf
  rw [eF']
  simp only [Option.any_some, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    Bool.not_eq_true'] at hl hf ⊢
  obtain ⟨hn, hns, hz', hw⟩ := H ⟨hl.1.1, hl.1.2, hl.2⟩
  refine ⟨⟨⟨hz'.1, hz'.2.1⟩, hz'.2.2⟩, fun j hj => ?_, by rw [hns]; exact hf.2⟩
  have hj' : a'.F.next + j < a'.F.ns := by omega
  have hb : a'.F.next + j < a'.F.gotF.size := by rw [hz'.2.2]; exact hj'
  have h0 := hf.1 (a'.F.next + j - a.F.next) (by rw [hn, hns] at *; omega)
  rw [show a.F.next + (a'.F.next + j - a.F.next) = a'.F.next + j by rw [hn]; omega] at h0
  have hb0 : a'.F.next + j < a.F.gotF.size := by rw [hl.2, ← hns]; exact hj'
  have e0 : a.F.gotF.getD (a'.F.next + j) false = false := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb0] at h0 ⊢
    exact h0
  have e1 : ¬ Filled a'.F (a'.F.next + j) := fun hF =>
    absurd ((hw _ (by rw [hn]; omega)).1 hF) (by unfold Filled; rw [e0]; simp)
  unfold Filled at e1
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hb] at e1 ⊢
  simpa using e1

/-- **No slot below the next free number turns across the merge**: neither a free one is filled nor
a filled one freed. -/
theorem merge_below_next (P : HeadMergeP) {s s' : S} {rs : List Fmt.RoundView}
    (h : headMergeDecide P s rs = .ok s') {a a' : HeadOwn} (ha : s.here = .head a)
    (ha' : s'.here = .head a') (hz : Sized a.F) (j : ℕ) (hj : j < a.F.next) :
    Filled a'.F j ↔ Filled a.F j := by
  obtain ⟨a₁, a₁', e1, e1', _, _, H⟩ := merge_ledger P h
  obtain rfl : a₁ = a := by
    rw [ha] at e1
    exact (Here.head.inj e1).symm
  obtain rfl : a₁' = a' := by
    rw [ha'] at e1'
    exact (Here.head.inj e1').symm
  exact (H hz).2.2.2 j (by omega)

end VerifiableInference.Desc.First.MergeLaw

#print axioms VerifiableInference.Desc.First.MergeLaw.merge_trees
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_keeps_ledger
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_below_next
#print axioms VerifiableInference.Desc.First.MergeLaw.merge_ledger
