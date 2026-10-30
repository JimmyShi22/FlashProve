-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
OnBytes/Tie/Pv/Lay/MergeTarget.lean: the target of the merge's sumcheck in a layers' sub-proof, on
the port's side: how the record's target reads in terms of the lists that were heard.

The merge's start form (wsForkStart, OnBytes/Model/Merge.lean) is the sum of the batching powers
times the slots of the claims' values. A sumcheck's target is the public part of its start form:
the form with what was shown in the place of each slot. The slots of the claims' values are end
slots of the batched sumcheck of the inner products and, in the first group, the slot of the
embedding's scalar. What lies under them stays until the merge begins (`Lies`, `Kept`,
OnBytes/Tie/Pv/Att/HearSaid.lean).

Main names:
  `merge_target_start`: the value of the merge's start form in a world, for all lists of slots and
    of coefficients: a coefficient that is lacking counts as 0.
  `merge_target_sum`: the same at the slots of a layers' sub-proof (`claimSlots`,
    OnBytes/Tie/Pv/Lay/HearOwn.lean).
  `merge_target`: under the records of OnBytes/Tie/Pv/Lay/HearAll.lean (`OwnSaidL`), with routed
    experts: the target of the merge's record reads as the sum, over the claims on the weights, of
    the batching power times the end value of the batched sumcheck that stands behind the two
    sides' values, the gated products' value and the experts' values; in the first group plus the
    last power times the embedding's scalar.

What is not claimed: this is the port's side alone. That the typed chain's claim at the merge names
the same sum is the field t7 of `OwnIs` (OnBytes/Tie/Pv/Lay/HearLater.lean) and is not shown here.
Nothing is said on what the end values or the scalar are worth. The limits of HearAll.lean hold
here too: one direction, from the routines' success.
-/
import OnBytes.Tie.Pv.Lay.HearLater
import OnBytes.Tie.Pv.Keeps.KeepsPend
import OnBytes.Tie.Pv.Keeps.KeepsModel

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace OnBytes.Tie.Pv.Lay.Proved
open Iop Prob Cb TWhole OnBytes OnBytes.Model OnBytes.Model.Road OnBytes.Model.Layer
open Johnson.L5.Layers Cb.Pv.Att Cb.Pv.Lay OnBytes.Tie.Pv.Lay.Eng OnBytes.Tie.Pv.Keeps.Pend
open OnBytes.Psc (Weight hearMany hearOne hidingEntries)
open OnBytes.Tie.Pv.Att (PscH Lies Kept filled_kept filled_lies sum_read SumRead)

/-! ### The value of the merge's start form -/

/-- The loop of the merge's start form, on lists: it adds each slot's value times its coefficient.
Where the coefficients end before the slots, the loop ends, and the sum's terms are 0. -/
theorem merge_target_fold {K : Type} [CommRing K] (ρ : Reading K) (W : World K) :
    ∀ (l : List Nat) (r : List E) (s : Aff),
      ((l.zip r).foldl (fun s y => Aff.addMul s (Aff.slot y.1) y.2) s).value ρ W =
        s.value ρ W +
          ∑ i ∈ Finset.range l.length, ρ.val (r.getD i zeroE) * W.slot (l.getD i 0)
  | [], r, s => by simp
  | a :: l, [], s => by
    rw [List.zip_nil_right, List.foldl_nil]
    simp [ρ.zero]
  | a :: l, b :: r, s => by
    rw [List.zip_cons_cons, List.foldl_cons, merge_target_fold ρ W l r, Aff.value_addMul,
      Aff.value_slot, List.length_cons, Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero]
    ring

/-- The value of the merge's start form. -/
theorem merge_target_start {K : Type} [CommRing K] (ρ : Reading K) (W : World K)
    (sv : Array Nat) (rho : Array E) :
    (wsForkStart sv rho).value ρ W =
      ∑ i ∈ Finset.range sv.size, ρ.val (rho.getD i zeroE) * W.slot (sv.getD i 0) := by
  unfold wsForkStart
  rw [← Array.foldl_toList, Array.toList_zip, merge_target_fold, Aff.value_empty, zero_add,
    Array.length_toList]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [List.getD_eq_getElem?_getD, Array.getD_eq_getD_getElem?, Array.getElem?_toList]

/-! ### The slots of the claims' values -/

/-- The number of the slots. -/
theorem merge_target_size (g n sV sVE : Nat) :
    (claimSlots g n sV sVE).size = n + (if g == 0 then 1 else 0) := by
  unfold claimSlots
  split <;> simp

/-- The slots of the claims without the embedding's follow one another from sV on. -/
theorem merge_target_low (g n sV sVE i : Nat) (hi : i < n) :
    (claimSlots g n sV sVE).getD i 0 = sV + i := by
  unfold claimSlots
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_left (by simpa using hi)]
  simp [hi]

/-- In the first group the last slot is that of the embedding's scalar. -/
theorem merge_target_top (g n sV sVE : Nat) (hg : (g == 0) = true) :
    (claimSlots g n sV sVE).getD n 0 = sVE := by
  unfold claimSlots
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_append_right (by simp)]
  simp [hg]

/-- The value of the merge's start form at the slots of a layers' sub-proof. -/
theorem merge_target_sum {K : Type} [CommRing K] (ρ : Reading K) (W : World K)
    (g n sV sVE : Nat) (w : Array E) :
    (wsForkStart (claimSlots g n sV sVE) w).value ρ W =
      (∑ a : Fin n, ρ.val (w.getD a.1 zeroE) * W.slot (sV + a.1)) +
        (if g == 0 then ρ.val (w.getD n zeroE) * W.slot sVE else 0) := by
  have lo : ∑ i ∈ Finset.range n,
      ρ.val (w.getD i zeroE) * W.slot ((claimSlots g n sV sVE).getD i 0) =
      ∑ a : Fin n, ρ.val (w.getD a.1 zeroE) * W.slot (sV + a.1) := by
    rw [Finset.sum_range]
    exact Finset.sum_congr rfl fun a _ => by rw [merge_target_low _ _ _ _ _ a.2]
  rw [merge_target_start, merge_target_size]
  by_cases hg : (g == 0) = true
  · rw [if_pos hg, if_pos hg, Finset.sum_range_succ, lo, merge_target_top _ _ _ _ hg]
  · rw [if_neg hg, if_neg hg, add_zero, add_zero, lo]

/-! ### The target -/

variable {K : Type} [Field K] [Fintype K] (ρ : Reading K)

/-- The merge's target, the port's side: the record's target reads as the batched sum of what was
heard for the claims' values. -/
theorem merge_target {P : Pub} {hp : HPlan2} {g : Nat} {fo : Forest.Heard} {O : Own} {F G : Fork}
    {D : OwnH} {H0 : Heard} {tT : Tsc} {hd2 : Level} {claims : Array WsClaim}
    (hp3 : P.y.h.p3 = true) (s : OwnSaidL P hp g fo O F G D H0 tT hd2 claims) :
    ρ.val O.wo.p.target =
      (∑ a : Fin (nclp hp g),
        ρ.val ((powers D.xW (claimSlots g (nclp hp g) O.K.sV O.sVE).size).getD a.1 zeroE) *
          ρ.val (D.H4.v.getD (2 + (1 + P.y.LamM) + a.1) zeroE)) +
      (if g == 0 then
        ρ.val ((powers D.xW (claimSlots g (nclp hp g) O.K.sV O.sVE).size).getD (nclp hp g) zeroE) *
          ρ.val (D.vE.getD 0 zeroE) else 0) := by
  obtain ⟨F4, F7, F8, F1, F1', F2, F3, F3', F5, F6, t3, C, p4, c1, c5, _, _, _, _, _, _, _, _,
    _, _, a11, a12, a13, fn, a14, a15, a16, a17⟩ := s.recs
  obtain ⟨_, Fm, _, g5, g6⟩ := a14.said
  obtain ⟨τ, q1, q2⟩ := a17.psc
  -- what lies under a slot behind the routed experts' layer lies there where the merge begins
  have k56 : Kept F5 F6 := by
    by_cases hg : (g == 0) = true
    · exact (taken_kept F5 1).trans (filled_kept (a15 hg).2)
    · rw [a16 (Bool.eq_false_iff.2 hg)]
      exact fun _ _ h => h
  have hl : ∀ a, a < nclp hp g →
      Lies F6 (O.K.sV + a) (D.H4.v.getD (2 + (1 + P.y.LamM) + a) zeroE) := by
    intro a ha
    have h0 := filled_lies a12 (2 + (1 + P.y.LamM) + a) (by
      rw [a11.vals]
      simp only [hp3, if_true]
      omega)
    rw [show O.K.sA0 + (2 + (1 + P.y.LamM) + a) = O.K.sV + a by
      rw [fn.sV]
      simp only [hp3, if_true]
      omega] at h0
    exact k56 _ _ (g6.kept _ _ (g5.kept _ _ (filled_kept a13 _ _ h0)))
  have ht : (g == 0) = true → Lies F6 O.sVE (D.vE.getD 0 zeroE) := by
    intro hg
    have h0 := filled_lies (a15 hg).2 0 (by
      rw [s.lenE, if_pos hg]
      exact Nat.one_pos)
    rw [Nat.add_zero, ← (a15 hg).1] at h0
    exact h0
  rw [q2.target, OnBytes.Tie.Pv.Att.public_value ρ F6 _ τ q1, merge_target_sum]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    show _ * ρ.val (F6.vp.getD _ zeroE) = _
    rw [(hl a.1 a.2).2]
  · by_cases hg : (g == 0) = true
    · rw [if_pos hg, if_pos hg]
      show _ * ρ.val (F6.vp.getD _ zeroE) = _
      rw [(ht hg).2]
    · rw [if_neg hg, if_neg hg]

end OnBytes.Tie.Pv.Lay.Proved
