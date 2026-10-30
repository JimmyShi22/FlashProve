-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
One file of the set on the key file's table of joints (Johnson/Desc/Key/KeyBorders.lean).
Johnson/RunOne/KeyFenceOrder.lean: THE TIE: KeyFenceB.inOrderB's YES GIVES Means.InOrder (Johnson/Desc/Means/Order.lean): so that a run of the Bool at a state shows the last field of the table's free₁ met there.
  groupOk_of_B · inOrder_of_B   **PROVED**
Nothing on soundness.
-/
import Johnson.RunOne.KeyFenceB
import Johnson.Desc.Means.Order
import Johnson.Desc.Key.KeyPubIn
import Johnson.Desc.Key.KeyTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes

theorem groupOk_of_B (S : Statement) (G : Group) (h : groupOkB S G = true) : Means.GroupOk S G := by
  unfold groupOkB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, h2, h3, fun o ho x hx => ?_, fun o ho x hx => ?_⟩
  · have q := h4 o ho
    rw [hx] at q
    have q' : ((x.shape.mainRows == 0 || x.shape.code == G.code) && (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode)) = true := q
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at q'
    exact q'.1
  · have q := h4 o ho
    rw [hx] at q
    have q' : ((x.shape.mainRows == 0 || x.shape.code == G.code) && (x.shape.maskRows == 0 || x.shape.maskCode == G.maskCode)) = true := q
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at q'
    exact q'.2

theorem inOrder_of_B (S : Statement) (h : inOrderB S false = true) : Means.InOrder S := by
  unfold inOrderB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hg, ho⟩ := h
  have key : ∀ (g : Nat) (G : Group), S.groups[g]? = some G → groupOkB S G = true ∧ ∀ r ∈ G.rows.toList, rowInB S G r = true := fun g G hG => by
    have q := hg g (Array.getElem?_eq_some_iff.1 hG).1
    rw [hG] at q
    have q' : (groupOkB S G && G.rows.toList.all fun r => rowInB S G r) = true := q
    simp only [Bool.and_eq_true, List.all_eq_true] at q'
    exact q'
  refine ⟨fun g G hG => groupOk_of_B S G (key g G hG).1, fun g G hG r hr => (rowInB_iff S G r).1 ((key g G hG).2 r hr), fun o x hx r hr => ?_⟩
  exact sampleIn_of_B S o (ho o (Array.getElem?_eq_some_iff.1 hx).1) x hx r hr

/-- KeyPubIn.maskWithB's yes gives KeyTies.MaskWith. -/
theorem maskWith_of_B (place : Nat → Option (Nat × Nat)) (o r : Nat) (h : VerifiableInference.Desc.Key.maskWithB place o r = true) : VerifiableInference.Desc.Key.MaskWith place o r := by
  unfold VerifiableInference.Desc.Key.maskWithB at h
  cases ho : place o with
  | none => simp [ho] at h
  | some a =>
    cases hr : place r with
    | none => simp [ho, hr] at h
    | some b =>
      simp only [ho, hr, Bool.and_eq_true, beq_iff_eq] at h
      exact ⟨a.1, a.2, ho, by rw [h.1, ← h.2]; exact hr⟩

end Johnson.RunOne.KeyRows23

#print axioms Johnson.RunOne.KeyRows23.inOrder_of_B
#print axioms Johnson.RunOne.KeyRows23.maskWith_of_B
