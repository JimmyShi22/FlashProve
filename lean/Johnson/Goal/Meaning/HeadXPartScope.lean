-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HeadXPartScope.lean: WHAT THE TWO CHEAP PUBLIC TESTS planK6AtZ AND padsAtZ
(Johnson/Desc/Kinds/HeadDoorAtZ.lean) READ OF THE PUBLIC PARAMETERS X, BUT FOR ONE NUMBER, AS CLOSED
VALUES IN THE GOALS' SCOPE. A joining of other files' theorems
(Johnson/Goal/Meaning/HidOwner.lean, HidSeatsOf.lean, HidPlanNM.lean). Theorems.

What is proved. Under publicOf pol KL lay = .ok X and Hd.PublicCore X.P (xPart_of_core), and so in
the goals' scope (xPart_in_scope):
  nhf      X.hS.NHf = 4.
  nm       X.H.tl.NM = 8: the output head's list has eight matrices.
  ixi      (matIx X.y).iXI = 8.
  nas      nasOf X g = 1 for g < 12.
  head     for a < 8: the label of matrix a of the head's list names (22, "M7"'s number 7) at a = 7,
          and (24, a) else.
  layers   for 0 < g < 12: the label of matrix 8 of segment 2 g names (2 (g - 1), 7).
  att      for g < 12: the label of matrix 4 of segment 2 g + 1 names (2 g, 6).
"Names": ownerP (labsOf X k a) = (the owning segment, Meaning.nameOf (the array's number there)).

No existential quantifier.
Not proved here. X.H.ns, the number of mask entries in use, which the first test also reads: see
Law/PlanK6NoNs.lean. Nothing on the layout, the codes or what is sent. The full size only. Nothing
on soundness.

-/
import Johnson.Desc.Kinds.Law.HeadDoorRowsLaw
import Johnson.Goal.Meaning.HidPlanNM
import Johnson.Goal.Meaning.HidSeatsOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes OnBytes.Road
open OnBytes.Model.Verify (publicOf Public)
open OnBytes.Model.Layer (matIx)

/-- What the two tests read of X, but for X.H.ns, as closed values. -/
structure XPart (X : Public) : Prop where
  nhf : X.hS.NHf = 4
  nm : X.H.tl.NM = 8
  ixi : (matIx X.y).iXI = 8
  nas : ∀ g, g < 12 → nasOf X g = 1
  head : ∀ a, a < 8 →
    ownerP (labsOf X 24 a) = if a = 7 then (22, Meaning.nameOf 7) else (24, Meaning.nameOf a)
  layers : ∀ g, 0 < g → g < 12 → ownerP (labsOf X (2 * g) 8) = (2 * (g - 1), Meaning.nameOf 7)
  att : ∀ g, g < 12 → ownerP (labsOf X (2 * g + 1) 4) = (2 * g, Meaning.nameOf 6)

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}

/-- The label's owner, as the tests read it. -/
theorem ownerP_of (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {k a : ℕ}
    (hk : k < 25) (ha : a < (Meaning.matsAt X k).size) :
    ownerP (labsOf X k a) =
      ((Meaning.ownerOf X k a).1, Meaning.nameOf (Meaning.ownerOf X k a).2) := by
  rw [labs_eq, owner_eq, ← Meaning.owner_label h C hk ha]

theorem xPart_of_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) : XPart X := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have hN : X.hS.NHf = 4 := (Hd.numH_of_layout B.full B.head).NHf
  obtain ⟨i6, i7, i8⟩ := Meaning.ix_of_core h C
  have hA : ∀ g, g < 12 → (Hd.shapeA X g).cf.NAs = 1 := fun g hg => by
    obtain ⟨_, _, n1, _⟩ := Meaning.matsAt_att_gid h C hg
    exact n1
  refine ⟨hN, ?_, i8, fun g hg => by rw [nas_eq]; exact hA g hg, ?_, ?_, ?_⟩
  · have n := Meaning.nmFit_of_core h C
    unfold Meaning.nmFit at n
    rw [List.all_eq_true] at n
    have e := of_decide_eq_true (n 24 (List.mem_range.2 (by norm_num)))
    have s := Meaning.size_head h C
    exact e.trans s
  · intro a ha
    rw [ownerP_of h C (by norm_num) (by rw [Meaning.size_head h C]; exact ha)]
    unfold Meaning.ownerOf
    rw [if_pos rfl, hN, i7]
    by_cases e : a = 7
    · rw [if_pos e, if_pos e]
    · rw [if_neg e, if_neg e]
  · intro g h0 hg
    rw [ownerP_of h C (by omega) (by rw [Meaning.size_even h C hg]; norm_num)]
    unfold Meaning.ownerOf
    rw [if_neg (by omega), if_neg (by omega), i8, i7, if_pos ⟨rfl, by omega⟩]
    show (2 * g - 2, _) = _
    rw [show 2 * g - 2 = 2 * (g - 1) by omega]
  · intro g hg
    rw [ownerP_of h C (by omega) (by rw [Meaning.size_odd h C hg]; norm_num)]
    unfold Meaning.ownerOf
    rw [if_neg (by omega), if_pos (by omega), show (2 * g + 1) / 2 = g by omega, hA g hg, i6,
      if_pos rfl]
    rfl

/-- **In the goals' scope.** -/
theorem xPart_in_scope {Z : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} (hZ : VerifierAndGoals.InScope Z = true)
    (hR : VerifierAndGoals.readFiles Z = .ok pp) (h : publicOf Z.pol Z.KL lay = .ok X) : XPart X :=
  xPart_of_core h (Hd.core_of_scope hZ hR h)

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.ownerP_of
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.xPart_of_core
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.xPart_in_scope
