-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/MergeBelowReached.lean: THE SLOT OF THE MERGE's END VALUE LIES BELOW THE OPEN
LEDGER's NEXT SLOT, AT EVERY STATE THAT THE FIRST CHAIN's RUN REACHES IN A LAYERS' SEGMENT FROM JUST
BEHIND K4's SUB-PROTOCOL (28 g + 5) TO THE FRONT OF THE LOOKUP ON THE DIGITS (28 g + 8). A JOIN OF
TWO FILES' THEOREMS: the make (`mergeBelow_made`, Johnson/Road/K4/MergeBelow.lean) and the keeping
(`OwnLater` and the steps back, Johnson/Desc/First/Link/Law/StretchParts.lean).
Statements with their proofs: calls.

  `below_of_ownLater`: s.own? = some o · s.fork? = some G · o.wo.sFv + 1 = G.next · OwnLater s s' ⟹
    MergeBelow s'.
  `ownLater_back6` · `ownLater_back7`: from 28 g + 6 and 28 g + 7 back to 28 g + 5 (the other
  file's own proof of its `ownLater_back`, cut short).
  **`mergeBelow_reach`**: hS · hR · an opening · F.planOk = true · g < 12 · i < 4 · Reach 0 c.blocksInOrder
  start (28 * g + 5 + i) (z, s') ⟹ MergeBelow s'. **`mergeBelow_reached`**: the same at the relation
  "reached" of the IOP as written in Lean.

Limits. A LAYERS' SEGMENT's FOUR BORDERS ALONE. Nothing at the output head's segment. At an
attention's segment, and in front of K4, the reader finds no slot by its text: not stated here. That
there is an opening is shown by no theorem here. K04_law, the law of K4's sub-protocol itself, IS
NOT PROVED. Nothing on soundness.
-/
import Johnson.Road.K4.MergeBelow
import Johnson.Desc.First.Link.Law.StretchParts

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.Model
open OnBytes.Model.Layer (Own)
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.LinkJoin (OwnLater ownLater_trans ownLater_back back_k8_of
  back_readsL_of k1_ownLater k8_ownLater quietLayers_ownLater k8Ix)
open Johnson.Desc.First.Walk.Tied (Reach RchAt rchAt_raw)

theorem below_of_ownLater {s s' : S} {o : Own} {G : Fork} (ho : s.own? = some o)
    (hG : s.fork? = some G) (e : o.wo.sFv + 1 = G.next) (K : OwnLater s s') : MergeBelow s' := by
  intro j hj
  rw [mergeOf_own (K.1.trans ho)] at hj
  obtain rfl := Option.some.inj hj
  obtain ⟨G', hG', L⟩ := K.2 G hG
  have := L.next
  exact ⟨G', hG', by omega⟩

variable {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : VerifiableInference.Desc.Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {g : ℕ} {Q : Type} {start : Q → S}

theorem ownLater_back6 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 6) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ OwnLater s s' :=
  back_readsL_of ownLater_trans k1_ownLater quietLayers_ownLater hS hR O hg h

theorem ownLater_back7 (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hg : g < 12) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 7) (z, s')) :
    ∃ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) ∧ OwnLater s s' := by
  have n24 : 2 * g ≠ 24 := by omega
  have i8 : k8Ix (2 * g) = 4 := by
    show 4 + (if 2 * g = 24 then 1 else 0) = 4
    simp [n24]
  have e7 : 28 * g + 7 = 14 * (2 * g) + 4 + 2 + 1 := by omega
  rw [e7] at h
  obtain ⟨s₁, r1, q1⟩ := back_k8_of k8_ownLater hS hR O (l := 2 * g) (by omega) (z := z)
    (s' := s') (by rw [i8]; exact h)
  rw [i8] at r1
  have e6 : 14 * (2 * g) + 4 + 2 = 28 * g + 6 := by omega
  rw [e6] at r1
  obtain ⟨s₀, r0, q0⟩ := ownLater_back6 hS hR O hg r1
  exact ⟨s₀, r0, ownLater_trans _ _ _ q0 q1⟩

/-- **From just behind K4 to the front of the lookup on the digits.** -/
theorem mergeBelow_reach (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {i : ℕ} (hi : i < 4) {z : Q} {s' : S}
    (h : Reach 0 c.blocksInOrder start (28 * g + 5 + i) (z, s')) : MergeBelow s' := by
  have key : ∀ s, Reach 0 c.blocksInOrder start (28 * g + 5) (z, s) → OwnLater s s' → MergeBelow s' := by
    intro s hr K
    obtain ⟨o, G, ho, hG, e⟩ := mergeBelow_made hS hR O hOk hg hr
    exact below_of_ownLater ho hG e K
  obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  · exact mergeBelow_behind hS hR O hOk hg h
  · obtain ⟨s, hr, K⟩ := ownLater_back6 hS hR O hg h
    exact key s hr K
  · obtain ⟨s, hr, K⟩ := ownLater_back7 hS hR O hg h
    exact key s hr K
  · obtain ⟨s, hr, K⟩ := ownLater_back hS hR O hg h
    exact key s hr K

/-- **The same at the relation "reached" of the IOP as written in Lean.** -/
theorem mergeBelow_reached (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction Pb.pol ly Pb.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hg : g < 12) {i : ℕ} (hi : i < 4) {Str : Type}
    {a : ((descAt Z A B c).XiPub × (descAt Z A B c).S₁) × Str}
    (h : RchAt (descAt Z A B c) (28 * g + 5 + i) a) : MergeBelow a.1.2 :=
  mergeBelow_reach hS hR O hOk hg hi (z := a.1.1) (s' := a.1.2) (rchAt_raw h)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.below_of_ownLater
#print axioms OnBytes.Road.K4.ownLater_back6
#print axioms OnBytes.Road.K4.ownLater_back7
#print axioms OnBytes.Road.K4.mergeBelow_reach
#print axioms OnBytes.Road.K4.mergeBelow_reached
