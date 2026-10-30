-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/EndIs358.lean: no soundness is claimed.
The premise hE of sampleTwoB_h4 | sampleTwoB_h4_paid («what Rc says is reached at border 358, in a family that hands back»), at «the first chain's last state is reached» as Johnson/Top/H0/Walk/ReachThree.lean says it (EndAt₁). hE wants the list's length.
  flat_358            in scope, at the opening: c.blocksInOrder.length = 358 (places_scope, Johnson/IMR/PlacesScope.lean | places_len, Johnson/IMR/WrittenList.lean: a line of the proof of flat_cases, Johnson/IMR/FlatCases.lean, as a lemma)
  **reach358_of_end**  EndAt₁ (ProofFile.fileDescBy … c) p ⇒ Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 p: the family at which handsBackB_below | handsBack_below stand
  **hE_of_end**        so hE, at Rch := that family, for every get | Oc | Rc with Rc q → EndAt₁ … (z q, (get q).2)
No member. Nothing on soundness.
-/
import Johnson.ToldDescR.HandsBackB
import Johnson.IMR.FlatCases
import Johnson.Top.H0.Walk.ReachThree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open VerifiableInference.Desc
open VerifiableInference.Desc.First (S)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
  {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
  {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

theorem flat_358 (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : c.blocksInOrder.length = 358 := by
  rw [← List.length_map (f := (·.place)), IM.places_scope hS hR O, IM.places_len]

theorem reach358_of_end (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {p : ProofFile.InstPub × S}
    (h : EndAt₁ (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B (fun s => s)
      (ProofFile.startS Z) c) p) :
    Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 p := by
  have h' : Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) c.blocksInOrder.length p := h
  rwa [flat_358 hS hR O] at h'

theorem hE_of_end (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {Q P₀ : Type}
    (get : Q → P₀ × S) (zOf : Q → ProofFile.InstPub) (Oc : Q → Strs → Prop) (Rc : Q → Prop)
    (hRc : ∀ q, Rc q → EndAt₁ (ProofFile.fileDescBy OnBytes.secondHashFunction ProofFile.pureRoad.links Z A B
      (fun s => s) (ProofFile.startS Z) c) (zOf q, (get q).2)) :
    ∀ q y, Oc q y → Rc q →
      ∃ z, Reach 0 (c.blocksInOrder.map Sound.below) (ProofFile.startS Z) 358 (z, (get q).2) :=
  fun q _ _ hq => ⟨zOf q, reach358_of_end hS hR O (hRc q hq)⟩

end

end ToldDesc

#print axioms ToldDesc.flat_358
#print axioms ToldDesc.reach358_of_end
#print axioms ToldDesc.hE_of_end
