-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LPFK9R/SubsFull.lean: JOININGS: THE TWO PREMISES ON PUBLIC DATA OF THE
TABLE's NUMBERS CLOSED OVER THE IOP's OWN SUB-PROTOCOLS, IN THE LETTERS OF THEIR USER
(blockPlaces_at | N_closed, Johnson/P5J/LettersAt2.lean), OFF Johnson/IMR/PlacesScope.lean, CALLED.
  linksW_full      the written row of sorts (IM.linksW) IS Desc.Sound.linksFull: by the kernel.
  subs_full        in the goals' scope: ProofFile.subsOf Z = Desc.Sound.linksFull (subs_all).
  blockPlaces_full in scope: the sub-protocols' own places ARE the driver's list at that row, with
                   "several": OUTRIGHT (places_any): so neither premise is wanted by who calls this.
  k13_stands       (no premise on scope; every o) a sub-protocol of the kind K13 stands in the first
                   chain's flat list: the third behind the links (back_of), as the flat list lays
                   it.
What is not claimed. Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.IMR.PlacesScope
import Johnson.Desc.Sound.AtDriver
import Johnson.Desc.First.NumbersAtBlocks

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open VerifiableInference.Desc (Block Chain FileDescription KindName)
open VerifiableInference.Desc.First (S ModelPart flatPlacesOf blockPlaces)
open VerifiableInference.Desc.Sound (linksFull)
open ProofFile (Cl)

theorem linksW_full : IM.linksW = linksFull := by decide

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

/-- **In scope the sorts of segments are the written list.** -/
theorem subs_full (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : ProofFile.subsOf Z = linksFull :=
  (IM.subs_all hS hR O).trans linksW_full

/-- **In scope the sub-protocols' own places are the written list.** -/
theorem blockPlaces_full (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) :
    blockPlaces c.blocksInOrder = flatPlacesOf linksFull true := by
  show c.blocksInOrder.map (·.place) = _
  rw [IM.places_any O, subs_full hS hR O]

end

/-- **A sub-protocol of the kind K13 stands in the first chain's flat list.** -/
theorem k13_stands {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl}
    {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} (O : IM.Open o pol lay KL F Z Bs base c A B) :
    ∃ b ∈ c.blocksInOrder, b.place.kind = KindName.K13 := by
  obtain ⟨-, -, ⟨b, b', hb, -, -, hL⟩, -⟩ := IM.back_of O
  have hm : b ∈ c.back := List.mem_of_getElem? hb
  refine ⟨{ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }, ?_, ?_⟩
  · exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, hm, rfl⟩)))
  · show b.place.kind = KindName.K13
    have e : b = IM.seatedAs ProofFile.sameReply b' b.name (IM.bAt 2 .K13) := hL
    rw [e]
    rfl

end LPFK9

#print axioms LPFK9.linksW_full
#print axioms LPFK9.subs_full
#print axioms LPFK9.blockPlaces_full
#print axioms LPFK9.k13_stands
