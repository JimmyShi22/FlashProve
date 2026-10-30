--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
ToldInScope.lean: told_succ (Johnson/Desc/First/ToldSucc.lean) AT
THE IOP's OWN FIRST CHAIN, IN THE GOALS' SCOPE: ITS ONE PREMISE "NO PLACE TWICE" IS PAID.
  placesW_nodup    the written list of the 358 places has no place twice: A
                   CLOSED FACT, by the kernel.
  places_nodup     in scope: so have the first chain's sub-protocols' own places (places_scope).
  told_succ_scope  in scope, at any N s links: the k-th sub-protocol of the flat list is b: the two
                   counts of the numbers closed over that list go on, along the written list, by
                   what b tells.
What is not claimed. That the composer's N is the numbers so closed (another house's N_closed).
Nothing on the verifier's state. Nothing on soundness.

-/
import Johnson.IMR.PlacesScope
import Johnson.Desc.First.ToldSucc

set_option autoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace LPFK9

open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S ModelPart Numbers blockPlaces told_succ_ps)
open ProofFile (Cl)

set_option maxRecDepth 1000000 in
/-- **The written list has no place twice.** -/
theorem placesW_nodup : IM.placesW.Nodup := by decide +kernel

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)} {c : Chain S Cl} {A : ProofFile.SharedSeat}
  {B : ProofFile.SecondSeat}

theorem places_nodup (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) : (blockPlaces c.blocksInOrder).Nodup := by
  show (c.blocksInOrder.map (·.place)).Nodup
  rw [IM.places_scope hS hR O]
  exact placesW_nodup

/-- **In scope the two counts go on by what the sub-protocol at the place tells.** -/
theorem told_succ_scope (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (N : Numbers)
    (s : OnBytes.Params.ReqShape) (links : List ModelPart) (k : Nat) (b : Block S Cl)
    (hb : c.blocksInOrder[k]? = some b) :
    (N.atBlocks s links c.blocksInOrder).treesAt IM.placesW[k + 1]? =
        (N.atBlocks s links c.blocksInOrder).treesAt IM.placesW[k]? + b.oracles.flatten.length ∧
      (N.atBlocks s links c.blocksInOrder).msgsAt IM.placesW[k + 1]? =
        (N.atBlocks s links c.blocksInOrder).msgsAt IM.placesW[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum :=
  told_succ_ps N s links c.blocksInOrder IM.placesW (IM.places_scope hS hR O) placesW_nodup k b hb

end

end LPFK9

#print axioms LPFK9.placesW_nodup
#print axioms LPFK9.places_nodup
#print axioms LPFK9.told_succ_scope
