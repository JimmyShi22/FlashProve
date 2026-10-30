-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Shape/Scope/OwesPlaces.lean: FROM THE WRITTEN LIST OF PLACES TO THE FIRST CHAIN's MEMBER AT THE SAME NUMBER, UNDER THE HEAD.

Limits. Every premise named here stays a premise. Nothing on soundness, completeness or hiding.
-/
import Johnson.P5J.PlacesPaid
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace Johnson.AtFull.Shape.Scope
open VerifiableInference.Desc (Block Chain Place)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **The member at a number of the written list.** -/
theorem member_of_ps (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {b : Nat} {p : Place}
    (hp : P5J.At.ps[b]? = some p) : ∃ blk, cF.blocksInOrder[b]? = some blk ∧ blk.place = p := by
  have e := P5J.At.places_paid h.scope h.reads h.laid
  rw [← e] at hp
  unfold VerifiableInference.Desc.First.blockPlaces at hp
  rw [List.getElem?_map] at hp
  obtain ⟨blk, hb, rfl⟩ := Option.map_eq_some_iff.1 hp
  exact ⟨blk, hb, rfl⟩

end Johnson.AtFull.Shape.Scope

#print axioms Johnson.AtFull.Shape.Scope.member_of_ps
