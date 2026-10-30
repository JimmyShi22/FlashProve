-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K2/Law/KindPlaces.lean: the kind "the code switch" (K2): the written
places of the kind are just the members of the first chain's written list of places that have the
kind's name, in that order. So, in scope, no block of the kind in the first chain lacks a row.

  kindPlacesW       by Lean's kernel
  kindPlacesW_bent  a control: the places of another kind's name are not these
  places_nodup_kind no two written places of the kind are at one place
  block_has_place   a block of the kind in the first chain stands at a written place of the kind

Limits. The first chain alone. Public numbers: no property of a prover.
-/
import Johnson.IMR.PlacesScope
import Johnson.IMR.BorderW
import Johnson.Desc.ProofFile.Honest.K2.Law.PlacesCount

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Place Block Chain FileDescription)
open VerifiableInference.Desc.First (S)

set_option maxRecDepth 1000000 in
/-- **The written places of the kind are the written list's members of its name.** -/
theorem kindPlacesW : IM.placesW.filter (fun a => a.kind == .K2) = placesW.map (·.place) := by
  decide +kernel

set_option maxRecDepth 1000000 in
/-- A control: at another kind's name the like equation fails. -/
theorem kindPlacesW_bent :
    IM.placesW.filter (fun a => a.kind == .K1) ≠ placesW.map (·.place) := by
  decide +kernel

/-- No two written places of the kind are at one place. -/
theorem places_nodup_kind : (placesW.map (·.place)).Nodup := by
  rw [← kindPlacesW]
  exact IM.places_nodup.filter _

/-- Every written place of the kind has its name. -/
theorem kind_of_written {p : SwitchPlace} (hp : p ∈ placesW) : p.place.kind = .K2 := by
  have h : p.place ∈ IM.placesW.filter (fun a => a.kind == .K2) := by
    rw [kindPlacesW]
    exact List.mem_map_of_mem hp
  exact beq_iff_eq.1 (List.mem_filter.1 h).2

variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)} {c : Chain S ProofFile.Cl}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}

/-- **A block of the kind in the first chain stands at a written place of the kind.** -/
theorem block_has_place (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {b : Block S ProofFile.Cl}
    (hb : b ∈ c.blocksInOrder) (hk : b.place.kind = .K2) : ∃ p ∈ placesW, p.place = b.place := by
  have h1 : b.place ∈ IM.placesW := by
    rw [← IM.places_scope hS hR O]
    exact List.mem_map_of_mem hb
  have h2 : b.place ∈ placesW.map (·.place) := by
    rw [← kindPlacesW]
    exact List.mem_filter.2 ⟨h1, beq_iff_eq.2 hk⟩
  exact List.mem_map.1 h2

end ProofFile.Honest.K2.Law

#print axioms ProofFile.Honest.K2.Law.kindPlacesW
#print axioms ProofFile.Honest.K2.Law.kindPlacesW_bent
#print axioms ProofFile.Honest.K2.Law.places_nodup_kind
#print axioms ProofFile.Honest.K2.Law.kind_of_written
#print axioms ProofFile.Honest.K2.Law.block_has_place
