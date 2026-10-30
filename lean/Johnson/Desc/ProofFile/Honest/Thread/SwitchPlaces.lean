-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Thread/SwitchPlaces.lean: THREE LEMMAS ON THE PLACES OF THE CODE
SWITCH's LIST (`K2.switchPlaces`, Johnson/Desc/ProofFile/Honest/K2/Half.lean), IN A LIGHT FILE OF
THEIR OWN: they are places of the kind in the plan's list, in its order; a place of the kind in the
plan's list is one of them; and the list has a place. On public data alone. The third is
CONDITIONAL: on an opening of the description's maker's return, and on the description's own test on
the plan. Lemmas.

Whose. By the authors of the attention sub-protocol's (K5's) own rounds. The three need none of the
lists of all kinds: they are laid here so that a file on the switches' places can call them over few
imports.

Main names (namespace ProofFile.Honest.SwitchPlaces):
  `k2_places_sub`: the places of `K2.switchPlaces Z G` are a sublist of the plan's places of the
    kind (`P1K2.purePlaces Z`). No premise.
  `k2_place_of_spot`: a place of the kind in the plan's list is a place of `K2.switchPlaces Z G`,
    where what the kind makes once of the plan is made.
  `k2_place_there`: at an opening, where the description passes its own test on the plan, the list
    at the maker's ground has a place: the first behind the segments.

Limits. Of what a place holds beside its address nothing is said. Through
Johnson/Loose/H2K12/SpotsAtAll.lean the file stands above Cb/Bridge/CodeListRSProved.lean, and so
above the files under ThirdParty/ (lean/LIMITS.md, L15): a fact on import lines.
Nothing is claimed on soundness, completeness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Half
import Johnson.Loose.H2K12.SpotsAtAll
import Johnson.IMR.PlanOkFlat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.SwitchPlaces
open VerifiableInference.Desc (Block Chain FileDescription Place KindName)
open VerifiableInference.Desc.First (S)

section
variable (Z : Pub) (G : Ground)

/-- The places of the list's sides are places of the kind in the plan's list, in its order. -/
theorem k2_places_sub :
    ((K2.switchPlaces Z G).map (·.place)).Sublist ((P1K2.purePlaces Z).map (·.place)) := by
  unfold K2.switchPlaces P1K2.purePlaces
  split
  · rename_i P sps _ hs
    rw [hs, List.map_map]
    exact List.Sublist.refl _
  · exact List.nil_sublist _

/-- **A place of the kind in the plan's list is a place of the list**, where what the kind makes
once of the plan is made. Conditional: hP; hs; hsp; hk. -/
theorem k2_place_of_spot {P : P1K2.Prep} {sps : List Spot} (hP : P1K2.prepOf Z G = some P)
    (hs : spotsOf Z.cuts = some sps) {sp : Spot} (hsp : sp ∈ sps) (hk : sp.place.kind = .K2) :
    ∃ p ∈ K2.switchPlaces Z G, p.place = sp.place := by
  unfold K2.switchPlaces
  rw [hP, hs]
  exact ⟨_, List.mem_map.2 ⟨sp, List.mem_filter.2 ⟨hsp, by rw [hk]; rfl⟩, rfl⟩, rfl⟩

variable {o : SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription Inst} {Bs : PureBase}
  {base : List (Block S Cl)} {c : Chain S Cl} {A : SharedSeat} {B : SecondSeat}

/-- **THE LIST HAS A PLACE: the first behind the segments**, at the ground that the description's
maker makes. CONDITIONAL: an opening; hF: the description passes its own test on the plan. So the
premise "p is one of the list's places" is not empty there. -/
theorem k2_place_there (O : IM.Open o pol lay KL F Z Bs base c A B) (hF : F.planOk = true) :
    ∃ p ∈ K2.switchPlaces Z Bs.G₀, p.place = ⟨1, none, 1, .K2⟩ := by
  obtain ⟨b, x, e1, hx, epx, hla, -⟩ := IM.k2_finish_of O
  have hm : ({ b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter } : Block S Cl) ∈ c.blocksInOrder := by
    unfold Chain.blocksInOrder
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_append_right _
      (List.mem_map.2 ⟨b, List.mem_of_getElem? e1, rfl⟩)))
  have hb0 := List.all_eq_true.1 (IM.blocksOk_of_planOk O hF) _ hm
  have hb : b.planOk = true := by
    simp only [Bool.and_eq_true] at hb0
    exact hb0.1.1
  obtain ⟨P, n, hP, -⟩ := (IM.k2_mem hx).live_alone hla hb
  have hN := (H2K12.table_apart O).1
  rw [H2K12.table_is] at hx
  obtain ⟨sp, hsp, rfl⟩ := List.mem_map.1 hx
  have e2 : sp.place = ⟨1, none, 1, .K2⟩ := (H2K12.entry_own hN sp hsp).symm.trans epx
  have hs := (IM.base_made O.made).1
  unfold P1K2.purePlaces at hsp
  rw [hs] at hsp
  obtain ⟨p, hp, e3⟩ := k2_place_of_spot Z Bs.G₀ hP hs (List.mem_filter.1 hsp).1 (by rw [e2])
  exact ⟨p, hp, e3.trans e2⟩

end

end ProofFile.Honest.SwitchPlaces

#print axioms ProofFile.Honest.SwitchPlaces.k2_places_sub
#print axioms ProofFile.Honest.SwitchPlaces.k2_place_of_spot
#print axioms ProofFile.Honest.SwitchPlaces.k2_place_there
