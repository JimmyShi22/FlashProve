-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/H2K5R/PlaceAtFlat.lean: KIND K5: ONE NUMBER k: the number at which the
kind's entry stands in the first chain's flat list is the number at which the driver's own list of
places has the kind's place, and the next number has the segment's fourth hearing place.

Why. The rule of composition walks two lists by one number k: the description's flat list of blocks
(c.blocksInOrder[k]) and a list of places (ps[k], ps[k + 1]), off which its table of rows is read.
LawAtLaid.lean names k := IM.flatIx c (2 g + 1) 2 for the first. Here the second is tied to it.

OVER WHAT IT STANDS: all that LawAtEntry.lean's head names, and
Johnson/IMR/FlatScope.lean.

Main names:
  `linkPlaces_att3`, `linkPlaces_att4`: numbers 3 and 4 of the driver's list of an attention
    segment's places (by unfolding).
  `K05_place_at`: **at an opening's letters, at every o, where the proof covers attention, for g
    below the number of groups: there is the flag "several" with: the flat list's places are
    flatPlacesOf (ProofFile.subsOf Z) several; the plan's row of links has attention at 2 g + 1; that list
    has ⟨1, some (2 g + 1), 3, K5⟩ at IM.flatIx c (2 g + 1) 2 and ⟨1, some (2 g + 1), 4, K1⟩ at the
    next number.**
From chainBy_first (LawAtEntry.lean), flat_places (Johnson/Desc/First/Driver/PlacesLaw.lean),
IM.link_flat_places and IM.link_at_flat.
Limits. The list of links is ProofFile.subsOf Z, the plan's own row. That it is a written list is a fact
in scope, not said here.
No soundness of the protocol is claimed.
Nothing is claimed on completeness or hiding.

-/
import Johnson.H2K5R.LawAtEntry
import Johnson.IMR.FlatScope
import Johnson.Desc.First.Driver.PlacesLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Claim Block Place Chain Link FileDescription KindName)
open VerifiableInference.Desc.First (linkPlaces flatPlacesOf)

theorem linkPlaces_att3 (g : ℕ) :
    (linkPlaces (2 * g + 1) .attention)[3]? = some ⟨1, some (2 * g + 1), 3, .K5⟩ := by
  have h0 : ((2 * g + 1 == 0) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  unfold linkPlaces
  rw [h0]
  rfl

theorem linkPlaces_att4 (g : ℕ) :
    (linkPlaces (2 * g + 1) .attention)[4]? = some ⟨1, some (2 * g + 1), 4, .K1⟩ := by
  have h0 : ((2 * g + 1 == 0) = false) := by
    rw [beq_eq_false_iff_ne]
    omega
  unfold linkPlaces
  rw [h0]
  rfl

/-- **ONE NUMBER k.** -/
theorem K05_place_at {o : ProofFile.SecondHashFunctionArgument} {pol lay KL : ByteArray} {F : FileDescription ProofFile.Inst}
    {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block First.S Claim)}
    {c : Chain First.S Claim} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (O : IM.Open o pol lay KL F Z Bs base c A B) (h4 : Bs.G₀.W.p4 = true) {g : ℕ}
    (hg : g < Bs.G₀.W.NGr) :
    ∃ several : Bool, c.blocksInOrder.map (·.place) = flatPlacesOf (ProofFile.subsOf Z) several ∧
      (ProofFile.subsOf Z)[2 * g + 1]? = some .attention ∧
      (flatPlacesOf (ProofFile.subsOf Z) several)[IM.flatIx c (2 * g + 1) 2]? =
        some ⟨1, some (2 * g + 1), 3, .K5⟩ ∧
      (flatPlacesOf (ProofFile.subsOf Z) several)[IM.flatIx c (2 * g + 1) 2 + 1]? =
        some ⟨1, some (2 * g + 1), 4, .K1⟩ := by
  obtain ⟨X0, eX0, k0, -, -⟩ := built_att O.pub O.blank h4 hg
  have hsub : (ProofFile.subsOf Z)[2 * g + 1]? = some .attention := by
    rw [IM.subs_of_kind O.blank eX0, k0]
    rfl
  obtain ⟨Hb, several, h1⟩ := chainBy_first O.chain
  have hfp := VerifiableInference.Desc.First.flat_places Hb _ several c h1
  obtain ⟨-, hlk⟩ := IM.link_flat_places O.chain
  obtain ⟨Lk, eL, hp⟩ := hlk (2 * g + 1) .attention hsub
  have at_ : ∀ (j : ℕ) (p : Place), (linkPlaces (2 * g + 1) .attention)[j]? = some p →
      (flatPlacesOf (ProofFile.subsOf Z) several)[(1 + c.front.length) +
              (((c.links.take (2 * g + 1)).flatMap Link.blocksInOrder).length + j)]? = some p := by
    intro j p hj
    rw [← hp, List.getElem?_map] at hj
    obtain ⟨bj, hbj, rfl⟩ := Option.map_eq_some_iff.1 hj
    rw [← hfp, List.getElem?_map, IM.link_at_flat eL hbj]
    rfl
  have e3 : IM.flatIx c (2 * g + 1) 2 = (1 + c.front.length) +
      (((c.links.take (2 * g + 1)).flatMap Link.blocksInOrder).length + 3) := by
    unfold IM.flatIx
    omega
  refine ⟨several, hfp, hsub, ?_, ?_⟩
  · rw [e3]
    exact at_ 3 _ (linkPlaces_att3 g)
  · rw [e3, show (1 + c.front.length) +
        (((c.links.take (2 * g + 1)).flatMap Link.blocksInOrder).length + 3) + 1 = (1 + c.front.length) +
        (((c.links.take (2 * g + 1)).flatMap Link.blocksInOrder).length + 4) by omega]
    exact at_ 4 _ (linkPlaces_att4 g)

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.linkPlaces_att3
#print axioms VerifiableInference.Desc.First.Att.P.linkPlaces_att4
#print axioms VerifiableInference.Desc.First.Att.P.K05_place_at
