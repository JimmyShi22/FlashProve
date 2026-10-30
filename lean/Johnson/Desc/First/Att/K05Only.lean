-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05Only.lean: kind K5: NO OTHER ENTRY: in a first chain that the driver
makes, whatever blocks the kinds supply, an entry of the flat list that bears the kind K5 is the
third hearing block of an attention segment.

Main names:
  `addresses_at`: member number i of the driver's list of places of a list of kinds.
  `hearKinds_k5`: among a segment's hearing kinds K5 stands at number 2 of an attention segment and
    nowhere else.
  `firstChain_k5_only`: **firstChain H links several = some c, E ∈ c.blocksInOrder, E.place.kind = .K5 ⊢
    there are l and Lk with links[l]? = some .attention, c.links[l]? = some Lk and Lk.hear[2]? =
    some E.**
It is K5's reading of the table of what the driver lays (Shape.firstChain_shape,
linkAt_shape: Johnson/Desc/First/Link/Law/Shape.lean; place_of_blockAt: Driver/PlacesLaw.lean). The
proximity test's files have the like for K12 (firstChain_only, Johnson/Desc/K12/Law/SitsOnly.lean).
Limits. A place is a label that the driver writes into a block: the law says at which number of
which segment the entry with the label K5 stands; it does not say what that entry's text is.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Link.Law.Shape
import Johnson.Desc.BlockLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open VerifiableInference.Desc (Block Chain Link Place KindName)
open VerifiableInference.Desc.First (ModelPart Blocks kindsBeforeBatching backKinds closeKinds closeAddresses
  addresses blockAt linkAt firstChain hearsReply frameAt kindOfModelPart place_of_blockAt)

/-- Member number i of the places of a list of kinds. -/
theorem addresses_at (link : Option Nat) (ks : List KindName) (i : Nat) :
    (addresses link ks)[i]? = (ks[i]?).map fun k => ⟨1, link, i + 1, k⟩ := by
  unfold addresses
  rw [List.getElem?_map, List.getElem?_zipIdx]
  cases ks[i]? <;> simp

/-- K5 among a segment's hearing kinds. -/
theorem hearKinds_k5 (sub : ModelPart) (first : Bool) (i : Nat)
    (h : (kindsBeforeBatching sub first)[i]? = some KindName.K5) : sub = .attention ∧ i = 2 := by
  cases sub <;> cases first <;>
    (rcases i with _ | _ | _ | _ | _ | _ | _ | _ | _ | i <;>
      simp [kindsBeforeBatching, kindOfModelPart] at h ⊢)

/-- **No other entry of the first chain bears the kind K5.** -/
theorem firstChain_k5_only {S Cl : Type} (H : Blocks S Cl) (links : List ModelPart) (several : Bool)
    (c : Chain S Cl) (h : firstChain H links several = some c) (E : Block S Cl) (hE : E ∈ c.blocksInOrder)
    (hK : E.place.kind = .K5) :
    ∃ (l : Nat) (Lk : Link S Cl), links[l]? = some ModelPart.attention ∧ c.links[l]? = some Lk ∧
      Lk.hear[2]? = some E := by
  obtain ⟨_, c0, ⟨hFirst, hFront, hLinks, hBack, hLast⟩, rfl⟩ := Shape.firstChain_shape h
  rw [Chain.flat_eq] at hE
  simp only [Chain.guarded, hFront, List.map_nil, List.mem_cons, List.mem_append,
    List.mem_flatMap, List.mem_map, List.not_mem_nil, or_false] at hE
  rcases hE with ((rfl | ⟨_, ⟨L, hL, rfl⟩, hE⟩) | ⟨_, ⟨b', hb', rfl⟩, rfl⟩) | rfl
  · rw [show (Block.asBare (Block.guarded H.same hearsReply c0.first)).place.kind =
      c0.first.place.kind from rfl, hFirst] at hK
    cases hK
  · -- a segment
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hL
    have hm : (c0.links.map some)[j]? = some (some L) := by rw [List.getElem?_map, hj]; rfl
    rw [hLinks, List.getElem?_map, List.getElem?_zipIdx] at hm
    obtain ⟨y, hy, e⟩ := Option.map_eq_some_iff.1 hm
    obtain ⟨sub, hsub, rfl⟩ := Option.map_eq_some_iff.1 hy
    have e' : linkAt H j sub = some L := by simpa using e
    obtain ⟨_, hHear, ⟨batch, _, hBatch⟩, hClose, _⟩ := Shape.linkAt_shape e'
    have hlk : (c0.links.map (Link.guarded H.same hearsReply))[j]? =
        some (L.guarded H.same hearsReply) := by rw [List.getElem?_map, hj]; rfl
    unfold Link.blocksInOrder at hE
    simp only [Link.guarded, List.mem_cons, List.mem_append, List.mem_map, List.not_mem_nil,
      or_false] at hE
    rcases hE with (((rfl | ⟨b0, hb0, rfl⟩) | (rfl | rfl)) | ⟨b0, hb0, rfl⟩) | rfl
    · cases hK
    · -- a hearing block
      obtain ⟨i, hi⟩ := List.getElem?_of_mem hb0
      have hm2 : (L.hear.map some)[i]? = some (some b0) := by rw [List.getElem?_map, hi]; rfl
      rw [hHear, List.getElem?_map, addresses_at] at hm2
      obtain ⟨a, ha, eb⟩ := Option.map_eq_some_iff.1 hm2
      obtain ⟨k, hk, rfl⟩ := Option.map_eq_some_iff.1 ha
      have hp := place_of_blockAt H _ b0 eb
      have hk5 : k = KindName.K5 := by
        have : (Block.guarded H.same hearsReply b0).place = b0.place := rfl
        rw [this, hp] at hK
        exact hK
      subst hk5
      obtain ⟨rfl, rfl⟩ := hearKinds_k5 sub _ i hk
      exact ⟨j, _, hsub, hlk, by
        show (L.hear.map (Block.guarded H.same hearsReply))[2]? = _
        rw [List.getElem?_map, hi]
        rfl⟩
    · -- the batching
      rw [hBatch] at hK
      cases hK
    · cases hK
    · -- the closing
      have hm3 : some b0 ∈ L.close.map some := List.mem_map.2 ⟨b0, hb0, rfl⟩
      rw [hClose] at hm3
      obtain ⟨a, ha, eb⟩ := List.mem_map.1 hm3
      have hp := place_of_blockAt H a b0 eb
      have : (Block.guarded H.same hearsReply b0).place = b0.place := rfl
      rw [this, hp] at hK
      unfold closeAddresses closeKinds at ha
      simp at ha
      rcases ha with rfl | rfl | rfl <;> cases hK
    · cases hK
  · have hm : some b' ∈ c0.back.map some := List.mem_map.2 ⟨b', hb', rfl⟩
    rw [hBack] at hm
    obtain ⟨a, ha, e⟩ := List.mem_map.1 hm
    have hp := place_of_blockAt H a b' e
    have hK' : a.kind = .K5 := hp ▸ hK
    have no5 : ∀ a ∈ addresses none (backKinds several), a.kind ≠ KindName.K5 := by
      cases several <;> decide
    exact absurd hK' (no5 a ha)
  · rw [show (Block.asBare (Block.guarded H.same hearsReply c0.last)).place.kind =
      c0.last.place.kind from rfl, hLast] at hK
    cases hK

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.addresses_at
#print axioms VerifiableInference.Desc.First.Att.P.hearKinds_k5
#print axioms VerifiableInference.Desc.First.Att.P.firstChain_k5_only
