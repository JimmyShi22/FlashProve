-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Law/KindPlaces.lean: where the driver's table of places has a place of the
kind K10, and where one of the kind K12. Theorems only; no file of the description imports this
one. It imports the driver's Chain.lean alone and is general in the list of the segments' sorts.
  `kind_of_addresses`   a place of `addresses link ks` has a kind of the list `ks`
  `mem_closeAddresses`  the three places of a segment's closing, written out
  `k10_of_linkPlaces`   in one segment's places the only one of the kind K10 is the closing's second
  `k10_places`          in `flatPlacesOf links several` a place of the kind K10 is the second place
                        of the closing of a segment `l`, whose sort is `links[l]`
  `k12_places`          a place of the kind K12 there is the second place after the last segment
  `flatPlaces_nodup`    no place stands twice in that table

-/
import Johnson.Desc.First.Driver.Chain

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Law
open VerifiableInference.Desc (KindName Place)
open VerifiableInference.Desc.First

theorem kind_of_addresses {link : Option Nat} {ks : List KindName} {a : Place}
    (h : a ∈ addresses link ks) : a.kind ∈ ks := by
  unfold addresses at h
  obtain ⟨⟨k, j⟩, hx, rfl⟩ := List.mem_map.1 h
  exact List.mem_of_getElem? (List.mem_zipIdx_iff_getElem?.1 hx)

theorem no_k10_hear (sub : ModelPart) (first : Bool) : KindName.K10 ∉ kindsBeforeBatching sub first := by
  cases sub <;> cases first <;> decide

theorem no_k10_back (several : Bool) : KindName.K10 ∉ backKinds several := by
  cases several <;> decide

theorem mem_closeAddresses {l n : Nat} {a : Place} (h : a ∈ closeAddresses l n) :
    a = { chain := 1, link := some l, piece := n + 3 + 0, kind := .K9 } ∨
      a = { chain := 1, link := some l, piece := n + 3 + 1, kind := .K10 } ∨
      a = { chain := 1, link := some l, piece := n + 3 + 2, kind := .K9 } := by
  have e : closeAddresses l n =
      [{ chain := 1, link := some l, piece := n + 3 + 0, kind := .K9 },
       { chain := 1, link := some l, piece := n + 3 + 1, kind := .K10 },
       { chain := 1, link := some l, piece := n + 3 + 2, kind := .K9 }] := rfl
  rw [e] at h
  rcases List.mem_cons.1 h with h | h
  · exact .inl h
  · rcases List.mem_cons.1 h with h | h
    · exact .inr (.inl h)
    · exact .inr (.inr (List.mem_singleton.1 h))

theorem k10_of_linkPlaces {l : Nat} {sub : ModelPart} {a : Place} (h : a ∈ linkPlaces l sub)
    (hk : a.kind = KindName.K10) :
    a = { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 3 + 1,
          kind := .K10 } := by
  unfold linkPlaces at h
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | h) | (rfl | rfl)) | h) | rfl
  · simp [frameAt] at hk
  · exact (no_k10_hear sub (l == 0) (hk ▸ kind_of_addresses h)).elim
  · simp at hk
  · simp [frameAt] at hk
  · rcases mem_closeAddresses h with rfl | rfl | rfl
    · simp at hk
    · rfl
    · simp at hk
  · simp [frameAt] at hk

/-- A place of the kind K10 in the driver's table of all places of the first chain: it is the second
place of the closing of a segment `l` of the list, of that segment's sort. -/
theorem k10_places (links : List ModelPart) (several : Bool) (i : Nat) (a : Place)
    (h : (flatPlacesOf links several)[i]? = some a) (hk : a.kind = KindName.K10) :
    ∃ l sub, links[l]? = some sub ∧
      a = { chain := 1, link := some l, piece := (kindsBeforeBatching sub (l == 0)).length + 3 + 1,
            kind := .K10 } := by
  have hm := List.mem_of_getElem? h
  unfold flatPlacesOf at hm
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    or_false] at hm
  rcases hm with ((rfl | ⟨x, hx, hl⟩) | hb) | rfl
  · simp [frameAt] at hk
  · exact ⟨x.2, x.1, List.mem_zipIdx_iff_getElem?.1 hx, k10_of_linkPlaces hl hk⟩
  · exact (no_k10_back several (hk ▸ kind_of_addresses hb)).elim
  · simp [frameAt] at hk

/-! ### The kind K12 -/

theorem mem_addresses {link : Option Nat} {ks : List KindName} {a : Place}
    (h : a ∈ addresses link ks) :
    ∃ j k, ks[j]? = some k ∧ a = { chain := 1, link := link, piece := j + 1, kind := k } := by
  unfold addresses at h
  obtain ⟨⟨k, j⟩, hx, rfl⟩ := List.mem_map.1 h
  exact ⟨j, k, List.mem_zipIdx_iff_getElem?.1 hx, rfl⟩

theorem no_k12_hear (sub : ModelPart) (first : Bool) : KindName.K12 ∉ kindsBeforeBatching sub first := by
  cases sub <;> cases first <;> decide

theorem back_k12 {several : Bool} {j : Nat} (h : (backKinds several)[j]? = some KindName.K12) :
    j = 1 := by
  cases several <;> rcases j with _ | _ | _ | _ | j <;> simp [backKinds] at h ⊢

theorem no_k12_linkPlaces {l : Nat} {sub : ModelPart} {a : Place} (h : a ∈ linkPlaces l sub) :
    a.kind ≠ KindName.K12 := by
  intro hk
  unfold linkPlaces at h
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | h) | (rfl | rfl)) | h) | rfl
  · simp [frameAt] at hk
  · exact no_k12_hear sub (l == 0) (hk ▸ kind_of_addresses h)
  · simp at hk
  · simp [frameAt] at hk
  · rcases mem_closeAddresses h with rfl | rfl | rfl <;> simp at hk
  · simp [frameAt] at hk

/-- A place of the kind K12 in the driver's table of all places of the first chain: it is the second
place after the last segment. -/
theorem k12_places (links : List ModelPart) (several : Bool) (i : Nat) (a : Place)
    (h : (flatPlacesOf links several)[i]? = some a) (hk : a.kind = KindName.K12) :
    a = { chain := 1, link := none, piece := 2, kind := .K12 } := by
  have hm := List.mem_of_getElem? h
  unfold flatPlacesOf at hm
  simp only [List.mem_cons, List.mem_append, List.mem_flatMap, List.not_mem_nil,
    or_false] at hm
  rcases hm with ((rfl | ⟨x, _, hl⟩) | hb) | rfl
  · simp [frameAt] at hk
  · exact (no_k12_linkPlaces hl hk).elim
  · obtain ⟨j, k, hj, rfl⟩ := mem_addresses hb
    have hk' : k = KindName.K12 := hk
    subst hk'
    rw [back_k12 hj]
  · simp [frameAt] at hk

/-! ### No place stands twice in the table -/

theorem zipIdx_ge {α : Type} : ∀ (l : List α) (n : Nat) (x : α × Nat), x ∈ l.zipIdx n → n ≤ x.2
  | [], _, _, h => by simp at h
  | _ :: l, n, x, h => by
    rw [List.zipIdx_cons] at h
    rcases List.mem_cons.1 h with rfl | h
    · exact Nat.le_refl _
    · exact Nat.le_of_succ_le (zipIdx_ge l (n + 1) x h)

theorem addressesFrom_nodup (link : Option Nat) : ∀ (ks : List KindName) (n : Nat),
    ((ks.zipIdx n).map fun x =>
      ({ chain := 1, link := link, piece := x.2 + 1, kind := x.1 } : Place)).Nodup
  | [], _ => by simp
  | _ :: ks, n => by
    rw [List.zipIdx_cons, List.map_cons]
    refine List.pairwise_cons.2 ⟨fun b hb e => ?_, addressesFrom_nodup link ks (n + 1)⟩
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hb
    have h3 := zipIdx_ge ks (n + 1) x hx
    have h4 : n + 1 = x.2 + 1 := congrArg Place.piece e
    omega

theorem addresses_nodup (link : Option Nat) (ks : List KindName) : (addresses link ks).Nodup :=
  addressesFrom_nodup link ks 0

/-- The pieces of one segment's places count from 0, without a gap. -/
theorem linkPlaces_pieces (l : Nat) (sub : ModelPart) :
    (linkPlaces l sub).map (·.piece) = List.range ((kindsBeforeBatching sub (l == 0)).length + 7) := by
  unfold linkPlaces
  generalize (l == 0) = f
  cases sub <;> cases f <;> rfl

theorem linkPlaces_nodup (l : Nat) (sub : ModelPart) : (linkPlaces l sub).Nodup := by
  have h : ((linkPlaces l sub).map (·.piece)).Nodup := by
    rw [linkPlaces_pieces]
    exact List.nodup_range
  exact (List.pairwise_map.1 h).imp fun hab e => hab (congrArg Place.piece e)

theorem link_of_linkPlaces {l : Nat} {sub : ModelPart} {a : Place} (h : a ∈ linkPlaces l sub) :
    a.link = some l := by
  unfold linkPlaces at h
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at h
  rcases h with (((rfl | h) | (rfl | rfl)) | h) | rfl
  · rfl
  · obtain ⟨_, _, _, rfl⟩ := mem_addresses h
    rfl
  · rfl
  · rfl
  · rcases mem_closeAddresses h with rfl | rfl | rfl <;> rfl
  · rfl

theorem linksFrom_nodup : ∀ (links : List ModelPart) (n : Nat),
    ((links.zipIdx n).flatMap fun x => linkPlaces x.2 x.1).Nodup
  | [], _ => by simp
  | s :: links, n => by
    rw [List.zipIdx_cons, List.flatMap_cons]
    refine List.pairwise_append.2 ⟨linkPlaces_nodup n s, linksFrom_nodup links (n + 1),
      fun a ha b hb e => ?_⟩
    obtain ⟨x, hx, hbx⟩ := List.mem_flatMap.1 hb
    have h1 : a.link = some n := link_of_linkPlaces ha
    have h2 : b.link = some x.2 := link_of_linkPlaces hbx
    have h3 := zipIdx_ge links (n + 1) x hx
    rw [e, h2] at h1
    have h4 : x.2 = n := Option.some.inj h1
    omega

/-- **No place stands twice in the driver's table of the first chain's places.** -/
theorem flatPlaces_nodup (links : List ModelPart) (several : Bool) :
    (flatPlacesOf links several).Nodup := by
  unfold flatPlacesOf
  have inLink : ∀ a ∈ (links.zipIdx.flatMap fun x => linkPlaces x.2 x.1), a.link ≠ none := by
    intro a ha e
    obtain ⟨x, _, hx⟩ := List.mem_flatMap.1 ha
    rw [link_of_linkPlaces hx] at e
    cases e
  have inBack : ∀ b ∈ addresses none (backKinds several),
      b.link = none ∧ 1 ≤ b.piece ∧ b.piece ≤ (backKinds several).length := by
    intro b hb
    obtain ⟨j, k, hj, rfl⟩ := mem_addresses hb
    obtain ⟨hlt, _⟩ := List.getElem?_eq_some_iff.1 hj
    exact ⟨rfl, Nat.succ_le_succ (Nat.zero_le j), hlt⟩
  refine List.pairwise_append.2 ⟨List.pairwise_append.2 ⟨List.pairwise_cons.2
    ⟨fun a ha e => inLink a ha (e ▸ rfl), linksFrom_nodup links 0⟩,
    addresses_nodup none _, fun a ha b hb e => ?_⟩, List.pairwise_singleton _ _,
    fun a ha b hb e => ?_⟩
  · obtain ⟨hl, h1, _⟩ := inBack b hb
    rcases List.mem_cons.1 ha with rfl | ha
    · rw [← e] at h1
      exact absurd h1 (by simp [frameAt])
    · exact inLink a ha (e ▸ hl)
  · rw [List.mem_singleton.1 hb] at e
    rcases List.mem_append.1 ha with ha | ha
    · rcases List.mem_cons.1 ha with rfl | ha
      · have h4 : 0 = (backKinds several).length + 1 := congrArg Place.piece e
        omega
      · exact inLink a ha (e ▸ rfl)
    · obtain ⟨_, _, h2⟩ := inBack a ha
      have h4 : a.piece = (backKinds several).length + 1 := congrArg Place.piece e
      omega

end ProofFile.Law

#print axioms ProofFile.Law.flatPlaces_nodup
#print axioms ProofFile.Law.k12_places
#print axioms ProofFile.Law.k10_of_linkPlaces
#print axioms ProofFile.Law.k10_places
