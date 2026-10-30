-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Coverage.lean: the kind "lookup" (K3): at which addresses of
the lookups' lot a site is made, and where the halves of the lot's honest side stand. At every
public part: no hypothesis. Theorems; no definition.

Terms. Honest/K3/GLOSSARY.md ("site", "lot", "half", "place"). `lookSites`, `lookMisses`, `siteAt`,
`lotBy`, `lotTests`: Honest/K3/Lot.lean. `K3Lot.addresses`: Johnson/Desc/ProofFile/Lot/K3.lean.
`twice`: Honest/Frame.lean.

Why. `lookSites` and `lookMisses` are two `filterMap`s over one list, with two texts; nothing tied
them. An address at which no site can be made falls out of `lookSites` without a word.

What is shown.
  `filterMap_split`, `filterMap_nil_iff`: two facts on `filterMap`, free of any kind.
  `misses_by`: the function under `lookMisses` returns nothing just where `siteAt` makes a site.
    That function has no name, so it is bound by "there is"; its own text is the witness.
  `sites_add_misses`: **each address is a site or a miss, never both**: the two lists are together
    as long as the lot's list.
  `lookMisses_nil_iff`: **no miss just where a site is made at every address.**
  `addresses_length`: two addresses a link. `lookMisses_nil_iff_length`: no miss just where there
    are twice as many sites as links.
  `no_table_no_site`: where the table of places is not made there is no site. `table_of_no_miss`: no
    miss and a link: the table is made.
  `lotBy_places`: the halves of `lotBy` stand at the sites' places, in order (`lotTests`' fifth
    clause at `lotBy`).
  `addresses_nodup`, `sites_nodup`, `lotBy_places_nodup`: **no place bears two addresses, two sites
    or two halves.** `at_place_le_one`, `twice_nil`, `lotBy_twice`: the last as `lotTests`' own
    seventh clause.
  `rowLot_is`, `lotBySeat_is`: `rowLot` (Honest/K3/LotRow.lean) and `lotBySeat` are a `lotBy`, by
    their texts. `lookLot_is`, `lookLotFast_is`: these two are `rowLot` at their letters.

Kin. `addresses_nodup` and `sites_nodup` are the statements of this folder's `address_places_once`
and `site_places_once` (Honest/K3/Law/Thread/SitesOnce.lean), and `pairs_nodup` and
`filterMap_sublist` those of its `pairs_once` and `filterMap_map_sublist`, with their proofs: typed
anew under other names, so that this file stands over fewer files.

Limits. "No miss" alone is void where there is no link: see `void_no_miss`
(Honest/K3/Law/CoverageTooth.lean [not in this library]). It speaks of the lot's own list of
addresses, not of a description's sub-protocols: that tie is made, under a hypothesis, in
Honest/K3/Law/Thread/CoverageAtHead.lean. That a half stands at a place: nothing on what it sends.
Nothing on the lots that drop halves (`theLotFit` and its like).
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.LotRow
import Johnson.Desc.ProofFile.Honest.K3.LotLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (pieceAt)

/-! ## 1 Two facts on `filterMap` -/

/-- Where g returns nothing just where f returns something, the two filtered lists are together as
long as the list. -/
theorem filterMap_split {α β γ : Type} (f : α → Option β) (g : α → Option γ)
    (h : ∀ a, g a = none ↔ (f a).isSome = true) :
    ∀ l : List α, (l.filterMap f).length + (l.filterMap g).length = l.length
  | [] => rfl
  | a :: l => by
    have ih := filterMap_split f g h l
    cases ef : f a with
    | some b =>
      have eg : g a = none := (h a).2 (by rw [ef]; rfl)
      rw [List.filterMap_cons_some ef, List.filterMap_cons_none eg, List.length_cons,
        List.length_cons]
      omega
    | none =>
      cases eg : g a with
      | none =>
        have k := (h a).1 eg
        rw [ef] at k
        exact Bool.noConfusion k
      | some c =>
        rw [List.filterMap_cons_none ef, List.filterMap_cons_some eg, List.length_cons,
          List.length_cons]
        omega

/-- The filtered list is empty just where g returns nothing at every member. -/
theorem filterMap_nil_iff {α γ : Type} (g : α → Option γ) :
    ∀ l : List α, l.filterMap g = [] ↔ ∀ a ∈ l, g a = none
  | [] => by simp
  | a :: l => by
    have ih := filterMap_nil_iff g l
    cases eg : g a with
    | none =>
      rw [List.filterMap_cons_none eg, ih]
      constructor
      · intro k b hb
        rcases List.mem_cons.1 hb with rfl | hb
        · exact eg
        · exact k b hb
      · intro k b hb
        exact k b (List.mem_cons_of_mem _ hb)
    | some c =>
      rw [List.filterMap_cons_some eg]
      constructor
      · intro k
        exact absurd k (List.cons_ne_nil _ _)
      · intro k
        have := k a List.mem_cons_self
        rw [eg] at this
        exact absurd this (by simp)

/-! ## 2 A site or a miss -/

/-- **The function under `lookMisses` returns nothing just where a site is made.** -/
theorem misses_by (Z : Pub) : ∃ g : Nat × Bool × Place → Option String,
    lookMisses Z = (K3Lot.addresses Z).filterMap g ∧
      ∀ x, g x = none ↔ (siteAt Z.p.X ((spotsOf Z.cuts).getD []) x).isSome = true := by
  refine ⟨_, rfl, fun x => ?_⟩
  unfold siteAt
  cases hp : VerifiableInference.Desc.First.Look.placeAt Z.p.X x.1 x.2.1 with
  | none => simp
  | some p =>
    cases hh : p.shape with
    | none => simp [hh]
    | some sh =>
      cases hn : baseIn ((spotsOf Z.cuts).getD []) x.2.2 with
      | none => simp [hh]
      | some n =>
        cases hd : x.2.1 with
        | false => simp [hh]
        | true =>
          cases hr : rngIn ((spotsOf Z.cuts).getD []) x.1 with
          | none => simp [hh]
          | some r => simp [hh]

/-- **Each address is a site or a miss, never both.** -/
theorem sites_add_misses (Z : Pub) :
    (lookSites Z).length + (lookMisses Z).length = (K3Lot.addresses Z).length := by
  obtain ⟨g, e, hg⟩ := misses_by Z
  rw [e]
  exact filterMap_split _ g hg _

/-- **No miss just where a site is made at every address.** -/
theorem lookMisses_nil_iff (Z : Pub) : lookMisses Z = [] ↔
    ∀ x ∈ K3Lot.addresses Z, (siteAt Z.p.X ((spotsOf Z.cuts).getD []) x).isSome = true := by
  obtain ⟨g, e, hg⟩ := misses_by Z
  rw [e, filterMap_nil_iff]
  exact ⟨fun k x hx => (hg x).1 (k x hx), fun k x hx => (hg x).2 (k x hx)⟩

/-- Two addresses a link. -/
theorem addresses_length (Z : Pub) :
    (K3Lot.addresses Z).length = 2 * Z.first.shape.link.length := by
  unfold K3Lot.addresses
  generalize Z.first.shape.link.length = n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.length_append, ih]
    simp
    omega

/-- No miss just where there are twice as many sites as links. -/
theorem lookMisses_nil_iff_length (Z : Pub) :
    lookMisses Z = [] ↔ (lookSites Z).length = 2 * Z.first.shape.link.length := by
  have h1 := sites_add_misses Z
  rw [addresses_length] at h1
  constructor
  · intro e
    rw [e] at h1
    simpa using h1
  · intro e
    exact List.eq_nil_of_length_eq_zero (by omega)

/-! ## 3 The table of places -/

/-- Where the table of places is not made there is no site. -/
theorem no_table_no_site (Z : Pub) (h : spotsOf Z.cuts = none) : lookSites Z = [] := by
  unfold lookSites
  rw [h]
  refine (filterMap_nil_iff _ _).2 fun x _ => ?_
  unfold siteAt
  have hb : baseIn ((none : Option (List Spot)).getD []) x.2.2 = none := rfl
  rw [hb]
  simp

/-- No miss and a link: the table of places is made. -/
theorem table_of_no_miss (Z : Pub) (hm : lookMisses Z = [])
    (hl : Z.first.shape.link.length ≠ 0) : (spotsOf Z.cuts).isSome = true := by
  cases h : spotsOf Z.cuts with
  | some ps => rfl
  | none =>
    have e := (lookMisses_nil_iff_length Z).1 hm
    rw [no_table_no_site Z h] at e
    have e' : 0 = 2 * Z.first.shape.link.length := e
    exact absurd e' (by omega)

/-! ## 4 Where the halves stand -/

section
variable {V W X : Type}

/-- The halves of `lotBy` stand at the sites' places, in order. -/
theorem lotBy_places (row : Site → List (Part V W X)) (Z : Pub) (G : Ground) :
    ((lotBy row).halves Z G).map (·.place) = (lookSites Z).map (·.at_.place) := by
  show ((lookSites Z).map fun s => (⟨s.at_.place, row s⟩ : Placed V W X)).map (·.place) = _
  rw [List.map_map]
  rfl

end

/-- A list of pairs, one pair for each number, has no member twice where the two families are
injective and never meet. -/
theorem pairs_nodup {α : Type} (F G : Nat → α) (hF : ∀ m n, F m = F n → m = n)
    (hG : ∀ m n, G m = G n → m = n) (hFG : ∀ m n, F m ≠ G n) (v : Nat) :
    ((List.range v).flatMap fun m => [F m, G m]).Nodup := by
  induction v with
  | zero => simp
  | succ v ih =>
    rw [List.range_succ, List.flatMap_append]
    refine List.Nodup.append ih ?_ ?_
    · simp [hFG]
    · intro a ha hb
      obtain ⟨m, hm, h1⟩ := List.mem_flatMap.1 ha
      have hm' : m < v := List.mem_range.1 hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at h1
      simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hb
      rcases h1 with rfl | rfl <;> rcases hb with hb | hb
      · have := hF _ _ hb; omega
      · exact hFG _ _ hb
      · exact hFG _ _ hb.symm
      · have := hG _ _ hb; omega

/-- Where g of what f makes is k of what it was made of, the g's of the list that f filters are a
sublist of the k's. -/
theorem filterMap_sublist {α β γ : Type} (f : α → Option β) (g : β → γ) (k : α → γ)
    (h : ∀ a b, f a = some b → g b = k a) :
    ∀ l : List α, ((l.filterMap f).map g).Sublist (l.map k)
  | [] => List.Sublist.slnil
  | a :: l => by
    cases e : f a with
    | none =>
      rw [List.filterMap_cons_none e, List.map_cons]
      exact (filterMap_sublist f g k h l).cons _
    | some b =>
      rw [List.filterMap_cons_some e, List.map_cons, List.map_cons, h a b e]
      exact (filterMap_sublist f g k h l).cons₂ _

/-- No place bears two addresses of the lot's list. -/
theorem addresses_nodup (Z : Pub) : ((K3Lot.addresses Z).map (·.2.2)).Nodup := by
  have e : (K3Lot.addresses Z).map (·.2.2) =
      (List.range Z.first.shape.link.length).flatMap fun i =>
        [(⟨1, some i, pieceAt Z.p.X i false, .K3⟩ : Place),
          (⟨1, some i, pieceAt Z.p.X i true, .K3⟩ : Place)] := by
    unfold K3Lot.addresses
    rw [List.map_flatMap]
    rfl
  rw [e]
  refine pairs_nodup _ _ ?_ ?_ ?_ _
  · intro m n h
    exact Option.some.inj (congrArg Place.link h)
  · intro m n h
    exact Option.some.inj (congrArg Place.link h)
  · intro m n h
    have e1 : m = n := Option.some.inj (congrArg Place.link h)
    subst e1
    exact Bool.noConfusion (pieceAt_inj Z.p.X m false true (congrArg Place.piece h))

/-- No place bears two sites. -/
theorem sites_nodup (Z : Pub) : ((lookSites Z).map (·.at_.place)).Nodup := by
  unfold lookSites
  exact (filterMap_sublist _ _ (·.2.2)
    (fun y s hy => (site_facts _ _ y s hy).2.2.2.2.1) _).nodup (addresses_nodup Z)

section
variable {V W X : Type}

/-- **No place bears two halves of `lotBy`.** -/
theorem lotBy_places_nodup (row : Site → List (Part V W X)) (Z : Pub) (G : Ground) :
    (((lotBy row).halves Z G).map (·.place)).Nodup := by
  rw [lotBy_places]
  exact sites_nodup Z

/-- Where no place stands twice among the halves' places, at most one half stands at a place. -/
theorem at_place_le_one (a : Place) : ∀ hs : List (Placed V W X), (hs.map (·.place)).Nodup →
    (hs.filter fun g => g.place == a).length ≤ 1
  | [], _ => Nat.zero_le _
  | g :: hs, h => by
    have hn : g.place ∉ hs.map (·.place) ∧ (hs.map (·.place)).Nodup := List.nodup_cons.1 h
    by_cases e : (g.place == a) = true
    · have e0 : (hs.filter fun g' => g'.place == a) = [] :=
        List.filter_eq_nil_iff.2 fun g' hg' e' => hn.1 (by
          rw [eq_of_beq e, ← eq_of_beq e']
          exact List.mem_map.2 ⟨g', hg', rfl⟩)
      rw [List.filter_cons_of_pos (p := fun g' : Placed V W X => g'.place == a) e, e0]
      exact Nat.le_refl 1
    · rw [List.filter_cons_of_neg (p := fun g' : Placed V W X => g'.place == a) e]
      exact at_place_le_one a hs hn.2

/-- Where no place stands twice among the halves' places, `twice` is empty. -/
theorem twice_nil {hs : List (Placed V W X)} (h : (hs.map (·.place)).Nodup) : twice hs = [] :=
  (congrArg List.eraseDups (List.filter_eq_nil_iff.2 fun a _ k =>
    absurd (of_decide_eq_true k) (Nat.not_lt.2 (at_place_le_one a hs h)))).trans rfl

/-- The same as `lotTests`' own seventh clause. -/
theorem lotBy_twice (row : Site → List (Part V W X)) (Z : Pub) (G : Ground) :
    (twice ((lotBy row).halves Z G)).isEmpty = true := by
  rw [twice_nil (lotBy_places_nodup row Z G)]
  rfl

/-! ## 5 A lot that is a `lotBy` -/

/-- `rowLot` is a `lotBy`, by its text. -/
theorem rowLot_is (A : Fill W) : (rowLot A : HLot V W X) =
    lotBy fun s => (proverSideOfLookupInChainAtOneOwner theReads (A.jobs s).asked (A.wit s) s.at_).parts :=
  rfl

/-- `lotBySeat` is a `lotBy`, by its text. -/
theorem lotBySeat_is {W' : Type} (row : Site → List (Part W' W' Unit)) (wit : Site → W → W') :
    (lotBySeat row wit : HLot W W X) = lotBy fun s => seatRow (wit s) (row s) :=
  rfl

end

section
variable {W₀ Rc Xi Tr X : Type}

/-- `lookLot` is `rowLot` at the specification's letters, by its text. -/
theorem lookLot_is (src : Sources W₀ Xi Tr) :
    (lookLot src : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) = rowLot (specFill src) :=
  rfl

/-- `lookLotFast` is `rowLot` at the fast letters, by its text. -/
theorem lookLotFast_is (src : Sources W₀ Xi Tr) :
    (lookLotFast src : HLot (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) = rowLot (fastFill src) :=
  rfl

end

end ProofFile.Honest.K3.Law

#print axioms ProofFile.Honest.K3.Law.filterMap_split
#print axioms ProofFile.Honest.K3.Law.filterMap_nil_iff
#print axioms ProofFile.Honest.K3.Law.misses_by
#print axioms ProofFile.Honest.K3.Law.sites_add_misses
#print axioms ProofFile.Honest.K3.Law.lookMisses_nil_iff
#print axioms ProofFile.Honest.K3.Law.addresses_length
#print axioms ProofFile.Honest.K3.Law.lookMisses_nil_iff_length
#print axioms ProofFile.Honest.K3.Law.no_table_no_site
#print axioms ProofFile.Honest.K3.Law.table_of_no_miss
#print axioms ProofFile.Honest.K3.Law.lotBy_places
#print axioms ProofFile.Honest.K3.Law.pairs_nodup
#print axioms ProofFile.Honest.K3.Law.filterMap_sublist
#print axioms ProofFile.Honest.K3.Law.addresses_nodup
#print axioms ProofFile.Honest.K3.Law.sites_nodup
#print axioms ProofFile.Honest.K3.Law.lotBy_places_nodup
#print axioms ProofFile.Honest.K3.Law.at_place_le_one
#print axioms ProofFile.Honest.K3.Law.twice_nil
#print axioms ProofFile.Honest.K3.Law.lotBy_twice
#print axioms ProofFile.Honest.K3.Law.rowLot_is
#print axioms ProofFile.Honest.K3.Law.lotBySeat_is
#print axioms ProofFile.Honest.K3.Law.lookLot_is
#print axioms ProofFile.Honest.K3.Law.lookLotFast_is
