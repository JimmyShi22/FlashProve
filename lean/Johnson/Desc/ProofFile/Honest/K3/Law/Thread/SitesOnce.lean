-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SitesOnce.lean: no two sites of a public part share a
place; so the search at a site's place in the lookups' own lot's list of halves finds that site's
half. Theorems; no definition; in the theorems on sites no hypothesis but that the site stands in
the list (in `site_of_place` also: the two places are one).

Terms. Honest/K3/GLOSSARY.md. In this file: the lot is `theLot` (Honest/K3/LotFilled.lean); a site's
half is `seatAt` (Honest/K3/Law/Thread/HalfOfLot.lean).

What is shown.
  `pairs_once`, `filterMap_map_sublist`: two lemmas on lists.
  `address_places_once`: the places of the library's list of the lookups' addresses
    (`K3Lot.addresses`, Johnson/Desc/ProofFile/Lot/K3.lean) are pairwise different.
  `site_places_once`: so are the places of `lookSites Z`.
  `site_of_place`: two sites of `lookSites Z` at one place are one site.
  `theLot_places_once`: so are the places of the lot's halves at `Z`.
  `theLot_find`: the search at a site's place in the lot's own list of halves finds `seatAt` at that
    site.

Hypotheses that remain.
  `hs`, in `theLot_find`; `hs` and `ht`, in `site_of_place`: the site, or each of the two, stands in
    `lookSites Z`. `e`: (in `site_of_place`) the two places are one.
  `hF`, `hG`, `hFG`: (in `pairs_once`) F and G are injective, and no value of F is one of G. `h`:
    (in `filterMap_map_sublist`) where f returns b at a, g b is k a.

How the proof goes. An address's place names its link and its piece; a link's two lookups stand at
two pieces (`pieceAt_inj`, Honest/K3/LotLaw.lean). A site's place is that of the address at which it
was made (`site_facts`, Honest/K3/Law/MemberSite.lean): so the sites' places are a sublist of the
addresses'. `pairs_once` follows `pairs_nodup` (Honest/K3/RowAt.lean), which is stated of stages,
line by line. The last theorem is `find_once` (Honest/K3/Law/Thread/SitePays.lean) at `mem_theLot`
(Honest/K3/Law/Thread/HalfOfLot.lean).

Imported, through Honest/K3/Law/Thread/HalfOfLot.lean: the files directly under Honest/ and those
under Honest/Thread/, Honest/Law/, Honest/SumLaw/ and Honest/K8/.

Users. `theLot_find` is meant for the hypothesis `hg`, "what the lot's own list holds at the place",
of `firstOf_find_pairs` (Honest/FirstFindPairs.lean; not imported).
That the two forms fit has not been tried in Lean.
`site_of_place` is the statement "no two sites share a place" that
Honest/K3/Law/Thread/RidersAtPlace.lean names as not shown. Honest/K3/Law/Thread/LotInstFind.lean,
Honest/K3/Law/Keep/LotInstKeepLaw.lean [not in this library] and Honest/K3/Good/MarksHead.lean
import this file.

Limits. General in the public part: nothing is said on whether a site stands at any place. Which
summands and which reader of the input the half holds is `seatAt`'s text. On public data and the
lot's text alone.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HalfOfLot

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.K3 (pieceAt)

/-- A list of pairs, one pair for each number, has no member twice where the two families are
injective and never meet. -/
theorem pairs_once {α : Type} (F G : Nat → α) (hF : ∀ m n, F m = F n → m = n)
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
theorem filterMap_map_sublist {α β γ : Type} (f : α → Option β) (g : β → γ) (k : α → γ)
    (h : ∀ a b, f a = some b → g b = k a) :
    ∀ l : List α, ((l.filterMap f).map g).Sublist (l.map k)
  | [] => List.Sublist.slnil
  | a :: l => by
    cases e : f a with
    | none =>
      rw [List.filterMap_cons_none e, List.map_cons]
      exact (filterMap_map_sublist f g k h l).cons _
    | some b =>
      rw [List.filterMap_cons_some e, List.map_cons, List.map_cons, h a b e]
      exact (filterMap_map_sublist f g k h l).cons₂ _

/-- The places of the library's list of the lookups' addresses are pairwise different. -/
theorem address_places_once (Z : Pub) : ((K3Lot.addresses Z).map (·.2.2)).Nodup := by
  have e : (K3Lot.addresses Z).map (·.2.2) =
      (List.range Z.first.shape.link.length).flatMap fun i =>
        [(⟨1, some i, pieceAt Z.p.X i false, .K3⟩ : Place),
          (⟨1, some i, pieceAt Z.p.X i true, .K3⟩ : Place)] := by
    unfold K3Lot.addresses
    rw [List.map_flatMap]
    rfl
  rw [e]
  refine pairs_once _ _ ?_ ?_ ?_ _
  · intro m n h
    exact Option.some.inj (congrArg Place.link h)
  · intro m n h
    exact Option.some.inj (congrArg Place.link h)
  · intro m n h
    have e1 : m = n := Option.some.inj (congrArg Place.link h)
    subst e1
    exact Bool.noConfusion (pieceAt_inj Z.p.X m false true (congrArg Place.piece h))

/-- The places of the sites of a public part are pairwise different. -/
theorem site_places_once (Z : Pub) : ((lookSites Z).map (·.at_.place)).Nodup := by
  unfold lookSites
  exact (filterMap_map_sublist _ _ (·.2.2)
    (fun y s hy => (site_facts _ _ y s hy).2.2.2.2.1) _).nodup (address_places_once Z)

/-- Two sites of a public part at one place are one site. -/
theorem site_of_place (Z : Pub) (s t : Site) (hs : s ∈ lookSites Z) (ht : t ∈ lookSites Z)
    (e : s.at_.place = t.at_.place) : s = t :=
  List.inj_on_of_nodup_map (site_places_once Z) hs ht e

section
variable {W₀ Rc Xi Tr X : Type} (cells : Tr → Cells) (weights : W₀ → Weights)
  (req : Xi → OnBytes.Model.Head.Covered × Array Nat)

/-- The places of the lot's halves at a public part are pairwise different. -/
theorem theLot_places_once (Z : Pub) (Gr : Ground) :
    (((theLot (Rc := Rc) (X := X) cells weights req).halves Z Gr).map (·.place)).Nodup := by
  show (((lookSites Z).map fun s => seatAt (Rc := Rc) (X := X) cells weights req Z s).map
    (·.place)).Nodup
  rw [List.map_map]
  exact site_places_once Z

/-- The search at a site's place in the lot's own list of halves finds that site's half. Conditional
on the site standing in `lookSites Z`. -/
theorem theLot_find (Z : Pub) (Gr : Ground) (s : Site) (hs : s ∈ lookSites Z) :
    ((theLot (Rc := Rc) (X := X) cells weights req).halves Z Gr).find?
        (fun x => x.place == s.at_.place) = some (seatAt cells weights req Z s) :=
  find_once _ _ (mem_theLot cells weights req Z Gr s hs) (theLot_places_once cells weights req Z Gr)

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.pairs_once
#print axioms ProofFile.Honest.K3.Law.AtThr.filterMap_map_sublist
#print axioms ProofFile.Honest.K3.Law.AtThr.address_places_once
#print axioms ProofFile.Honest.K3.Law.AtThr.site_places_once
#print axioms ProofFile.Honest.K3.Law.AtThr.site_of_place
#print axioms ProofFile.Honest.K3.Law.AtThr.theLot_places_once
#print axioms ProofFile.Honest.K3.Law.AtThr.theLot_find
