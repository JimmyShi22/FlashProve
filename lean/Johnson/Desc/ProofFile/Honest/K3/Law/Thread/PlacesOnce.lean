-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/PlacesOnce.lean: conditional: "no two share a place",
the two hypotheses of Honest/K3/Law/Thread/SitePays.lean, from two tests that every run of the frame
has passed (`readyTests`, Honest/Frame.lean): no two halves stand at one place (`twice`, there); the
description's own test on its places (`FileDescription.placesOk`, Johnson/Desc/Block.lean). Theorems.

Terms. Honest/K3/GLOSSARY.md: see there half, lot, site, place, flat list and frame.

What is shown.
  `nodup_of_counts`: a list that holds each of its elements once has no element twice.
  `halves_once`: where the frame's list of places with two halves is empty, no two halves share a
    place.
  `flat_once`: where the description's test on its places accepts, no two sub-protocols of the first
    chain's flat list share a place.
  `base_site_ok`, `half_site_ok`: the two theorems `base_site_nodup` and `half_site` of
    SitePays.lean, from these two tests.

Hypotheses that remain.
  `h`, `ht`, `hok`: the acceptance of the two tests: tests with code on public data.
  `hf`, `hb`, `hp`: (in `base_site_ok`) `siteFits` (Honest/K3/Law/SiteFits.lean); blk is member
    number b of the first chain's flat list, at the site's place.
  `hl`, `hs`: (in `half_site_ok`) the lookups' lot stands in the list of lots; s is a site of the
    public part.

Imported: Honest/Frame.lean.

Users. Honest/K3/Law/Thread/HalfOfLot.lean calls `halves_once`;
Honest/K3/Law/Keep/Alike/AlikeLess.lean [not in this library] imports this file.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place placesOf)

/-- A list that holds each of its elements once has no element twice. Conditional on that. -/
theorem nodup_of_counts {α : Type} [BEq α] [LawfulBEq α] (l : List α) (h : ∀ a ∈ l, l.count a ≤ 1) :
    l.Nodup := by
  rw [List.nodup_iff_count_le_one]
  intro a
  by_cases ha : a ∈ l
  · exact h a ha
  · rw [List.count_eq_zero_of_not_mem ha]
    exact Nat.zero_le 1

section
variable {V W X : Type}

/-- **Where the frame's list of places with two halves is empty, no two halves share a place.**
Conditional on that test. -/
theorem halves_once (hs : List (Placed V W X)) (h : twice hs = []) : (hs.map (·.place)).Nodup := by
  unfold twice at h
  have hf : ((hs.map (·.place)).filter fun a => 1 < (hs.filter fun x => x.place == a).length) =
    [] := by
    cases hl : ((hs.map (·.place)).filter fun a =>
        decide (1 < (hs.filter fun x => x.place == a).length)) with
    | nil => rfl
    | cons a l =>
      rw [hl, List.eraseDups_cons] at h
      exact nomatch h
  refine nodup_of_counts _ fun a ha => ?_
  have e := List.filter_eq_nil_iff.1 hf a ha
  have hc : (hs.map (·.place)).count a = (hs.filter fun x => x.place == a).length := by
    rw [List.count_eq_length_filter, List.filter_map, List.length_map]
    rfl
  rw [hc]
  simpa using e

end

/-- **Where the description's test on its places accepts, no two sub-protocols of the first chain's
flat list share a place.** Conditional on that test. -/
theorem flat_once {Xi : Type} (F : FileDescription Xi) (h : F.placesOk = true) :
    (F.first.blocksInOrder.map (·.place)).Nodup := by
  unfold FileDescription.placesOk at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  have hall := h.2
  have hn : (F.places.map fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)).Nodup :=
    nodup_of_counts _ fun a ha => Nat.le_of_eq (hall a ha)
  unfold FileDescription.places at hn
  rw [List.map_append, List.map_append] at hn
  have h1 := (List.nodup_append.1 (List.nodup_append.1 hn).1).1
  unfold placesOf at h1
  rw [List.map_map] at h1
  have h2 : ((F.first.blocksInOrder.map (·.place)).map fun a : Place => (a.chain, a.link, a.piece)).Nodup :=
    by
    rw [List.map_map]
    exact h1
  exact h2.of_map _

/-- The theorem of Honest/K3/Law/Thread/SitePays.lean on the rounds in front, from the description's
own test. Conditional on `siteFits`; the member at number b of the first chain's flat list, at the
site's place; and `FileDescription.placesOk`. -/
theorem base_site_ok {Xi : Type} (F : FileDescription Xi) (s : Site) (b : Nat) (blk : Block _ _)
    (hf : siteFits F.first.blocksInOrder s = true) (hb : F.first.blocksInOrder[b]? = some blk)
    (hp : blk.place = s.at_.place) (hok : F.placesOk = true) :
    s.at_.base = roundsTo F.first.blocksInOrder b :=
  base_site_nodup _ s b blk hf hb hp (flat_once F hok)

/-- The theorem of Honest/K3/Law/Thread/SitePays.lean on the half at a site's place, from the
frame's own test. Conditional on the lookups' lot standing in the list of lots; the site; and the
frame's list of places with two halves being empty. -/
theorem half_site_ok {V W X : Type} (Z : Pub) (Gr : Ground) (ls : List (HLot V W X))
    (row : Site → List (Part V W X)) (hl : lotBy row ∈ ls) (s : Site) (hs : s ∈ lookSites Z)
    (ht : twice (firstOf Z Gr ls) = []) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) = some ⟨s.at_.place, row s⟩ :=
  half_site Z Gr ls row hl s hs (halves_once _ ht)

#print axioms ProofFile.Honest.K3.Law.AtThr.nodup_of_counts
#print axioms ProofFile.Honest.K3.Law.AtThr.halves_once
#print axioms ProofFile.Honest.K3.Law.AtThr.flat_once
#print axioms ProofFile.Honest.K3.Law.AtThr.base_site_ok
#print axioms ProofFile.Honest.K3.Law.AtThr.half_site_ok

end ProofFile.Honest.K3.Law.AtThr
