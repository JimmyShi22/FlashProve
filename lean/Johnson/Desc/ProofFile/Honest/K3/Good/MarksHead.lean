-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Good/MarksHead.lean: of the list of the lookups' marks at a proof
file's first chain (`k3Marks`, Honest/K3/Good/MarksList.lean): that each member stands where a
kind's mark may stand; that no place bears more than two; that at the full size the list has 100
members, each at a place at which a sub-protocol of the chain stands; and the bound at each member,
conditional. Theorems, and one definition that a proof needs.

Terms. Honest/K3/GLOSSARY.md. In this file: a mark is a value of `ProofFile.Honest.Mark`
(Honest/Law/Marks.lean); a site is a lookup of a public part at its place
(`lookSites`, Honest/K3/Lot.lean); `markK3` and `markOut`: Honest/K3/Good/Mark.lean.

What is defined.
  `pairs50`: the fifty pairs of a link below 25 and a sort.

Why no `markRun` stands in the list. The one theorem of this folder that spends a run's test at a
whole lookup, `share_live` (Honest/K3/Good/AtBatch.lean [not in this library]), takes the whole test
`goodK3` and goes down to each run by
`goodRun_of` (Honest/K3/GoodDrawsLaw.lean): so where `markK3` is silent every run is served.

What is shown.
  `k3Marks_mem`: a member is `markK3` or `markOut` at a site's place and face.
  `k3Marks_kind`: every member's place has the kind K3. No hypothesis.
  `k3Marks_seat`: **every member's place passes `markSeat`** (Honest/Law/CoverSeats.lean):
    the frame's test on where a kind's mark of the first chain may stand. No
    hypothesis.
  `k3Marks_length`: the list has twice as many members as there are sites. No hypothesis.
  `count_twice`, `k3Marks_count`: **no place bears more than two members**: those of its one site.
    No hypothesis: no two sites of a public part share a place (`site_places_once`,
    Honest/K3/Law/Thread/SitesOnce.lean).
  `sites_fifty`: conditional on `P5J.AtMgA`: `lookSites Zp` has 50 members.
  `k3Marks_100`: **the list is not empty: conditional on `P5J.AtMgA`: it has 100 members**, at every
    G₀.
  `site_lt25`, `site_in_ps`: conditional on `P5J.AtMgA`: a site's link is below 25; its place stands
    in the written list of places `P5J.At.ps`. The first has the statement of `link_lt_head`
    (Honest/K3/Law/Thread/LinkLtHead.lean), by another proof; the second concludes what the field
    there of `SiteRest'` (Honest/K3/Law/Thread/LotAtSite.lean) asks as a test with code.
  `k3Marks_member`: **nor do its members stand at empty places: conditional on `P5J.AtMgA`: at every
    member's place a sub-protocol of the first chain cF stands**: by `P5J.At.places_paid`
    (Johnson/P5J/PlacesPaid.lean): under that hypothesis the chain's places are
    the written list.
  `k3Marks_debt`: **the bound at each member**, conditional on hS:
    `MarkDebt C mk dsb (fun _ => True) (mk.share.num * kap)`. Here hS says of every site at the
    member's place: `CanAll`, `FewAll` and `FewOut` (Honest/K3/Good/MarkShare.lean, MarkOut.lean)
    hold at the site's face, the kit C, the rounds' data dsb and the number kap. It asks all three
    at a member of either sort, though `markK3` spends the first two alone and `markOut` the first
    and the third.

Hypotheses that remain.
  `h`: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x` (Johnson/P5J/MgAtAll.lean): the library's
    hypothesis at the full size. In the first three theorems and in `k3Marks_debt` `h`, in
    `k3Marks_member` `hm`: mk is a member of the list. `hs`: s is a site of the public part.
  `hS`, in `k3Marks_debt`: not paid at the release's kit or at any real face by anybody; kap is a
    letter for the share of a round's challenges that show a given element.

Imported. Honest/K3/Good/MarksList.lean; Honest/K3/Good/MarkOut.lean; Honest/K3/Law/LotOfSite.lean,
for `spot_of_site`; Johnson/AtFull/Shape/SitesAtHead.lean, for `site_made_at`,
`reqShape_at` and `rng_at`; Honest/Law/CoverSeats.lean, for `markSeat`;
Honest/K3/Law/Thread/SitesOnce.lean; Honest/K3/Law/Thread/SiteThereHead.lean, for `site_there_head`,
`site_link_lt` and `site_place`; Johnson/P5J/PlacesPaid.lean.
The frame's files lie beneath them.

Users. Honest/K3/Good/MarksHeadGuards.lean [not in this library] imports this file. Meant for a list
of all kinds' marks.

Limits. `k3Marks_100` and `k3Marks_member` speak of the full size alone. No instance of `P5J.AtMgA`
is exhibited in this file.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Good.MarksList
import Johnson.Desc.ProofFile.Honest.K3.Good.MarkOut
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.AtFull.Shape.SitesAtHead
import Johnson.Desc.ProofFile.Honest.Law.CoverSeats
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitesOnce
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.P5J.PlacesPaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Good
open VerifiableInference.Desc (Chain KindName Place)
open scoped ENNReal
open OnBytes.Maker (RDT)
open _root_.Run.PQ (CK)

/-- A member is one of the two marks at a site. -/
theorem k3Marks_mem (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (mk : Mark) (h : mk ∈ k3Marks Zp G₀) :
    ∃ s ∈ lookSites Zp,
      mk = markK3 s.at_.place s.at_.face ∨ mk = markOut s.at_.place s.at_.face := by
  obtain ⟨s, hs, hm⟩ := List.mem_flatMap.1 h
  refine ⟨s, hs, ?_⟩
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hm

/-- **Every member's place has the kind K3.** -/
theorem k3Marks_kind (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (mk : Mark) (h : mk ∈ k3Marks Zp G₀) :
    mk.place.kind = KindName.K3 := by
  obtain ⟨s, hs, rfl | rfl⟩ := k3Marks_mem Zp G₀ mk h
  · exact (Law.spot_of_site Zp s hs).1
  · exact (Law.spot_of_site Zp s hs).1

/-- **Every member's place passes the frame's test on where a kind's mark may stand.** -/
theorem k3Marks_seat (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (mk : Mark) (h : mk ∈ k3Marks Zp G₀) :
    markSeat mk.place = true := by
  unfold markSeat
  rw [k3Marks_kind Zp G₀ mk h]
  rfl

/-- Two marks a site. -/
theorem k3Marks_length (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) :
    (k3Marks Zp G₀).length = 2 * (lookSites Zp).length := by
  unfold k3Marks
  induction lookSites Zp with
  | nil => rfl
  | cons s l ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    simp only [List.length_cons, List.length_nil]
    omega

/-- At a list of sites: a place is borne by twice as many marks as sites. -/
theorem count_twice (l : List Site) (a : Place) :
    ((l.flatMap fun s => [markK3 s.at_.place s.at_.face, markOut s.at_.place s.at_.face]).map
      (·.place)).count a = 2 * (l.map (·.at_.place)).count a := by
  induction l with
  | nil => rfl
  | cons s l ih =>
    have e : (((s :: l).flatMap fun s =>
        [markK3 s.at_.place s.at_.face, markOut s.at_.place s.at_.face]).map (·.place)) =
        s.at_.place :: s.at_.place :: ((l.flatMap fun s =>
          [markK3 s.at_.place s.at_.face, markOut s.at_.place s.at_.face]).map (·.place)) := by
      rw [List.flatMap_cons, List.map_append]
      rfl
    rw [e]
    simp only [List.map_cons, List.count_cons, ih]
    split <;> omega

/-- **No place bears more than the two marks of its one site.** No hypothesis: no two sites of a
public part share a place. -/
theorem k3Marks_count (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (a : Place) :
    ((k3Marks Zp G₀).map (·.place)).count a ≤ 2 := by
  unfold k3Marks
  rw [count_twice]
  have h := List.nodup_iff_count_le_one.1 (Law.AtThr.site_places_once Zp) a
  omega

section Head
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)
open Johnson.AtFull.Shape (site_made_at reqShape_at rng_at)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- The fifty pairs of a link below 25 and a sort. -/
def pairs50 : List (Nat × Bool) := (List.range 25).flatMap fun l => [(l, false), (l, true)]

theorem pairs50_nodup : pairs50.Nodup := by decide

theorem pairs50_length : pairs50.length = 50 := by decide

/-- **Conditional on `P5J.AtMgA`: there are fifty sites.** -/
theorem sites_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : (lookSites Zp).length = 50 := by
  apply Nat.le_antisymm
  · -- no more than the addresses
    have h1 : (lookSites Zp).length ≤ (K3Lot.addresses Zp).length := by
      unfold lookSites
      exact List.length_filterMap_le _ _
    have h2 : (K3Lot.addresses Zp).length = 50 := by
      unfold K3Lot.addresses
      rw [reqShape_at h]
      rfl
    omega
  · -- each of the fifty pairs is some site's
    have hsub : pairs50 ⊆ (lookSites Zp).map fun s => (s.link, s.digits) := by
      intro p hp
      obtain ⟨l, hl, hp⟩ := List.mem_flatMap.1 hp
      have hl' : l < 25 := List.mem_range.1 hl
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl
      · obtain ⟨s, hs, e1, e2⟩ := site_made_at h l hl' false
        exact List.mem_map.2 ⟨s, hs, by rw [e1, e2]⟩
      · obtain ⟨s, hs, e1, e2⟩ := site_made_at h l hl' true
        exact List.mem_map.2 ⟨s, hs, by rw [e1, e2]⟩
    have hle := (List.subperm_of_subset pairs50_nodup hsub).length_le
    rw [pairs50_length, List.length_map] at hle
    exact hle

/-- **The list is not empty. Conditional on `P5J.AtMgA`: it has 100 members.** -/
theorem k3Marks_100 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) :
    (k3Marks Zp G₀).length = 100 := by
  rw [k3Marks_length, sites_fifty h]

/-- Conditional on `P5J.AtMgA`: a site's link is below 25. -/
theorem site_lt25 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    s.link < 25 := by
  have h1 := Law.AtThr.site_link_lt Zp s hs
  rw [reqShape_at h] at h1
  exact h1

/-- Conditional on `P5J.AtMgA`: a site's place stands in the written list of places. -/
theorem site_in_ps (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    s.at_.place ∈ P5J.At.ps := by
  have hl := site_lt25 h s hs
  obtain ⟨s', hs', e1, e2, _, e4⟩ :=
    Law.AtThr.site_there_head h s.link hl s.digits fun _ => rng_at h s.link hl
  have a := Law.AtThr.site_place Zp s hs
  have b := Law.AtThr.site_place Zp s' hs'
  rw [e1, e2] at b
  rw [a, ← b]
  exact e4

/-- **Nor do its members stand at empty places. Conditional on `P5J.AtMgA`: at every member's place
a sub-protocol of the first chain stands.** -/
theorem k3Marks_member (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (G₀ : ProofFile.Ground) (mk : Mark)
    (hm : mk ∈ k3Marks Zp G₀) : ∃ b ∈ cF.blocksInOrder, b.place = mk.place := by
  have key : ∀ s ∈ lookSites Zp, ∃ b ∈ cF.blocksInOrder, b.place = s.at_.place := by
    intro s hs
    have hp := site_in_ps h s hs
    rw [← P5J.At.places_paid h.scope h.reads h.laid] at hp
    exact List.mem_map.1 hp
  obtain ⟨s, hs, rfl | rfl⟩ := k3Marks_mem Zp G₀ mk hm
  · exact key s hs
  · exact key s hs

end Head

/-- **Conditional on hS: the bound at each member.** hS: at every site at the member's place the
three hypotheses of the lookups' bounds hold at the site's face. -/
theorem k3Marks_debt (C : CK) (kap : ℝ≥0∞) (Zp : ProofFile.Pub) (G₀ : ProofFile.Ground) (mk : Mark)
    (h : mk ∈ k3Marks Zp G₀) (dsb : List RDT)
    (hS : ∀ s ∈ lookSites Zp, s.at_.place = mk.place →
      CanAll C s.at_.face dsb ∧ FewAll C s.at_.face dsb kap ∧ FewOut C s.at_.face dsb kap) :
    MarkDebt C mk dsb (fun _ => True) ((mk.share.num : ℝ≥0∞) * kap) := by
  obtain ⟨s, hs, rfl | rfl⟩ := k3Marks_mem Zp G₀ mk h
  · obtain ⟨hc, hf, _⟩ := hS s hs rfl
    exact markK3_debt C s.at_.place s.at_.face dsb kap hc hf
  · obtain ⟨hc, _, hf⟩ := hS s hs rfl
    exact markOut_debt C s.at_.place s.at_.face dsb kap hc hf

end ProofFile.Honest.K3.Good

#print axioms ProofFile.Honest.K3.Good.k3Marks_mem
#print axioms ProofFile.Honest.K3.Good.k3Marks_kind
#print axioms ProofFile.Honest.K3.Good.k3Marks_seat
#print axioms ProofFile.Honest.K3.Good.k3Marks_length
#print axioms ProofFile.Honest.K3.Good.count_twice
#print axioms ProofFile.Honest.K3.Good.k3Marks_count
#print axioms ProofFile.Honest.K3.Good.pairs50_nodup
#print axioms ProofFile.Honest.K3.Good.pairs50_length
#print axioms ProofFile.Honest.K3.Good.sites_fifty
#print axioms ProofFile.Honest.K3.Good.k3Marks_100
#print axioms ProofFile.Honest.K3.Good.site_lt25
#print axioms ProofFile.Honest.K3.Good.site_in_ps
#print axioms ProofFile.Honest.K3.Good.k3Marks_member
#print axioms ProofFile.Honest.K3.Good.k3Marks_debt
