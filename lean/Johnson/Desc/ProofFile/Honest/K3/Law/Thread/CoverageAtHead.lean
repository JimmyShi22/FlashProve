-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/CoverageAtHead.lean: the kind "lookup" (K3): under the
library's hypothesis at the full size, `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): a site is made at
each of the lot's fifty addresses, and every sub-protocol of the kind in the description's first
chain has a half of `lotBy` (Honest/K3/Lot.lean) at its place, at every row. Theorems; no
definition.

Terms. Honest/K3/GLOSSARY.md. cF: the first chain that the description returns; `cF.blocksInOrder`: its list
of sub-protocols. `P5J.At.ps`: the written list of the chain's places (Johnson/P5J/LettersAt.lean).
`lotTests`: Honest/K3/Lot.lean. `strays`, `twice`, `lacking`: Honest/Frame.lean.

Why. "No miss" (`lookMisses Zp = []`) alone is void where there is no link, and speaks of the lot's
own list of addresses, not of the chain. So beside it stand: fifty addresses; and the two sentences
on `cF.blocksInOrder`.

What is shown, each conditional on `P5J.AtMgA`.
  `links_head`, `addresses_fifty`: 25 links; fifty addresses.
  `mem_addresses` (no hypothesis): an address of the lot's list, written out.
  `site_of_address`: at each address a site is made; its place is `IM.k3Place` at the address's link
    and sort, and stands on the written list. `site_in_written`: so does every site's place.
  `lookMisses_head`: **no miss.** `sites_fifty_head`: fifty sites. `table_head`: the table of places
    is made.
  `k3_places_written`, `k3_written_fifty` (no hypothesis): a place of the kind on the written list
    is one of the fifty; there are fifty. Calls of facts of the library.
  `places_head`: the places of the chain's sub-protocols are the written list. `look_has_site`: a
    site at the place of every sub-protocol of the kind.
  `every_look_has_half`: **every sub-protocol of the kind K3 in the chain has a half at its place.**
  `no_stray_half`: **every half stands at the place of a sub-protocol of the kind in the chain.**
  `looks_fifty`: the chain has fifty sub-protocols of the kind.
  `lotTests_three`: `lotTests`' third, fourth and eighth clause, as its own Booleans, at the lot's
    count of addresses, `cF.blocksInOrder`, `lookSites Zp` and the halves of `lotBy`. `lotTests_more`: its
    second, fifth, sixth and seventh.
  `covered_head`: no miss, fifty addresses, and a site at the place of every sub-protocol of the
    kind: as one conjunction.
  `every_look_has_half_of`: the two sentences, and that no place bears two halves, for whatever lot
    has the halves of a `lotBy` at Zp.

Kin. `sites_fifty_head` is the statement of this folder's `sites_fifty`
(Honest/K3/Good/MarksHead.lean) and `site_in_written` that of its `site_in_ps`, and of
`there_of_site` (Honest/K3/Law/Thread/ThinRest.lean) but for the form: typed anew under other names,
so that this file stands over fewer files.

Hypotheses that remain. h: `P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x`. Conditional on the head
`P5J.AtMgA`. That it holds at the goals' two named sets of public files is a sealed theorem
(`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own limits; this file
does not call it: AtFullSide/Honest/K3/CoveredAtNamed.lean [not in this library] does. In
`every_look_has_half_of`: hL: the lot's halves at Zp are those of `lotBy row`.

What is called. This folder's `site_digits_paid` (Honest/K3/Law/Thread/RngWrittenHolds.lean),
`spot_of_site` (Honest/K3/Law/LotOfSite.lean), `site_facts` (Honest/K3/Law/MemberSite.lean) and
Honest/K3/Law/Coverage.lean. Of the library: `P5J.AtMg.shape_full` (Johnson/P5J/ShapeFullAtMg.lean),
`P5J.At.places_paid` (Johnson/P5J/PlacesPaid.lean), `P5J.k03_border_of_kind`
(Johnson/P5J/K03AsksAt.lean), `k3Border_calls`, `k3Border_digits`
(Johnson/Desc/Sound/MgAt/K3RidesRows.lean) and `k3Split_full`
(Johnson/Desc/Sound/MgAt/K3RidesLed.lean).

Limits. Under the hypothesis, at letters: at no public part that is written out. It speaks of
`lotBy` at every row: which lots have such halves is said in Honest/K3/Law/CoverageLots.lean
[not in this library] and CoverageLotsNamed.lean. Not of the lots that drop halves (`theLotFit` and
its like). That a half stands at a place: nothing on what it sends. `lotTests`' first clause (just
one lot of the description bears the name) and its thirteen clauses a site: nothing.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Coverage
import Johnson.Desc.ProofFile.Honest.K3.Law.LotOfSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds
import Johnson.P5J.ShapeFullAtMg
import Johnson.P5J.PlacesPaid
import Johnson.P5J.K03AsksAt
import Johnson.Desc.Sound.MgAt.K3RidesRows
import Johnson.Desc.Sound.MgAt.K3RidesLed

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Chain Place KindName)
open VerifiableInference.Desc.K3 (pieceAt)
open VerifiableInference.OnPublicFiles (k3K k3Border_calls k3Border_digits k3SplitB k3Split_full)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

/-! ## 1 The written list of places -/

/-- A place of the kind K3 on the written list is one of the fifty. -/
theorem k3_places_written (p : Place) (hp : p ∈ P5J.At.ps) (hk : p.kind = .K3) :
    ∃ l, l < 25 ∧ ∃ d, p = IM.k3Place l d := by
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hp
  obtain ⟨l, hl, d, rfl⟩ := P5J.k03_border_of_kind hi hk
  refine ⟨l, hl, d, ?_⟩
  cases d with
  | false => exact Option.some.inj (hi.symm.trans (k3Border_calls hl).1)
  | true => exact Option.some.inj (hi.symm.trans (k3Border_digits hl).1)

/-- There are fifty. -/
theorem k3_written_fifty : (P5J.At.ps.filter fun p => p.kind == .K3).length = 50 := by
  have h := k3Split_full
  unfold k3SplitB at h
  have h2 := ((Bool.and_eq_true _ _).mp h).2
  have e : (fun p : Place => p.kind == KindName.K3) = fun a => decide (a.kind = .K3) := by
    funext a
    by_cases k : a.kind = .K3 <;> simp [k]
  rw [e]
  exact eq_of_beq h2

/-- An address of the lot's list, written out. -/
theorem mem_addresses (Z : Pub) (y : Nat × Bool × Place) (hy : y ∈ K3Lot.addresses Z) :
    ∃ i, i < Z.first.shape.link.length ∧ ∃ dg,
      y = (i, dg, (⟨1, some i, pieceAt Z.p.X i dg, .K3⟩ : Place)) := by
  unfold K3Lot.addresses at hy
  obtain ⟨i, hi, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨dg, _, rfl⟩ := List.mem_map.1 hy
  exact ⟨i, List.mem_range.1 hi, dg, rfl⟩

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 2 A site at every address -/

/-- Conditional on `P5J.AtMgA`: 25 links. -/
theorem links_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    Zp.first.shape.link.length = 25 := by
  rw [h.toAtMg.shape_full]
  rfl

/-- Conditional on `P5J.AtMgA`: fifty addresses. -/
theorem addresses_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (K3Lot.addresses Zp).length = 50 := by
  rw [addresses_length, links_head h]

/-- Conditional on `P5J.AtMgA`: at each address of the lot's list a site is made, at its written
place. -/
theorem site_of_address (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (y : Nat × Bool × Place)
    (hy : y ∈ K3Lot.addresses Zp) :
    ∃ s, siteAt Zp.p.X ((spotsOf Zp.cuts).getD []) y = some s ∧
      s.at_.place = IM.k3Place y.1 y.2.1 ∧ s.at_.place ∈ P5J.At.ps := by
  obtain ⟨i, hi, dg, rfl⟩ := mem_addresses Zp y hy
  rw [links_head h] at hi
  obtain ⟨s, hs, e1, e2, e3, e4⟩ := site_digits_paid h i hi dg
  unfold lookSites at hs
  obtain ⟨y', hy', hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨i', _, dg', rfl⟩ := mem_addresses Zp y' hy'
  obtain ⟨_, _, f3, f4, _⟩ := site_facts _ _ _ s hsy
  have g1 : i' = i := f3.symm.trans e1
  have g2 : dg' = dg := f4.symm.trans e2
  subst g1 g2
  exact ⟨s, hsy, e3, e4⟩

/-- Conditional on `P5J.AtMgA`: every site's place stands on the written list. -/
theorem site_in_written (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : s.at_.place ∈ P5J.At.ps := by
  unfold lookSites at hs
  obtain ⟨y, hy, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨s', e, _, e4⟩ := site_of_address h y hy
  obtain rfl : s' = s := Option.some.inj (e.symm.trans hsy)
  exact e4

/-- **Conditional on `P5J.AtMgA`: no miss.** Alone it is void where there is no link: see the head.
-/
theorem lookMisses_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) : lookMisses Zp = [] :=
  (lookMisses_nil_iff Zp).2 fun y hy => by
    obtain ⟨s, e, _⟩ := site_of_address h y hy
    rw [e]
    rfl

/-- Conditional on `P5J.AtMgA`: fifty sites. -/
theorem sites_fifty_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (lookSites Zp).length = 50 := by
  have e := sites_add_misses Zp
  rw [lookMisses_head h, addresses_fifty h] at e
  exact e

/-- Conditional on `P5J.AtMgA`: the table of places is made. -/
theorem table_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (spotsOf Zp.cuts).isSome = true :=
  table_of_no_miss Zp (lookMisses_head h) (by rw [links_head h]; decide)

/-! ## 3 The chain's own sub-protocols -/

/-- Conditional on `P5J.AtMgA`: the places of the chain's sub-protocols are the written list. -/
theorem places_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    cF.blocksInOrder.map (·.place) = P5J.At.ps :=
  P5J.At.places_paid h.scope h.reads h.laid

/-- Conditional on `P5J.AtMgA`: a site at the place of every sub-protocol of the kind in the chain.
-/
theorem look_has_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ b ∈ cF.blocksInOrder, b.place.kind = .K3 → ∃ s ∈ lookSites Zp, s.at_.place = b.place := by
  intro b hb hk
  have hp : b.place ∈ P5J.At.ps := by
    rw [← places_head h]
    exact List.mem_map.2 ⟨b, hb, rfl⟩
  obtain ⟨l, hl, d, ep⟩ := k3_places_written b.place hp hk
  obtain ⟨s, hs, _, _, e3, _⟩ := site_digits_paid h l hl d
  exact ⟨s, hs, e3.trans ep.symm⟩

section
variable {V W X : Type}

/-- **Conditional on `P5J.AtMgA`: every sub-protocol of the kind K3 in the chain has a half at its
place**, at every row. -/
theorem every_look_has_half (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (row : Site → List (Part V W X)) (G : Ground) :
    ∀ b ∈ cF.blocksInOrder, b.place.kind = .K3 → ∃ hf ∈ (lotBy row).halves Zp G, hf.place = b.place := by
  intro b hb hk
  obtain ⟨s, hs, e⟩ := look_has_site h b hb hk
  exact ⟨⟨s.at_.place, row s⟩, List.mem_map.2 ⟨s, hs, rfl⟩, e⟩

/-- **Conditional on `P5J.AtMgA`: every half stands at the place of a sub-protocol of the kind in
the chain.** -/
theorem no_stray_half (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (row : Site → List (Part V W X)) (G : Ground) :
    ∀ hf ∈ (lotBy row).halves Zp G, ∃ b ∈ cF.blocksInOrder, b.place = hf.place ∧ b.place.kind = .K3 := by
  intro hf hm
  obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hm
  have hp : s.at_.place ∈ cF.blocksInOrder.map (·.place) := by
    rw [places_head h]
    exact site_in_written h s hs
  obtain ⟨b, hb, e⟩ := List.mem_map.1 hp
  exact ⟨b, hb, e, by rw [e]; exact (spot_of_site Zp s hs).1⟩

end

/-- Conditional on `P5J.AtMgA`: the chain has fifty sub-protocols of the kind. -/
theorem looks_fifty (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    (cF.blocksInOrder.filter fun b => b.place.kind == .K3).length = 50 := by
  have e : ((cF.blocksInOrder.map (·.place)).filter fun p => p.kind == .K3).length = 50 := by
    rw [places_head h]
    exact k3_written_fifty
  rw [List.filter_map, List.length_map] at e
  exact e

section
variable {V W X : Type}

/-- Conditional on `P5J.AtMgA`: `lotTests`' third, fourth and eighth clause, as its own Booleans. -/
theorem lotTests_three (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (row : Site → List (Part V W X)) (G : Ground) :
    ((lookSites Zp).length == (K3Lot.addresses Zp).length) = true ∧
      ((lookSites Zp).length == (cF.blocksInOrder.filter fun b => b.place.kind == .K3).length) = true ∧
      (lacking (cF.blocksInOrder.filter fun b => b.place.kind == .K3)
        ((lotBy row).halves Zp G)).isEmpty = true := by
  refine ⟨?_, ?_, ?_⟩
  · rw [sites_fifty_head h, addresses_fifty h]
    rfl
  · rw [sites_fifty_head h, looks_fifty h]
    rfl
  · unfold lacking
    rw [List.filter_eq_nil_iff.2 fun b hb => ?_]
    · rfl
    · obtain ⟨hb1, hb2⟩ := List.mem_filter.1 hb
      obtain ⟨hf, hm, e⟩ := every_look_has_half h row G b hb1 (eq_of_beq hb2)
      have ha : (((lotBy row).halves Zp G).any fun g => g.place == b.place) = true :=
        List.any_eq_true.2 ⟨hf, hm, by rw [e]; exact beq_self_eq_true _⟩
      rw [ha]
      simp

/-- Conditional on `P5J.AtMgA`: its second, fifth, sixth and seventh clause. -/
theorem lotTests_more (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (row : Site → List (Part V W X)) (G : Ground) :
    ((K3Lot.addresses Zp).length != 0) = true ∧
      (((lotBy row).halves Zp G).map (·.place) == (lookSites Zp).map (·.at_.place)) = true ∧
      (strays cF.blocksInOrder ((lotBy row).halves Zp G)).isEmpty = true ∧
      (twice ((lotBy row).halves Zp G)).isEmpty = true := by
  refine ⟨?_, ?_, ?_, lotBy_twice row Zp G⟩
  · rw [addresses_fifty h]
    rfl
  · rw [lotBy_places]
    exact beq_self_eq_true _
  · unfold strays
    rw [List.filter_eq_nil_iff.2 fun hf hm => ?_]
    · rfl
    · obtain ⟨b, hb, e, _⟩ := no_stray_half h row G hf hm
      have ha : (cF.blocksInOrder.any fun b => b.place == hf.place) = true :=
        List.any_eq_true.2 ⟨b, hb, by rw [e]; exact beq_self_eq_true _⟩
      rw [ha]
      simp

end

/-- **Conditional on `P5J.AtMgA`: no miss, fifty addresses, and a site at the place of every
sub-protocol of the kind in the chain.** -/
theorem covered_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    lookMisses Zp = [] ∧ (K3Lot.addresses Zp).length = 50 ∧
      ∀ b ∈ cF.blocksInOrder, b.place.kind = .K3 → ∃ s ∈ lookSites Zp, s.at_.place = b.place :=
  ⟨lookMisses_head h, addresses_fifty h, look_has_site h⟩

section
variable {V W X : Type}

/-- Conditional on `P5J.AtMgA` and hL: the two sentences, and that no place bears two halves, for
whatever lot has the halves of a `lotBy` at Zp. -/
theorem every_look_has_half_of (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (L : HLot V W X)
    (row : Site → List (Part V W X)) (G : Ground)
    (hL : L.halves Zp G = (lotBy row).halves Zp G) :
    (∀ b ∈ cF.blocksInOrder, b.place.kind = .K3 → ∃ hf ∈ L.halves Zp G, hf.place = b.place) ∧
      (∀ hf ∈ L.halves Zp G, ∃ b ∈ cF.blocksInOrder, b.place = hf.place ∧ b.place.kind = .K3) ∧
      ((L.halves Zp G).map (·.place)).Nodup := by
  rw [hL]
  exact ⟨every_look_has_half h row G, no_stray_half h row G, lotBy_places_nodup row Zp G⟩

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3_places_written
#print axioms ProofFile.Honest.K3.Law.AtThr.k3_written_fifty
#print axioms ProofFile.Honest.K3.Law.AtThr.mem_addresses
#print axioms ProofFile.Honest.K3.Law.AtThr.links_head
#print axioms ProofFile.Honest.K3.Law.AtThr.addresses_fifty
#print axioms ProofFile.Honest.K3.Law.AtThr.site_of_address
#print axioms ProofFile.Honest.K3.Law.AtThr.site_in_written
#print axioms ProofFile.Honest.K3.Law.AtThr.lookMisses_head
#print axioms ProofFile.Honest.K3.Law.AtThr.sites_fifty_head
#print axioms ProofFile.Honest.K3.Law.AtThr.table_head
#print axioms ProofFile.Honest.K3.Law.AtThr.places_head
#print axioms ProofFile.Honest.K3.Law.AtThr.look_has_site
#print axioms ProofFile.Honest.K3.Law.AtThr.every_look_has_half
#print axioms ProofFile.Honest.K3.Law.AtThr.no_stray_half
#print axioms ProofFile.Honest.K3.Law.AtThr.looks_fifty
#print axioms ProofFile.Honest.K3.Law.AtThr.lotTests_three
#print axioms ProofFile.Honest.K3.Law.AtThr.lotTests_more
#print axioms ProofFile.Honest.K3.Law.AtThr.covered_head
#print axioms ProofFile.Honest.K3.Law.AtThr.every_look_has_half_of
