-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SitePays.lean: conditional: five of the hypotheses on a
lookup's place in the first chain's letters (`SiteAt`, Honest/K3/Law/Thread/SiteThr.lean), shown:
the member's rounds, its oracle messages and the entries' test, from the member's own test on the
plan; the number of rounds in front, from a test with code; the half at the place, from the frame's
own gathering of the lots' halves. Theorems.

Terms. Honest/K3/GLOSSARY.md: see there site, lot, half, member, flat list, border and frame. In
this file: the gathered halves are `firstOf Z Gr ls` (Honest/Frame.lean).

What is shown.
  `member_plan_site`: the description's member at a site: its rounds and oracle messages are those
    of the plan's entries, and the hearing at the site's face goes by these entries.
  `borderNo_of_nodup`: in a list of sub-protocols no two of which share a place, a sub-protocol's
    number is the border's at its place.
  `base_site`, `base_site_nodup`: the site's number of rounds in front is the flat list's own count
    up to the member.
  `find_once`: in a list of halves no two of which share a place, the search at a half's place finds
    that half.
  `half_in`, `half_site`: the half of the lookups' lot at a site stands in the gathered list; so the
    search at the site's place finds it.
  `half_seat`: the same at the seated row of Honest/K3/Row.lean.

Hypotheses that remain. Each theorem's are in its docstring.
  `O`, `hs`, `hb`, `hbs`, `hm`, `hmp`, `hpk`: (in `member_plan_site`) the description returns; the
    site; the sub-protocol of the lookups' lot at its place; the member at that place; and the
    member passes its test on the plan.
  `hf`: `siteFits` (Honest/K3/Law/SiteFits.lean): a test with code.
  `hn`: no two share a place: asked of the description's flat list, and of the gathered list of
    halves.
  `hl`: the lot stands in the list of lots.
  `hp`: (in `base_site_nodup`) blk stands at the site's place.

Imported: Honest/Frame.lean and Honest/Thread/HeardLaw.lean.

Users. Honest/K3/Law/Thread/SiteAtLetters.lean calls `member_plan_site` and `base_site_nodup`;
Honest/K3/Law/Thread/PlacesOnce.lean calls `base_site_nodup` and `half_site`;
Honest/K3/Law/Thread/HalfOfLot.lean calls `find_once`.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
"No two share a place" is a test on public data; it is not shown here of any description. Shown in
part: Honest/K3/Law/Thread/PlacesOnce.lean, from two tests with code (`halves_once`: the frame's
list of places with two halves is empty; `flat_once`: `FileDescription.placesOk` accepts); at the written
list of places: `ps_nodup` (Honest/K3/Law/Thread/SiteAtLetters.lean); of the sites' places, and of
the halves of `theLot` alone, with no hypothesis: `site_places_once`, `theLot_places_once`
(Honest/K3/Law/Thread/SitesOnce.lean). What stays open: of a description's own flat list, and of the
halves gathered over all lots of a list, it rests on these two tests; under `P5J.AtMgA` the proof of
`siteAt_lettersAt` (SiteAtLetters.lean) has it of the flat list, from `P5J.At.places_paid` and
`ps_nodup`, but no theorem of this folder states it by name.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.Thread.HeardLaw
import Johnson.Desc.ProofFile.Honest.K3.Law.MemberSite
import Johnson.Desc.ProofFile.Honest.K3.Law.SiteFits

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place Oracle)
open VerifiableInference.Desc.K3 (entriesFit)

local notation "FS" => VerifiableInference.Desc.First.S

/-! ## 1 Rounds, oracle messages, entries -/

/-- **The description's member at a site.** Conditional on the description's return; the site; the
sub-protocol of the lookups' lot at its place; the member at that place; and the member's test on
the plan. No instance of these hypotheses is exhibited in this file. -/
theorem member_plan_site (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) (Z : Pub)
    (Bs : PureBase) (base : List (Block FS ProofFile.Cl)) (ch : Chain FS ProofFile.Cl) (A : SharedSeat)
    (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) (s : Site)
      (hs : s ∈ lookSites Z)
    (b m : Block FS ProofFile.Cl) (hb : b ∈ (K3Lot.lot Z).blocks Bs.G₀) (hbs : b.place = s.at_.place)
    (hm : m ∈ ch.blocksInOrder) (hmp : m.place = b.place) (hpk : m.planOk = true) :
    m.rounds = (s.p.entries.getD []).map declOf ∧
      m.oracles = (s.p.entries.getD []).map (fun _ => ([] : List Oracle)) ∧
      entriesFit s.at_.face (s.p.entries.getD []) = true := by
  obtain ⟨_, hfit, _, hr, ho⟩ :=
    site_block o pol lay KL Fd Z Bs base ch A B O s hs b m hb hbs hm hmp hpk
  obtain ⟨_, gr, go, _, _⟩ := memberAtSite o pol lay KL Fd Z Bs base ch A B O b hb m hm hmp
  exact ⟨gr.trans hr, go.trans ho, hfit⟩

/-! ## 2 The rounds in front -/

section
variable {S Cl : Type}

/-- In a list of sub-protocols no two of which share a place, a sub-protocol's number is the number
of the border in front of its place. Conditional on that, and on the sub-protocol standing at the
number. -/
theorem borderNo_of_nodup : ∀ (bs : List (Block S Cl)) (b : Nat) (blk : Block S Cl) (p : Place),
    bs[b]? = some blk → blk.place = p → (bs.map (·.place)).Nodup → borderNo bs p = b
  | [], b, blk, p, h, _, _ => by simp at h
  | x :: bs, 0, blk, p, h, hp, _ => by
    have e : x = blk := by simpa using h
    have hx : (x.place == p) = true := by rw [e, hp]; exact beq_self_eq_true p
    simp [borderNo, List.findIdx_cons, hx]
  | x :: bs, b + 1, blk, p, h, hp, hn => by
    have h' : bs[b]? = some blk := by simpa using h
    rw [List.map_cons, List.nodup_cons] at hn
    have hmem : p ∈ bs.map (·.place) :=
      List.mem_map.2 ⟨blk, List.mem_of_getElem? h', hp⟩
    have hx : (x.place == p) = false := by
      rw [beq_eq_false_iff_ne]
      intro e
      exact hn.1 (e ▸ hmem)
    have ih := borderNo_of_nodup bs b blk p h' hp hn.2
    unfold borderNo at ih ⊢
    rw [List.findIdx_cons, hx]
    simp [ih]

/-- **The site's number of rounds in front is the flat list's own count up to the border at the
site's place.** Conditional on the test with code `siteFits` (Honest/K3/Law/SiteFits.lean) and on b
being that border's number. -/
theorem base_site (bs : List (Block S Cl)) (s : Site) (b : Nat) (hf : siteFits bs s = true)
    (hb : borderNo bs s.at_.place = b) : s.at_.base = roundsTo bs b := by
  rw [← hb]
  exact (roundsTo_inFront bs _ _ (base_of_fits bs s hf)).symm

/-- The same, where the member stands at number b and no two sub-protocols share a place.
Conditional on `siteFits` and on these. -/
theorem base_site_nodup (bs : List (Block S Cl)) (s : Site) (b : Nat) (blk : Block S Cl)
    (hf : siteFits bs s = true) (hb : bs[b]? = some blk) (hp : blk.place = s.at_.place)
    (hn : (bs.map (·.place)).Nodup) : s.at_.base = roundsTo bs b :=
  base_site bs s b hf (borderNo_of_nodup bs b blk _ hb hp hn)

end

/-! ## 3 The half at the place -/

section
variable {V W X : Type}

/-- In a list of halves no two of which share a place, the search at a half's place finds that half.
Conditional on these two. -/
theorem find_once : ∀ (hs : List (Placed V W X)) (g : Placed V W X), g ∈ hs →
    (hs.map (·.place)).Nodup → hs.find? (fun h => h.place == g.place) = some g
  | [], g, h, _ => by simp at h
  | x :: hs, g, h, hn => by
    rw [List.map_cons, List.nodup_cons] at hn
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · have hx : (x.place == g.place) = false := by
        rw [beq_eq_false_iff_ne]
        intro e
        exact hn.1 (e ▸ List.mem_map.2 ⟨g, h, rfl⟩)
      rw [List.find?_cons, hx]
      exact find_once hs g h hn.2

/-- The half of the lookups' lot at a site stands in the list that the frame gathers of the lots'
halves. Conditional on the lot standing in the list of lots, and on the site. -/
theorem half_in (Z : Pub) (Gr : Ground) (ls : List (HLot V W X)) (row : Site → List (Part V W X))
    (hl : lotBy row ∈ ls) (s : Site) (hs : s ∈ lookSites Z) :
    (⟨s.at_.place, row s⟩ : Placed V W X) ∈ firstOf Z Gr ls :=
  List.mem_flatMap.2 ⟨lotBy row, hl, List.mem_map.2 ⟨s, hs, rfl⟩⟩

/-- **The search at a site's place finds the half of the lookups' lot.** Conditional on the
lot standing in the list of lots; the site; and no two of the gathered halves sharing a place.
No instance of these hypotheses is exhibited in this file. -/
theorem half_site (Z : Pub) (Gr : Ground) (ls : List (HLot V W X)) (row : Site → List (Part V W X))
    (hl : lotBy row ∈ ls) (s : Site) (hs : s ∈ lookSites Z)
    (hn : ((firstOf Z Gr ls).map (·.place)).Nodup) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) = some ⟨s.at_.place, row s⟩ :=
  find_once _ ⟨s.at_.place, row s⟩ (half_in Z Gr ls row hl s hs) hn

/-- **The same at the seated row of Honest/K3/Row.lean**, at summands and a reader of the input that
may depend on the site. Conditional on the same three. No instance of these hypotheses is exhibited
in this file. -/
theorem half_seat {Wj : Type} (Z : Pub) (Gr : Ground) (ls : List (HLot V W X)) (R : Reads)
    (J : Site → LookJobs Wj) (wit : Site → W → Wj)
    (hl : lotBy (fun s => (proverSideOfLookupInChainAtOneOwner (V₁ := V) (X₁ := X) R (J s) (wit s) s.at_).parts) ∈ ls)
      (s : Site)
    (hs : s ∈ lookSites Z) (hn : ((firstOf Z Gr ls).map (·.place)).Nodup) :
    (firstOf Z Gr ls).find? (fun h => h.place == s.at_.place) =
      some (proverSideOfLookupInChainAtOneOwner R (J s) (wit s) s.at_) :=
  half_site Z Gr ls _ hl s hs hn

end

#print axioms ProofFile.Honest.K3.Law.AtThr.member_plan_site
#print axioms ProofFile.Honest.K3.Law.AtThr.borderNo_of_nodup
#print axioms ProofFile.Honest.K3.Law.AtThr.base_site
#print axioms ProofFile.Honest.K3.Law.AtThr.base_site_nodup
#print axioms ProofFile.Honest.K3.Law.AtThr.find_once
#print axioms ProofFile.Honest.K3.Law.AtThr.half_in
#print axioms ProofFile.Honest.K3.Law.AtThr.half_site
#print axioms ProofFile.Honest.K3.Law.AtThr.half_seat

end ProofFile.Honest.K3.Law.AtThr
