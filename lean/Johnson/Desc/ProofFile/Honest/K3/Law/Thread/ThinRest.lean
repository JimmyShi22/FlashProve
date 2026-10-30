-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ThinRest.lean: the kind "lookup" (K3): the field there of
`SiteRest'` (Honest/K3/Law/Thread/LotAtSite.lean), "the site's place stands in the written list of
places", is shown under the library's hypothesis `P5J.AtMgA`; and the three theorems of that file that
take `SiteRest'` once more, under a structure without that field. One structure; theorems.

Terms. Honest/K3/GLOSSARY.md; the head of LotAtSite.lean.

What is defined. `SiteRestThin`: `SiteRest'` less its field there: five fields, each with the text that
it has there.

What is shown.
  `there_of_site`: under `P5J.AtMgA`, at every site: the written list of places holds the site's place.
  `SiteRestThin.rest`: so `SiteRestThin` gives `SiteRest'`.
  `siteAt_lettersAt_thin`, `plays_lettersAt_thin`, `accepted_lettersAt_thin`: `siteAt_lettersAt'`,
    `plays_lettersAt'` and `accepted_lettersAt'` under `SiteRestThin`: one call of the elder each; the
    conclusions are the elder's, to the letter.

Hypotheses that remain. The elder theorems', with five fields in the place of six. Of the five, ok is
stated at every site by `face_ok_site` (Johnson/AtFull/Shape/FaceAtSites.lean), which this file does
not import.

How the proof goes. `there_of_site`: `link_lt_head` (LinkLtHead.lean); `site_digits_paid`
(RngWrittenHolds.lean) gives a site at that link and sort whose place stands in the list;
`site_place_head` (AtLink.lean) says that both sites' places are one.

A second text. `site_in_ps` (Honest/K3/Good/MarksHead.lean) has the sentence of `there_of_site` as a
membership; it goes by `rng_at` (Johnson/AtFull/Shape/SitesAtHead.lean), which this file does not
import. Here it goes by `site_digits_paid`: so it stands on fewer files. Both stand: the elder file is
unchanged.

`SiteRestThin` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. At the full size alone. No instance of the hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LotAtSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RngWrittenHolds
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLink

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place KindName Strs)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

/-- **The written list of places holds every site's place.** Conditional on `P5J.AtMgA` and the site.
No instance of these hypotheses is exhibited in this file. -/
theorem there_of_site {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp) :
    P5J.At.ps.contains s.at_.place = true := by
  obtain ⟨s', _, _, _, e3, e4⟩ := site_digits_paid h s.link (link_lt_head h s hs) s.digits
  refine List.contains_iff_mem.2 ?_
  rw [site_place_head h s hs, ← e3]
  exact e4

/-- `SiteRest'` (Honest/K3/Law/Thread/LotAtSite.lean) less its field there. -/
structure SiteRestThin {W₀ Rc Xi Tr Xo Wj : Type} (Zp : Pub) (cF : Chain TS ProofFile.Cl)
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xo)) (s : Site)
    (J : LookJobs Wj) (wit : Local W₀ Rc Xi Tr → Wj) : Prop where
  /-- the list of halves holds the lookup's seated row at the site's place -/
  half : hs.find? (fun g => g.place == s.at_.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)
  /-- four tests with code on public data -/
  fits : siteFits cF.blocksInOrder s = true
  ok : s.at_.face.ok = true
  shapeIs : (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true
  usedIs : (!s.digits || s.caller == .head ||
    usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true

/-- `SiteRestThin` gives `SiteRest'`. Conditional on `P5J.AtMgA` and the site. -/
theorem SiteRestThin.rest {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
    (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {W₀ Rc Tr Xo Wj : Type}
    {hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo)} {s : Site}
    {J : LookJobs Wj} {wit : Local W₀ Rc ProofFile.Inst Tr → Wj} (R : SiteRestThin Zp cF hs s J wit)
    (hsite : s ∈ lookSites Zp) : SiteRest' Zp cF hs s J wit :=
  ⟨there_of_site h s hsite, R.half, R.fits, R.ok, R.shapeIs, R.usedIs⟩

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts} {W₀ Rc Tr Xo Wj : Type}
  (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
  (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
  (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
  (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
  (keeps : Nat → TS → TS → Prop)

/-- `siteAt_lettersAt'` under `SiteRestThin`. At the full size alone. No instance of these hypotheses is
exhibited in this file. -/
theorem siteAt_lettersAt_thin (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRestThin Zp cF hs s J wit) :
    ∃ lot Bs, SiteAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp Bs cF s lot J wit h.𝔇.sent h.𝔇.l3 :=
  siteAt_lettersAt' h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite J wit
    (R.rest h hsite)

/-- `plays_lettersAt'` under `SiteRestThin`. At the full size alone. No instance of these hypotheses is
exhibited in this file. -/
theorem plays_lettersAt_thin (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRestThin Zp cF hs s J wit) :
    Plays (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (borderOf s.link s.digits) :=
  plays_lettersAt' h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite J wit
    (R.rest h hsite)

/-- `accepted_lettersAt'` under `SiteRestThin`. At the full size alone. No instance of these hypotheses is
exhibited in this file. -/
theorem accepted_lettersAt_thin (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRestThin Zp cF hs s J wit)
    (hH : HeadReturns (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      (borderOf s.link s.digits) :=
  accepted_lettersAt' h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite J wit
    (R.rest h hsite) hH fall

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.there_of_site
#print axioms ProofFile.Honest.K3.Law.AtThr.SiteRestThin.rest
#print axioms ProofFile.Honest.K3.Law.AtThr.siteAt_lettersAt_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_lettersAt_thin
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_lettersAt_thin
