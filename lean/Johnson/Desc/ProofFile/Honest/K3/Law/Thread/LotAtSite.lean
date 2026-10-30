-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/LotAtSite.lean: conditional, under the library's
hypothesis `P5J.AtMgA`: at every lookup of the public part whose place stands in the written list of
places, a sub-protocol of the lookups' lot stands at the site's place. So two hypotheses of
`SiteRest` (Honest/K3/Law/Thread/SiteAtLetters.lean) are no longer needed, and one test with code on
public data is added. One structure of hypotheses; theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. See there lot, too.

What is shown.
  `lot_at_site`: the sub-protocol.
  `SiteRest'`, `rest_of_rest'`: what remains: `SiteRest` without the sub-protocol, with the test;
    and that there is a sub-protocol with which `SiteRest` holds.
  `siteAt_lettersAt'`, `plays_lettersAt'`, `accepted_lettersAt'`: under it: `SiteAt`
    (Honest/K3/Law/Thread/SiteThr.lean), `Plays` and `Accepted` (Honest/Thread/Pays.lean) at the
    first chain's letters set to the library's own.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the three public files in
    scope, the description laid, its tests on the plan passed.
  `hs`, `hsite`: s is a site of the public part.
  `hp`: (in `lot_at_site`) the site's place stands in the written list.
  `R`: `SiteRest'`: the site's place stands in `P5J.At.ps` (Johnson/P5J/LettersAt.lean); the list of
    halves holds the lookup's seated row at the site's place; four tests with code on public data.
  `hH`: (in `accepted_lettersAt'`) `HeadReturns` (SiteThr.lean).

Imported. Files under Honest/Thread/.

How the proof goes. `lot_block_at` (Honest/K3/Law/LotMember.lean) goes from a sub-protocol of the
lot to its address; this is the way back. It rests on this: in scope, at each of the fifty written
places of the kind, the kind's own maker of sub-protocols returns (the library's `IM.k3_of`,
Johnson/IMR/K3Seat.lean).

Users. Honest/K3/Law/Thread/RestOfFits.lean calls `plays_lettersAt'` and `accepted_lettersAt'`.

`SiteRest'` has the field half: the list of halves holds, at the lookup's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. All statements are implications. No instance of these hypotheses is exhibited in this file.
At the full size alone: that limit comes with `P5J.AtMgA`. The test that is added: the site's place
stands in `P5J.At.ps`, the written list of places at the full size. It says of the public part that
the site's link is below 25 and that its piece, which the site reads off the public structure (is
the link the head's?), is the written one. That is not shown here of a public part in scope. Shown
in part: Honest/K3/Law/Thread/ThereOf.lean (`there_of_facts`): the test, of every site, from three
public facts, which are hypotheses there: attention links stand between the layers' links; there are
twelve groups; the first chain's shape has at most 25 links. Under `P5J.AtMgA` alone: there is such
a site at every link below 25, at either sort (`site_at_all_fifty`,
Honest/K3/Law/Thread/SiteAllFifty.lean); every site's place is the library's written one at its link
and sort (`site_place_head`, Honest/K3/Law/Thread/AtLink.lean); and every site's link is below 25
(`link_lt_head`, Honest/K3/Law/Thread/LinkLtHead.lean). That the test itself accepts at a given site
under `P5J.AtMgA` alone:
`site_in_ps` (Honest/K3/Good/MarksHead.lean) concludes, under `P5J.AtMgA`, that
every site's place stands in `P5J.At.ps`; so does `there_of_site`
(Honest/K3/Law/Thread/ThinRest.lean). Here it remains the field there of `SiteRest'`. That field is
spent in `rest_of_rest'` alone, for `lot_at_site`. `lot_of_site` (Honest/K3/Law/LotOfSite.lean)
gives a sub-protocol of the lookups' lot at every site's place from the description's return, which
`P5J.AtMgA` holds, with no test on the list of places; that it serves here in the place of
`lot_at_site` is not tried here. It is called under
`P5J.AtMgA` in `link_lt_head` (Honest/K3/Law/Thread/LinkLtHead.lean) and in
Honest/K3/Good/H3/MemberAtSite.lean.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.AtLetters
import Johnson.IMR.K3Seat

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place KindName Strs)
open VerifiableInference.Desc.K3 (pieceAt)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (pieceOf borderOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **A sub-protocol of the lookups' lot stands at the site's place.** Conditional on `P5J.AtMgA`,
the site, and the site's place standing in the written list. No instance of these hypotheses is
exhibited in this file. -/
theorem lot_at_site (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (hp : s.at_.place ∈ P5J.At.ps) :
    ∃ lot ∈ K3Lot.hear Zp, lot.place = s.at_.place := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpl := site_place Zp s hs
  obtain ⟨l, hl, d, e⟩ := k3_place_full hp (by rw [hpl])
  obtain ⟨_, _, b', _, _, hb', _⟩ := IM.k3_of h.scope h.reads O l hl d
  rw [O.W] at hb'
  have ep : IM.k3Place l d = s.at_.place := by
    rw [e]
    rfl
  rw [ep] at hb'
  have hs' := hs
  unfold lookSites at hs'
  obtain ⟨y, hy, hsy⟩ := List.mem_filterMap.1 hs'
  obtain ⟨_, _, _, _, f5, _, _, _⟩ := site_facts _ _ y s hsy
  refine ⟨b', ?_, IM.theStated_place hb'⟩
  unfold K3Lot.hear
  exact List.mem_filterMap.2 ⟨y, hy, by rw [← f5]; exact hb'⟩

end

/-- **The hypotheses that remain**: `SiteRest` without the sub-protocol of the lot; with the test on
the site's place. -/
structure SiteRest' {W₀ Rc Xi Tr Xo Wj : Type} (Zp : Pub) (cF : Chain TS ProofFile.Cl)
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xo)) (s : Site)
    (J : LookJobs Wj) (wit : Local W₀ Rc Xi Tr → Wj) : Prop where
  /-- the site's place stands in the written list of places: a test with code on public data -/
  there : P5J.At.ps.contains s.at_.place = true
  /-- the list of halves holds the lookup's seated row at the site's place -/
  half : hs.find? (fun g => g.place == s.at_.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)
  /-- four tests with code on public data -/
  fits : siteFits cF.blocksInOrder s = true
  ok : s.at_.face.ok = true
  shapeIs : (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true
  usedIs : (!s.digits || s.caller == .head ||
    usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true

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

include h in
/-- There is a sub-protocol with which `SiteRest` holds. Conditional on `P5J.AtMgA`, the site and
`SiteRest'`. No instance of these hypotheses is exhibited in this file. -/
theorem rest_of_rest' (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRest' Zp cF hs s J wit) :
    ∃ lot, SiteRest Zp cF hs s lot J wit := by
  obtain ⟨lot, h1, h2⟩ := lot_at_site h s hsite (List.contains_iff_mem.1 R.there)
  exact ⟨lot, h1, h2, R.half, R.fits, R.ok, R.shapeIs, R.usedIs⟩

/-- **`SiteAt` at the first chain's letters set to the library's own.** Conditional on `P5J.AtMgA`,
the site, and `SiteRest'`. At the full size alone. No instance of these hypotheses is exhibited in
this file. -/
theorem siteAt_lettersAt' (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRest' Zp cF hs s J wit) :
    ∃ lot Bs, SiteAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp Bs cF s lot J wit h.𝔇.sent h.𝔇.l3 := by
  obtain ⟨lot, R'⟩ := rest_of_rest' h hs s hsite J wit R
  exact ⟨lot, siteAt_lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite
    lot J wit R'⟩

/-- **It plays.** Conditional on the same. At the full size alone. No instance of these hypotheses
is exhibited in this file. -/
theorem plays_lettersAt' (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRest' Zp cF hs s J wit) :
    Plays (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread
      (borderOf s.link s.digits) := by
  obtain ⟨lot, R'⟩ := rest_of_rest' h hs s hsite J wit R
  exact plays_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite lot J
    wit R'

/-- **It is accepted, at every letter fall.** Conditional on the same and on `HeadReturns`. At the
full size alone. No instance of these hypotheses is exhibited in this file. -/
theorem accepted_lettersAt' (s : Site) (hsite : s ∈ lookSites Zp) (J : LookJobs Wj)
    (wit : Local W₀ Rc ProofFile.Inst Tr → Wj) (R : SiteRest' Zp cF hs s J wit)
    (hH : HeadReturns (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp s)
    (fall : Nat → TS → List Fmt.Drawn → Option String) :
    Accepted (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps).thread fall
      (borderOf s.link s.digits) := by
  obtain ⟨lot, R'⟩ := rest_of_rest' h hs s hsite J wit R
  exact accepted_letters h hs Q stored ans test carryX item n₁ n₂ valid rides keeps s hsite lot
    J wit R' hH fall

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.lot_at_site
#print axioms ProofFile.Honest.K3.Law.AtThr.rest_of_rest'
#print axioms ProofFile.Honest.K3.Law.AtThr.siteAt_lettersAt'
#print axioms ProofFile.Honest.K3.Law.AtThr.plays_lettersAt'
#print axioms ProofFile.Honest.K3.Law.AtThr.accepted_lettersAt'
