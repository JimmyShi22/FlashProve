-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/SiteAtLetters.lean: conditional, under the library's
hypothesis `P5J.AtMgA`: the hypotheses on a lookup's member of the first chain (`SiteAt`,
Honest/K3/Law/Thread/SiteThr.lean) at the first chain's letters set to the library's own
(`lettersAt`, Honest/Thread/FirstAt.lean): which clauses follow, and which remain hypotheses. One
closed test, one structure of hypotheses, theorems.

Terms. Honest/K3/GLOSSARY.md: see there thread, border, letters, frame, half, seat, site, member,
step and coins. In this file: the letters are `lettersAt h hs Q ...` under h, a value of
`P5J.AtMgA`: the flat list is the description's own first chain cF; the segments' sorts and the
places are the written lists at the full size; the meaning of the promise is the library's composed
one. The list hs of halves is a letter.

What is shown.
  `k3AllB`, `k3AllB_full`, `ps_nodup`, `k3_place_full`: closed facts on the written list of places
    `P5J.At.ps` (Johnson/P5J/LettersAt.lean): every place of the kind K3 in it is one of the fifty;
    no two of its places are one.
  `sort_of_piece`, `site_place`, `site_border`: a site's place in the written list: the site's link
    is below 25; at the written border's number stands the site's place; the two texts of the piece
    agree.
  `SiteRest`: the hypotheses that remain.
  `siteAt_lettersAt`: `SiteAt` at these letters, at the written number of the border in front of the
    lookup.

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA` (Johnson/P5J/MgAtAll.lean): the three public files in
    scope, the description laid, its tests on the plan passed.
  `hs`, `hsite`: s is a site of the public part.
  `hin`, `hlp`: (in `site_border`) a sub-protocol of the lookups' lot stands at the site's place.
  `R`: `SiteRest`: a sub-protocol of the lookups' lot stands at the site's place; the list of halves
    holds the lookup's seated row at that place; four tests with code on public data: `siteFits`
    (Honest/K3/Law/SiteFits.lean), the face's own tests, `sameShape` at the calls of a layers' link,
    `usedAt` at the digits.
  `hp`, `hk`: (in `k3_place_full`) the place stands in the written list; it is of the kind K3.

Imported: the files under Honest/Thread/ and Honest/Member/InSegment.lean.

How the proof goes. What follows under h, the site, and a sub-protocol of the lookups' lot at the
site's place, field by field of `SiteAt`:
  the number b: b := `borderOf s.link s.digits` (Johnson/Desc/Sound/MgAt/K3Open.lean), the written
    number of the border in front.
  flat: by the letters' text.
  place: the description's places are the written list (`P5J.At.places_paid`,
    Johnson/P5J/PlacesPaid.lean); at that number stands the lookup's place (`places_are_k3`,
    K3Open.lean).
  plan: every member passes its test on the plan (`IM.plan_flat`, Johnson/IMR/PlanAt.lean;
    `P5J.AtMgA` holds the test).
  rounds, oracles, entries: `member_plan_site` (Honest/K3/Law/Thread/SitePays.lean).
  base: `base_site_nodup` (SitePays.lean), from the test `siteFits`; no two places of the written
    list are one: a closed test here.
  k3At: the library's `k3At_mgAll` (Johnson/Desc/Sound/MgAt/K3At.lean).
  lookIn: the library's `k3_open_calls` and `k3_open_digits` (K3Open.lean): "lookIn" is open at that
    border.
That the description can be opened at cF (`IM.Open`) is a field of `P5J.AtMgA`. The fields entries
and base are shown at one block that is found at number b; the other clauses at every block at b. It
is the same block: `cF.blocksInOrder[b]?` has one value.

Users. Honest/K3/Law/Thread/AtLetters.lean, Honest/K3/Law/Thread/AtThreadBridges.lean
[not in this library] and Honest/K3/Law/Thread/LotAtSite.lean call `siteAt_lettersAt`.
Honest/K3/Law/Thread/KeepsKind.lean [not in this library], Honest/K3/Law/Thread/LinkLtHead.lean,
Honest/K3/Law/Thread/RidersAtHeadSite.lean and Honest/K3/Law/Thread/SiteAtHead.lean import this file
too.

`SiteRest` has the field half: the list of halves holds, at the lookup's place, the elder row
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
Two closed facts on the written list of places at the full size are decided by Lean's kernel
(`k3AllB_full`, `ps_nodup`); nothing else is evaluated at the full size, and no value of `P5J.AtMgA`
is exhibited here. At the full size alone: that limit comes with `P5J.AtMgA`. No statement of this
file says that a verifier's sub-protocol accepts.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SitePays
import Johnson.Desc.ProofFile.Honest.Thread.FirstAt
import Johnson.Desc.ProofFile.Honest.Member.InSegment
import Johnson.Desc.Sound.MgAt.K3At
import Johnson.Desc.Sound.MgAt.K3Open
import Johnson.P5J.PlacesPaid
import Johnson.IMR.PlanAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain Place KindName Strs Wit)
open VerifiableInference.Desc.K3 (pieceAt isHead)
open VerifiableInference.Desc.First (pubSets flatPlacesOf blockPlaces)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.Sound (mgAll mgBase mgMore mgAll_more_closed linksFull MsgT)
open VerifiableInference.Desc.Sound.MgAt (pieceOf ixOf borderOf openAt k3_open_calls k3_open_digits
  places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA mgAtAll CellsM TS)
open ProofFile.Honest.FirstThread (lettersAt WtF Script)

/-! ## 1 Closed facts on the written list of places -/

/-- A test: every place of the kind K3 in the written list is one of the fifty. -/
def k3AllB : Bool :=
  P5J.At.ps.all fun p => p.kind != KindName.K3 ||
    (List.range 25).any fun l => [false, true].any fun d =>
      decide (p = ⟨1, some l, pieceOf l d, KindName.K3⟩)

set_option maxRecDepth 1000000 in
theorem k3AllB_full : k3AllB = true := by decide +kernel

set_option maxRecDepth 1000000 in
/-- No two places of the written list are one. -/
theorem ps_nodup : P5J.At.ps.Nodup := by decide +kernel

/-- A place of the kind K3 in the written list is one of the fifty. -/
theorem k3_place_full {p : Place} (hp : p ∈ P5J.At.ps) (hk : p.kind = KindName.K3) :
    ∃ l, l < 25 ∧ ∃ d, p = ⟨1, some l, pieceOf l d, KindName.K3⟩ := by
  have h := List.all_eq_true.1 k3AllB_full p hp
  rw [hk] at h
  simp only [bne_self_eq_false, Bool.false_or, List.any_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  obtain ⟨l, hl, d, _, e⟩ := h
  exact ⟨l, hl, d, e⟩

/-- The two texts of a lookup's piece tell the calls from the digits alike. -/
theorem sort_of_piece (X : OnBytes.Model.Verify.Public) (l : Nat) (dg d : Bool)
    (h : pieceAt X l dg = pieceOf l d) : dg = d := by
  unfold pieceAt pieceOf ixOf at h
  cases dg <;> cases d <;> first
    | rfl
    | (exfalso; revert h; cases isHead X l <;> by_cases e : l = 24 <;> simp [e])

/-! ## 2 A site's place in the written list -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- A site's place, written out. -/
theorem site_place (Zq : Pub) (s : Site) (hs : s ∈ lookSites Zq) :
    s.at_.place = ⟨1, some s.link, pieceAt Zq.p.X s.link s.digits, KindName.K3⟩ := by
  unfold lookSites at hs
  obtain ⟨y, hy, hsy⟩ := List.mem_filterMap.1 hs
  obtain ⟨_, _, f3, f4, f5, _, _, _⟩ := site_facts _ _ y s hsy
  unfold K3Lot.addresses at hy
  obtain ⟨j, _, hy⟩ := List.mem_flatMap.1 hy
  obtain ⟨e, _, rfl⟩ := List.mem_map.1 hy
  rw [f5, f3, f4]

/-- **The site's link is below 25; at the written border's number stands the site's place; the two
texts of the piece agree.** Conditional on `P5J.AtMgA`, the site, and a sub-protocol of the lookups'
lot at the site's place. No instance of these hypotheses is exhibited in this file. -/
theorem site_border (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl) (hin : lot ∈ K3Lot.hear Zp)
    (hlp : lot.place = s.at_.place) :
    s.link < 25 ∧ P5J.At.ps[borderOf s.link s.digits]? = some s.at_.place ∧
      pieceAt Zp.p.X s.link s.digits = pieceOf s.link s.digits := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hpl := site_place Zp s hs
  have hL : K3Lot.lot Zp ∈ onlineFirstChainBlockTables Zp := by simp [onlineFirstChainBlockTables]
  have hkind : lot.place.kind ≠ KindName.frame := by
    rw [hlp, hpl]
    show KindName.K3 ≠ KindName.frame
    decide
  obtain ⟨m, hm, hmp⟩ := ProofFile.Honest.AtPlace.stands_in_segment O hL (b := lot)
    (show lot ∈ (K3Lot.lot Zp).blocks Bs.G₀ from hin) hkind (l := s.link) (by rw [hlp, hpl])
  have hmem : s.at_.place ∈ P5J.At.ps := by
    rw [← P5J.At.places_paid h.scope h.reads h.laid]
    exact List.mem_map.2 ⟨m, hm, hmp.trans hlp⟩
  obtain ⟨l, hl, d, e⟩ := k3_place_full hmem (by rw [hpl])
  rw [hpl] at e
  have e1 : s.link = l := by
    have := congrArg Place.link e
    exact Option.some.inj this
  have e2 : pieceAt Zp.p.X s.link s.digits = pieceOf l d := congrArg Place.piece e
  subst e1
  have e3 := sort_of_piece _ _ _ _ e2
  subst e3
  refine ⟨hl, ?_, e2⟩
  rw [hpl, e2]
  exact places_are_k3 hl s.digits

end

/-! ## 3 What remains a hypothesis -/

/-- **The hypotheses that remain**, at a public part, a first chain, a list of halves, a site, a
sub-protocol, the summands and the seat's reader of the input. -/
structure SiteRest {W₀ Rc Xi Tr Xo Wj : Type} (Zp : Pub) (cF : Chain TS ProofFile.Cl)
    (hs : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xo)) (s : Site)
    (lot : Block TS ProofFile.Cl) (J : LookJobs Wj) (wit : Local W₀ Rc Xi Tr → Wj) : Prop where
  /-- a sub-protocol of the lookups' lot stands at the site's place -/
  inLot : lot ∈ K3Lot.hear Zp
  lotPlace : lot.place = s.at_.place
  /-- the list of halves holds the lookup's seated row at the site's place -/
  half : hs.find? (fun g => g.place == s.at_.place) =
    some (proverSideOfLookupInChainAtOneOwner ⟨ptsOf, pointsAt⟩ J wit s.at_)
  /-- four tests with code on public data -/
  fits : siteFits cF.blocksInOrder s = true
  ok : s.at_.face.ok = true
  shapeIs : (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true
  usedIs : (!s.digits || s.caller == .head ||
    usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true

/-! ## 4 The theorem -/

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **`SiteAt` holds at the first chain's letters set to the library's own, at the written number of
the border in front of the lookup.** Conditional on `P5J.AtMgA`, the site, and `SiteRest`. At the
full size alone. No instance of these hypotheses is exhibited in this file. -/
theorem siteAt_lettersAt (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {Bk : ProverCoinCounts}
    {W₀ Rc Tr Xo Wj : Type}
    (hs : List (Placed (Local W₀ Rc ProofFile.Inst Tr) (Local W₀ Rc ProofFile.Inst Tr) Xo))
    (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
    (stored : Local W₀ Rc ProofFile.Inst Tr → Nat → Nat → Option (List UInt64))
    (ans : Nat → Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (test : Nat → TS → Option String)
    (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop) (item n₁ n₂ : Nat)
    (valid : Local W₀ Rc ProofFile.Inst Tr → Prop) (rides : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop)
    (keeps : Nat → TS → TS → Prop) (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (J : LookJobs Wj) (wit : Local W₀ Rc ProofFile.Inst Tr → Wj)
    (R : SiteRest Zp cF hs s lot J wit) :
    ∃ Bs, SiteAt (lettersAt h hs Q stored ans test carryX item n₁ n₂ valid rides keeps)
      (borderOf s.link s.digits) Zp Bs cF s lot J wit h.𝔇.sent h.𝔇.l3 := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨hl, hb, hpc⟩ := site_border h s hsite lot R.inLot R.lotPlace
  have hP : blockPlaces cF.blocksInOrder = P5J.At.ps := P5J.At.places_paid h.scope h.reads h.laid
  have hat : ∀ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk → blk.place = s.at_.place := by
    intro blk hk
    have e : (blockPlaces cF.blocksInOrder)[borderOf s.link s.digits]? = some blk.place := by
      unfold blockPlaces
      rw [List.getElem?_map, hk]
      rfl
    rw [hP, hb] at e
    exact (Option.some.inj e).symm
  obtain ⟨blk0, hblk0⟩ : ∃ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk := by
    have e : (blockPlaces cF.blocksInOrder)[borderOf s.link s.digits]? = some s.at_.place := by rw [hP, hb]
    unfold blockPlaces at e
    rw [List.getElem?_map] at e
    obtain ⟨blk, hk, _⟩ := Option.map_eq_some_iff.1 e
    exact ⟨blk, hk⟩
  have hplan : ∀ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk → blk.planOk = true :=
    fun blk hk => IM.plan_flat O h.laid.planOk blk (List.mem_of_getElem? hk)
  have hpay := fun blk (hk : cF.blocksInOrder[borderOf s.link s.digits]? = some blk) =>
    member_plan_site _ _ _ _ _ Zp Bs base cF _ _ O s hsite lot blk R.inLot R.lotPlace
      (List.mem_of_getElem? hk) ((hat blk hk).trans R.lotPlace.symm) (hplan blk hk)
  refine ⟨Bs, ?_⟩
  exact
    { flat := rfl
      site := hsite
      inLot := R.inLot
      lotPlace := R.lotPlace
      place := fun blk hk => (hat blk hk).trans R.lotPlace.symm
      plan := hplan
      rounds := fun blk hk => (hpay blk hk).1
      oracles := fun blk hk => (hpay blk hk).2.1
      entries := (hpay blk0 hblk0).2.2
      half := fun blk hk => by
        show hs.find? (fun g => g.place == blk.place) = _
        rw [hat blk hk]
        exact R.half
      base := base_site_nodup cF.blocksInOrder s _ blk0 R.fits hblk0 (hat blk0 hblk0)
        (by
          show (blockPlaces cF.blocksInOrder).Nodup
          rw [hP]
          exact ps_nodup)
      ok := R.ok
      shapeIs := R.shapeIs
      usedIs := R.usedIs
      k3At := VerifiableInference.OnPublicFiles.k3At_mgAll h.𝔇 mgBase
      lookIn := by
        show VerifiableInference.Desc.First.Pub.lookIn s.link (pieceAt Zp.p.X s.link s.digits) ∈
          ((pubSets (mgAll h.𝔇 mgBase).more linksFull (flatPlacesOf linksFull true))[
            borderOf s.link s.digits]?).getD []
        rw [mgAll_more_closed h.𝔇 mgBase rfl, hpc]
        cases hd : s.digits with
        | false => exact (k3_open_calls hl).1
        | true => exact (k3_open_digits hl).2.1 }

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.k3AllB_full
#print axioms ProofFile.Honest.K3.Law.AtThr.ps_nodup
#print axioms ProofFile.Honest.K3.Law.AtThr.k3_place_full
#print axioms ProofFile.Honest.K3.Law.AtThr.sort_of_piece
#print axioms ProofFile.Honest.K3.Law.AtThr.site_place
#print axioms ProofFile.Honest.K3.Law.AtThr.site_border
#print axioms ProofFile.Honest.K3.Law.AtThr.siteAt_lettersAt
