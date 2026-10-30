-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/AtLink.lean: the lookups' theorems for the files that
call them, stated at a link's number under the library's hypothesis `P5J.AtMgA`
(Johnson/P5J/MgAtAll.lean). What each of these theorems assumes on the description's return, the
lot's sub-protocol and the chain's member is shown here from that hypothesis alone; `keeps_at_link`
and six of the eight theorems at a site keep further hypotheses, listed below. Theorems: each joins
earlier ones; no definition, no new argument.

Terms. Honest/K3/GLOSSARY.md. In this file: `borderOf l d` (Johnson/Desc/Sound/MgAt/K3Open.lean) is
the number of the border in front of link l's lookup, and `IM.k3Place l d` (Johnson/IMR/K3Seat.lean)
is that lookup's place, written out. The sort d is false for the lookup on the calls and true for
the lookup on the digits. An accepting step of a member is `StepYes`
(Johnson/Top/H0/Walk/Reach.lean). "keeps" is the field keeps of `Thread` (Honest/Thread/Thr.lean).
`Carries` and `Returns` are definitions of Honest/Thread/Shape.lean.

What is shown.
Helpers, for the theorems below and for other files:
  `piece_head`, `site_place_head`: a site's place is `IM.k3Place` at the site's link and sort.
  `lot_at_link`: at a link l below 25 and either sort d: the description returns; a sub-protocol of
    the lot stands at `IM.k3Place l d`; whatever stands at the border `borderOf l d` in the first
    chain's flat list is a member at that place and passes its test on the plan.
  `site_hub`: the same at a site's own link and sort.
Theorems without a site in the statement:
  `look_rest_link`, `merged_link`: what holds behind an accepting step of the member at the border
    of link l's lookup on the calls: the conclusions of `look_rest_at`
    (Honest/K3/Law/Thread/LookRest.lean) and of `merged_at` (Honest/K3/Law/Thread/MergedPoint.lean).
  `keeps_at_link`: the lookups' clause of "keeps", where "keeps" is given by the place's kind
    (`kpBy`, Honest/Thread/KeepsBy.lean), at all fifty borders.
Theorems at a site. A caller takes one site from `site_there_head`
(Honest/K3/Law/Thread/SiteThereHead.lean) and calls them all at it. Each is a theorem of another
file under Honest/K3/Law/Thread/, taken at the border. Beside `h`, `hs`, `hl` and the site's sort
(`hd`) it keeps these hypotheses:
  `heard_shape_link` (`heard_shape_layers`, PutFo.lean): the caller is the layers; the test
    `shapeIsFs` passes.
  `carries_calls_link` (`carries_calls`, CarriesCalls.lean): the guards at the border are `callsG`.
  `returns_calls_link` (`returns_calls`, ReturnsLook.lean): the face's test passes; the test on the
    layers' shape passes; the guards are `callsG`.
  `carries_digits_link` (`carries_digits`, CarriesDigits.lean): what stands behind the lookup is
    `quietDigits`; the guards are `digitsG`.
  `returns_digits_link` (`returns_digits`, ReturnsLook.lean): the caller is not the head; the face's
    test passes; the test on the slots in use passes; the guards are `digitsG`.
  `back_g_link` (`member_back_g`, PutG.lean), `back_cEnd_link` (`member_back_cEnd`,
    CEndBelow.lean): none.
  `stands_link` (`stands_member`, StandsBehind.lean), of either sort: `fitsVia`, `okRoundsE` and
    `k3OnIn` pass.

What `keeps_at_link` says at the digits. `k3KeepsAt Z p` (Honest/K3/Law/Thread/K3KeepsAt.lean)
speaks of every site of `lookSites Z` at the place p: where no site stands at p the clause is empty.
As a proof of the lookups' clause of "keeps" the theorem is whole at all fifty borders: it shows the
clause, whatever the clause says. As a sentence on the two states it has content at the 25 borders
on the calls under `P5J.AtMgA` alone (`site_calls_head`, SiteThereHead.lean); at the 25 on the
digits only where a site stands there, for which `site_there_head` assumes `hr`: `rngIn`
(Honest/K3/Lot.lean) returns a number at the link. Since this was written `hr` is shown under
`P5J.AtMgA`, and with it a site at each of the 25 borders on the digits: `site_digits_paid`
(RngWrittenHolds.lean), `site_digits` (RngHeadPaid.lean), `site_at_all_fifty` (SiteAllFifty.lean).

Hypotheses that remain.
  `h`: the library's hypothesis `P5J.AtMgA`.
  `hl`: the link's number is below 25.
  `hf`: (in `keeps_at_link`) the clause of the family f at the kind K3 is `k3KeepsAt Zp`.
  `hs`, `hd`: (in the theorems at a site) s is a site of the public part (`lookSites Zp`); its sort.
  The further hypotheses of the theorems at a site, as listed above: `hc`: the site's caller is the
    layers, or is not the head; `hg`: the letter g at the border is the lookups' own; `hok`, `hT2`,
    `hT3`: three tests with code on public data; `hq`: which step without a round `quietAt` yields.
  `hf`: (in `heard_shape_link`) shapeIsFs Zp.p.X s = true.
No test on the table of places is assumed here: a site on the digits is the caller's to bring.

Imported: Honest/Thread/KeepsBy.lean, Honest/Thread/Thr.lean and Honest/Thread/Shape.lean.

Users. `site_hub` is called in Honest/K3/Law/Thread/CallsHeardLink.lean and
Honest/K3/Shape/ClaimAtHeadLink.lean [not in this library], among others; `lot_at_link` in
Honest/K3/Law/Thread/KeepsThread.lean; `back_g_link` in Honest/K3/Law/Thread/AttBackHead.lean;
`carries_digits_link` in Honest/K3/Law/Thread/QuietAtLink.lean. That a member stands at each of the
fifty borders is `member_at_link` (Honest/K3/Law/Thread/AtLinkThere.lean).
Honest/K3/Law/Thread/QuietAtHeadLink.lean imports this file too.

Limits. At the full size alone: that limit comes with `P5J.AtMgA`. Each theorem has the limits of
the theorem that it is taken from. `look_rest_link` and `merged_link` conclude under "the state
behind stands in a layers' link and holds a structure of the lookup on the calls": at a link of
another sort they say nothing. No instance of these hypotheses is exhibited in this file.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LookRest
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.MergedPoint
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PutFo
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.PutG
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CEndBelow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesCalls
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriesDigits
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ReturnsLook
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.StandsBehind
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.K3KeepsAt
import Johnson.Desc.ProofFile.Honest.Thread.KeepsBy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open OnBytes.Model (Fork lastOf Reading)
open VerifiableInference.Desc (Block Chain FileDescription Place KindName OpenedColumn)
open VerifiableInference.Desc.K3 (pieceAt seatCalls quietAt quietDigits k3OnIn)
open VerifiableInference.Desc.K3.Law (hearVia fitsVia)
open VerifiableInference.Desc.First.Look (sameShape)
open VerifiableInference.Desc.First.Shape (ChainSh chainSh)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open VerifiableInference.OnPublicFiles (okRoundsE K3Stands)
open Johnson.Desc.First.Walk.Tied (StepYes)
open OnBytes.Maker (WholeD)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-! ## 1 The helpers -/

/-- Under `P5J.AtMgA` the two texts of a lookup's piece agree: `pieceAt`
(Johnson/Desc/First/Look/K3Own.lean) and the piece of `IM.k3Place l d`. -/
theorem piece_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (d : Bool) :
    pieceAt Zp.p.X l d = (IM.k3Place l d).piece := by
  cases d with
  | false => exact (P5J.k03_pieceAt h.toAtMg l).symm
  | true => exact (P5J.k03_pieceAt_dig h.toAtMg l).symm

/-- Under `P5J.AtMgA` a site's place is `IM.k3Place` at the site's link and sort. -/
theorem site_place_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site)
    (hs : s ∈ lookSites Zp) : s.at_.place = IM.k3Place s.link s.digits := by
  rw [site_place Zp s hs, piece_head h]

/-- **At a link below 25 and either sort**: the description returns; a sub-protocol of the lot
stands at `IM.k3Place l d`; whatever stands at the border `borderOf l d` is a member at that place
and passes its test on the plan. Conditional on `P5J.AtMgA`. No instance of these hypotheses is
exhibited in this file. -/
theorem lot_at_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) :
    ∃ (Fd : FileDescription Inst) (Bs : PureBase) (base : List (Block TS ProofFile.Cl)) (A : SharedSeat)
      (B : SecondSeat) (lot : Block TS ProofFile.Cl),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL Fd Zp Bs base cF A B ∧
      lot ∈ (K3Lot.lot Zp).blocks Bs.G₀ ∧ lot.place = IM.k3Place l d ∧
      ∀ blk, cF.blocksInOrder[borderOf l d]? = some blk →
        blk ∈ cF.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  obtain ⟨b', hb', ep, _, _⟩ := lot_spot_head h.scope h.reads O h.laid.planOk l hl d
  refine ⟨_, Bs, base, _, _, b', O, hb', ep, fun blk hblk => ?_⟩
  have hmem := List.mem_of_getElem? hblk
  refine ⟨hmem, ?_, IM.plan_flat O h.laid.planOk blk hmem⟩
  have hp : P5J.At.ps[borderOf l d]? = some blk.place := by
    rw [← P5J.At.places_paid h.scope h.reads h.laid]
    show (cF.blocksInOrder.map (·.place))[borderOf l d]? = _
    rw [List.getElem?_map, hblk]
    rfl
  rw [ep]
  exact Option.some.inj (hp.symm.trans (places_are_k3 hl d))

/-- The same at a site's own link and sort. Conditional on `P5J.AtMgA` and the site. -/
theorem site_hub (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp)
    (hl : s.link < 25) :
    ∃ (Fd : FileDescription Inst) (Bs : PureBase) (base : List (Block TS ProofFile.Cl)) (A : SharedSeat)
      (B : SecondSeat) (lot : Block TS ProofFile.Cl),
      IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL Fd Zp Bs base cF A B ∧
      lot ∈ (K3Lot.lot Zp).blocks Bs.G₀ ∧ lot.place = s.at_.place ∧
      ∀ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk →
        blk ∈ cF.blocksInOrder ∧ blk.place = lot.place ∧ blk.planOk = true := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hp, hm⟩ := lot_at_link h s.link hl s.digits
  exact ⟨Fd, Bs, base, A, B, lot, O, hb, hp.trans (site_place_head h s hs).symm, hm⟩

/-! ## 2 Theorems without a site in the statement -/

/-- **Behind an accepting step of the member at the border of link l's lookup on the calls**: the
two conclusions of `look_rest_at`. Conditional on `P5J.AtMgA`. No instance of these hypotheses is
exhibited in this file. -/
theorem look_rest_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[borderOf l false]? = some blk →
      ∀ (ft : Nat) (s₀ s' : TS), StepYes ft blk s₀ s' →
        ∀ a fo, s'.here = .lay a → a.fo = some fo →
          (∀ k Zq, (lastOf fo.zx k).toOption = some Zq →
            ∃ ends, (fo.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
              ends.all (· == Zq) = true) ∧
          fo.e.size = fo.shape.NC := by
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_calls_head h l hl
  subst e1
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [e2] at hm
  intro blk hblk
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  exact look_rest_at _ _ _ _ Fd Zp Bs base cF A B O s hs e2 lot hb hbs blk m1 m2 m3

/-- The like with the conclusion of `merged_at`. Conditional on `P5J.AtMgA`. No instance of these
hypotheses is exhibited in this file. -/
theorem merged_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25) :
    ∀ blk, cF.blocksInOrder[borderOf l false]? = some blk →
      ∀ (ft : Nat) (s₀ s' : TS), StepYes ft blk s₀ s' →
        ∀ a fo, s'.here = .lay a → a.fo = some fo → ∀ k, k ≤ fo.shape.dT →
          ∃ Zq ends, (lastOf fo.zx k).toOption = some Zq ∧
            (fo.zk.mapM fun zk => (lastOf zk k).toOption) = some ends ∧
            ends.all (· == Zq) = true := by
  obtain ⟨s, hs, e1, e2, _, _⟩ := site_calls_head h l hl
  subst e1
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [e2] at hm
  intro blk hblk ft s₀ s' ⟨R, c, _, hstep⟩
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  exact merged_at _ _ _ _ Fd Zp Bs base cF A B O s hs e2 lot blk hb hbs m1 m2 m3 ft s₀ s' _ R c
    hstep

/-- **The lookups' clause of "keeps", where "keeps" is given by the place's kind, at all fifty
borders.** Conditional on `P5J.AtMgA`, and on the family's clause at the kind K3 being the lookups'
(`hf`). Where no site stands at the place the clause is empty: see this file's head. No instance of
these hypotheses is exhibited in this file. -/
theorem keeps_at_link (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (l : Nat) (hl : l < 25)
    (d : Bool) (f : KindName → Place → TS → TS → Prop) (hf : f .K3 = k3KeepsAt Zp) :
    ∀ blk, cF.blocksInOrder[borderOf l d]? = some blk →
      ∀ (ft : Nat) (t t' : TS), StepYes ft blk t t' → kpBy f blk.place t t' := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hp, hm⟩ := lot_at_link h l hl d
  intro blk hblk ft t t' ⟨R, c, _, hstep⟩
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  have hk : blk.place.kind = KindName.K3 := by rw [m2, hp]
  rw [kpBy_at f hk, hf]
  exact k3KeepsAt_pays _ _ _ _ Fd Zp Bs base cF A B O blk.place lot blk hb m2.symm m1 m2 m3 ft t t'
    _ R c hstep

/-! ## 3 Theorems at a site -/

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) (s : Site) (hs : s ∈ lookSites Zp)
  (hl : s.link < 25)

include h hs hl

/-- `heard_shape_layers` at the border. It keeps: the caller is the layers; the test `shapeIsFs`
passes. -/
theorem heard_shape_link (hd : s.digits = false) (hc : s.caller = .layers)
    (hf : shapeIsFs Zp.p.X s = true) :
    ∀ blk, cF.blocksInOrder[borderOf s.link false]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∀ al fo', sj'.here = .lay al → al.fo = some fo' → fo'.shape = Zp.p.X.y.fo := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  exact heard_shape_layers _ _ _ _ Fd Zp Bs base cF A B O s hs hd hc hf lot blk hb hbs m1 m2 m3 ft
    sj sj' n rs c hstep

/-- `carries_calls` at the first chain's flat list and the border. It keeps: the guards. -/
theorem carries_calls_link (hd : s.digits = false) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (borderOf s.link false) = callsG s.shape s.p.first) :
    Carries cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link false) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  exact carries_calls _ _ _ _ Fd Zp Bs base cF A B O s hs hd lot hb hbs cF.blocksInOrder ft _ hm g vals hg

/-- `returns_calls` likewise. It keeps: the face's test; the test on the layers' shape; the guards.
-/
theorem returns_calls_link (hd : s.digits = false) (hok : s.at_.face.ok = true)
    (hT2 : (s.digits || s.caller != .layers || sameShape s.shape Zp.p.X.y.fo) = true) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (borderOf s.link false) = callsG s.shape s.p.first) :
    Returns cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link false) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  exact returns_calls _ _ _ _ Fd Zp Bs base cF A B O s hs hd lot hb hbs hok hT2 cF.blocksInOrder ft _ hm g
    vals hg

/-- `carries_digits` likewise. It keeps: what stands behind the lookup is `quietDigits`; the
guards. -/
theorem carries_digits_link (hd : s.digits = true) (used claims : Nat)
    (hq : quietAt Zp.p.X s.link true = some (quietDigits used claims)) (ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (borderOf s.link true) = digitsG s.shape s.p.first used claims) :
    Carries cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link true) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  exact carries_digits _ _ _ _ Fd Zp Bs base cF A B O s hs hd lot hb hbs used claims hq cF.blocksInOrder ft
    _ hm g vals hg

/-- `returns_digits` likewise. It keeps: the caller is not the head; the face's test; the test on
the slots in use; the guards. -/
theorem returns_digits_link (hd : s.digits = true) (hc : s.caller ≠ .head)
    (hok : s.at_.face.ok = true)
    (hT3 : (!s.digits || s.caller == .head ||
      usedAt Zp.p.X s == some (s.p.first + s.at_.face.slots)) = true) (used claims ft : Nat)
    (g : Nat → ChainSh → Except String ChainSh)
    (vals : Nat → TS → List Fmt.RoundView → List (List (Nat × List UInt64)) → Bool)
    (hg : g (borderOf s.link true) = digitsG s.shape s.p.first used claims) :
    Returns cF.blocksInOrder ft ⟨ChainSh, chainSh, g, vals⟩ (borderOf s.link true) := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  exact returns_digits _ _ _ _ Fd Zp Bs base cF A B O s hs hd hc lot hb hbs hok hT3 used claims
    cF.blocksInOrder ft _ hm g vals hg

/-- `member_back_g` at the border. It keeps no further hypothesis. -/
theorem back_g_link (hd : s.digits = false) :
    ∀ blk, cF.blocksInOrder[borderOf s.link false]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ F H G, (seatCalls K3Lot.ofForm).fork sj = some F ∧ hearVia s.p F rs = some (H, G) ∧
          ∀ att, sj'.here = .att att → att.g = some H := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  exact member_back_g _ _ _ _ Fd Zp Bs base cF A B O s hs hd lot blk hb hbs m1 m2 m3 ft sj sj' n rs
    c hstep

/-- `member_back_cEnd` at the border. It keeps no further hypothesis. -/
theorem back_cEnd_link (hd : s.digits = false) :
    ∀ blk, cF.blocksInOrder[borderOf s.link false]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) →
        ∃ F H G, (seatCalls K3Lot.ofForm).fork sj = some F ∧ hearVia s.p F rs = some (H, G) ∧
          (seatCalls K3Lot.ofForm).heard sj' = some H ∧
          (seatCalls K3Lot.ofForm).fork sj' = some G ∧ H.cEnd.ents.isEmpty = true ∧
          ∀ y ∈ H.cEnd.slots.toList, F.next ≤ y.1 ∧ y.1 < G.next := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  rw [hd] at hm
  intro blk hblk ft sj sj' n rs c hstep
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  exact member_back_cEnd _ _ _ _ Fd Zp Bs base cF A B O s hs hd lot blk hb hbs m1 m2 m3 ft sj sj' n
    rs c hstep

/-- `stands_member` at the border, of either sort. It keeps: `fitsVia`, `okRoundsE` and `k3OnIn`
pass. -/
theorem stands_link :
    ∀ blk, cF.blocksInOrder[borderOf s.link s.digits]? = some blk →
      ∀ (ft : Nat) (sj sj' : TS) (n : Nat) (rs : List Fmt.RoundView) (c : List OpenedColumn),
        blk.step ft sj rs c = .ok (sj', n) → fitsVia s.p = true → okRoundsE rs = true →
        k3OnIn s.p sj = true → ∀ lm : Nat,
        ∃ F' g, (seatOf K3Lot.ofForm s.digits).fork sj' = some F' ∧
          (seatOf K3Lot.ofForm s.digits).heard sj' = some g ∧
          K3Stands g.shape lm s.p.first Reading.gl g F' := by
  obtain ⟨Fd, Bs, base, A, B, lot, O, hb, hbs, hm⟩ := site_hub h s hs hl
  intro blk hblk ft sj sj' n rs c hstep hfv hok hin lm
  obtain ⟨m1, m2, m3⟩ := hm blk hblk
  exact stands_member _ _ _ _ Fd Zp Bs base cF A B O s hs lot blk hb hbs m1 m2 m3 ft sj sj' n rs c
    hstep hfv hok hin lm

end

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.piece_head
#print axioms ProofFile.Honest.K3.Law.AtThr.site_place_head
#print axioms ProofFile.Honest.K3.Law.AtThr.lot_at_link
#print axioms ProofFile.Honest.K3.Law.AtThr.site_hub
#print axioms ProofFile.Honest.K3.Law.AtThr.look_rest_link
#print axioms ProofFile.Honest.K3.Law.AtThr.merged_link
#print axioms ProofFile.Honest.K3.Law.AtThr.keeps_at_link
#print axioms ProofFile.Honest.K3.Law.AtThr.heard_shape_link
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_calls_link
#print axioms ProofFile.Honest.K3.Law.AtThr.returns_calls_link
#print axioms ProofFile.Honest.K3.Law.AtThr.carries_digits_link
#print axioms ProofFile.Honest.K3.Law.AtThr.returns_digits_link
#print axioms ProofFile.Honest.K3.Law.AtThr.back_g_link
#print axioms ProofFile.Honest.K3.Law.AtThr.back_cEnd_link
#print axioms ProofFile.Honest.K3.Law.AtThr.stands_link
