-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/FormRest.lean: the kind "lookup" (K3): WHAT "THE FORM
BEHIND A LOOKUP'S MEMBER" STILL ASKS AT THE FIRST CHAIN'S LETTERS, IN ONE RECORD OF PREMISES A SORT
OF MEMBER; and that form from the record. The letters L are a variable.

  `FormRestDigits`   the premises of `form_site_digits` (BehindSite.lean) beside `SiteAt`,
                     `HeadReturns`, the thread, the challenges' fit and the step: name for name
  `FormRestDigitsS`  the same with its three last fields asked from the pair alone: lighter
  `FormRestCalls`    the same of `form_site_callsR` (BehindSiteCalls.lean), with hst, from which
                     "reached" is had at the pair (`reach_thrS`, BehindSaid.lean)
  `formOf_digits`    the form at b + 1 behind the member's step, from the thread
  `formOf_digitsS`, `formOf_calls`   the same from the pair: the thread with `SaidOk` beside it

They are definitions: premises' forms; and two calls of laws that lie. The conclusions have the form
of the premise hFormOf of RidersAtSite.lean, RidersAtPlace.lean and RidersAtHead.lean, without the
two facts that these hand to its payer: they are not spent.

THE FIELDS, AND WHAT WOULD PAY EACH AT THE LETTERS `lettersAt` (Honest/Thread/FirstAt.lean), whose
meaning `MgP` is the library's composed one (`mgAtAll h`, that is `mgAll` at the head's data and the
base meaning). Where a field speaks of `L.mgP`: that is `honest L.MgP …` (Honest/Thread/First.lean),
which turns five other fields: `pub`, `pubP` and `more` are `MgP`'s, by its text. The laws named lie
in Johnson/Desc/Sound/MgAt/. OF EACH THE STATEMENT WAS READ, but where it says otherwise. CALLED IN
THIS FOLDER SINCE (FormRestAtHead.lean): `heldReads_mgAll`, `inOrderReads_mgAll`, `hfit_mgAll`,
`hTab_mgAll`; for othersP and hRest the laws beneath the two tops (FormRestAtHead.lean,
FormRestAtHeadRest.lean [not in this library]: their heads say which).
  hHe       `heldReads_mgAll` (K3At.lean): no premise
  hIO       `inOrderReads_mgAll` (K3At.lean): from the same of the base meaning
  hTab      `hTab_mgAll` (K3Tests.lean)          hfit   `hfit_mgAll` (K3Tests.lean)
  othersP   `othersP_dig_mgAll` (K3DigitsSaid.lean): its proof spends no hand on the step
  hRest     `othersPub_dig_mgAll` (K3DigitsOthers.lean): ALL BUT THE ITEMS formsIn, which it takes
            as a premise of its own (hForms): OF OTHER KINDS' ITEMS AT THE DIGITS THESE ARE LEFT;
            hObj is one of them
  hk        `site_border` (SiteAtLetters.lean)    hled   by unfolding (the frame's `head_ledgerB`)
  bPub, bPubP   the like at the calls (K3CallsOthers.lean, K3CallsSaid.lean): names alone seen;
            since: bPubP: `bPubP_at` (FormRestAtHeadFill.lean [not in this library])
  hk1, hfitS, hsub, hpcT, hlook, hsx, hfree, hns, hbf, hn, askFresh, hst: public facts on places,
            links and stored words. Since: ten of the twelve have a theorem in
            FormRestAtHeadFacts.lean, at `lettersAt` under the head (`hk1_at`: hk1, hfitS;
            `hsub_at`: hsub, hpcT; `hlook_at`; `hsx_at`; `hfree_at`; `hbf_at`; `hn_at`;
            `askFresh_at`); hns and hst: none in this folder

`SiteAt` has the field half: the list of halves holds, at the site's place, the elder row `proverSideOfLookupInChainAtOneOwner`
at these summands. Who pays the field, each at the fast summands and under hypotheses on the list:
where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot` (HalfAtSite.lean
[not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean [not in this library]); where it
holds a lot with the halves of `theLotInst` at the public part: `half_like_ok`, `half_field_like`
(HalfOfLotLike.lean [not in this library]). A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. A record can hold a field that cannot be had: nothing here shows that it cannot. No instance
of these hypotheses is exhibited in this file. Nothing on soundness, completeness or any other
property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.BehindSaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.AtThr
open VerifiableInference.Desc (Block Chain FileDescription Place OpenedColumn Oracle fieldPrimeWord)
open VerifiableInference.Desc.First (ModelPart pubSets openSets start shift sameStand bookFit pubFit
  pubStep pubRowM pubOfItems stepOpen)
open VerifiableInference.Desc.First.Look (P Sent lookAt)
open VerifiableInference.Desc.Sound (MsgT Frame onQ)
open VerifiableInference.OnPublicFiles (K3Letters InOrderReads HeldReads SameBut paidCallsR digTableB
        k3Like)
open ProofFile.Honest.FirstThread (Letters)

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo Pp Cells Tok Wj : Type}

/-- **WHAT THE FORM BEHIND A LOOKUP ON THE DIGITS STILL ASKS.** ITS THREE LAST FIELDS ARE ASKED FROM
THE THREAD ALONE: where their payer wants the library's "reached", TAKE `FormRestDigitsS`. -/
structure FormRestDigits (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT) (b : Nat)
    (Z : Pub) (s : Site) (a' : Place) (sub : ModelPart) (x : PlaceL) (told : List (List Oracle)) :
    Prop where
  hIO : InOrderReads L.MgP
  hHe : HeldReads L.MgP
  hk : L.ps[b]? = some s.at_.place
  hk1 : L.ps[b + 1]? = some a'
  hfitS : sameStand L.links s.at_.place a' = true
  hsub : L.links[s.link]? = some sub
  hpcT : s.at_.place.piece = 7 + shift sub
  hTab : digTableB L.MgP.more L.links L.ps b s.at_.place s.link (shift sub) = true
  hlook : lookAt Z.p.X s.link true = some x
  hbf : bookFit L.N L.ps told = true
  hn : told[b]? = some []
  hObj : AtStep L b fun z _ t' =>
    L.mgP.pub (.formsIn s.link (7 + shift sub) "objects") (z, t') = true
  hRest : AtStep L b fun z _ t' =>
    ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.mgP.more L.links s.at_.place) ++
      pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
        (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
    k3Like r = false → r ≠ .formsIn s.link (7 + shift sub) "objects" →
      L.mgP.pub r (z, t') = true
  othersP : AtStep L b fun z _ t' =>
    ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
      (pubRowM L.mgP.more L.links s.at_.place),
    (∀ j, r ≠ .left j) → (∀ j, r ≠ .leftOn j) → L.mgP.pubP r (z, t')

/-- **THE SAME WITH ITS THREE LAST FIELDS ASKED FROM THE PAIR ALONE**: a lighter record. -/
structure FormRestDigitsS (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT) (b : Nat)
    (Z : Pub) (s : Site) (a' : Place) (sub : ModelPart) (x : PlaceL) (told : List (List Oracle)) :
    Prop where
  hIO : InOrderReads L.MgP
  hHe : HeldReads L.MgP
  hk : L.ps[b]? = some s.at_.place
  hk1 : L.ps[b + 1]? = some a'
  hfitS : sameStand L.links s.at_.place a' = true
  hsub : L.links[s.link]? = some sub
  hpcT : s.at_.place.piece = 7 + shift sub
  hTab : digTableB L.MgP.more L.links L.ps b s.at_.place s.link (shift sub) = true
  hlook : lookAt Z.p.X s.link true = some x
  hbf : bookFit L.N L.ps told = true
  hn : told[b]? = some []
  hObj : AtStepS L b fun z _ t' =>
    L.mgP.pub (.formsIn s.link (7 + shift sub) "objects") (z, t') = true
  hRest : AtStepS L b fun z _ t' =>
    ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.mgP.more L.links s.at_.place) ++
      pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
        (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
    k3Like r = false → r ≠ .formsIn s.link (7 + shift sub) "objects" →
      L.mgP.pub r (z, t') = true
  othersP : AtStepS L b fun z _ t' =>
    ∀ r ∈ pubStep ((pubSets L.mgP.more L.links L.ps)[b]?.getD [])
      (pubRowM L.mgP.more L.links s.at_.place),
    (∀ j, r ≠ .left j) → (∀ j, r ≠ .leftOn j) → L.mgP.pubP r (z, t')

/-- **WHAT THE FORM BEHIND A LOOKUP ON THE CALLS STILL ASKS.** -/
structure FormRestCalls (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT) (b : Nat)
    (Z : Pub) (s : Site) (Fr : Frame) (a' : Place) (sub : ModelPart) (x : PlaceL)
    (nsOf : Nat → Option Nat) (told : List (List Oracle)) : Prop where
  hIO : InOrderReads L.MgP
  hHe : HeldReads L.MgP
  hst : ∀ w i x u, L.stored w i x = some u → ∀ c ∈ u, c < fieldPrimeWord
  hk : L.ps[b]? = some s.at_.place
  hk1 : L.ps[b + 1]? = some a'
  hfitS : sameStand L.links s.at_.place a' = true
  hsub : L.links[s.link]? = some sub
  hpcT : s.at_.place.piece = 2 + shift sub
  hlook : lookAt Z.p.X s.link false = some x
  hsx : (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x).shape = some x.fs
  hled : ∀ j u, L.MgP.pub (.ledger j) u = VerifiableInference.Desc.First.ledgerB u.2
  hfree : ∀ j u, L.MgP.pub (.freeAbove j) u =
    (nsOf j).any fun n => VerifiableInference.Desc.First.freeAboveB n u.2
  hns : nsOf s.link = some (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x).ns
  hbf : bookFit L.N L.ps told = true
  hn : told[b]? = some []
  hfit : pubFit L.MgP.more L.links L.ps = true
  askFresh : VerifiableInference.Desc.First.Pub.linkFresh s.link ∈
    (pubSets L.MgP.more L.links L.ps)[b]?.getD []
  bPub : AtStepS L b fun z _ _ => ∀ u v : FS × Fr.E.Str,
    onQ L.N L.mgP L.links L.ps (fun t => (z, t)) b u → ReachB L b z u → u.1.failed = none →
    AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
      v → SameBut u.1 v.1 →
    ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.MgP.more L.links s.at_.place) ++
        pubOfItems (stepOpen ((openSets L.links L.ps (start L.links))[b]?.getD [])
          (VerifiableInference.Desc.First.rowOf L.links s.at_.place)),
      q ∉ paidCallsR s.link (2 + shift sub) → L.MgP.pub q (z, v.1) = true
  bPubP : AtStepS L b fun z _ _ => ∀ u v : FS × Fr.E.Str,
    onQ L.N L.mgP L.links L.ps (fun t => (z, t)) b u → ReachB L b z u → u.1.failed = none →
    AcceptsCalls K3Lot.ofForm Fr (P.ofPlace (OnBytes.Params.settingOf Z.p.X.P.frame) false x) u
      v → SameBut u.1 v.1 →
    ∀ q ∈ pubStep ((pubSets L.MgP.more L.links L.ps)[b]?.getD [])
        (pubRowM L.MgP.more L.links s.at_.place),
      q ≠ .left s.link → L.MgP.pubP q (z, v.1)

variable {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo Pp Cells Tok MsgT}
  (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub}
  {Bs : PureBase} (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat)
  (B : SecondSeat) (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site}
  {lot : Block FS ProofFile.Cl} {J : LookJobs Wj} {wit : Local W₀ Rc Xi Tr → Wj} {D : Sent}
  {Lk : K3Letters Cells Tok} (hS : SiteAt L b Z Bs ch s lot J wit D Lk)
include O hS

/-- **THE FORM BEHIND A LOOKUP ON THE DIGITS, FROM THE RECORD.** Two hypotheses do not stand in the
theorem's own lines: O (`IM.Open`: the description's return) and hS (`SiteAt`): they come from the
`variable` lines above, by `include O hS`. No instance of these hypotheses is exhibited in this
file. -/
theorem formOf_digits (hH : HeadReturns L b Z s) (hdg : s.digits = true) (Fr : Frame)
    (y₀ : Fr.E.Str) {a' : Place} {sub : ModelPart} {x : PlaceL} {told : List (List Oracle)}
    (F : FormRestDigits L b Z s a' sub x told) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS)
      (m : Mid (Local W₀ Rc Xi Tr) Xo) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn) (s' : FS),
      Thr L.thread b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m E ds y cols s' → L.thread.Form (b + 1) k s' y.2 :=
  fun blk hb k st m E ds y cols s' hA hd hSt =>
    form_site_digits L o pol lay KL Fd base A B O hS hH hdg hb hA hd hSt F.hIO F.hHe Fr y₀ a' F.hk
      F.hk1 F.hfitS sub F.hsub F.hpcT F.hTab F.hlook told F.hbf F.hn
      (F.hObj blk hb k st m E ds y cols s' hA hd hSt)
      (F.hRest blk hb k st m E ds y cols s' hA hd hSt)
      (F.othersP blk hb k st m E ds y cols s' hA hd hSt)

/-- **THE FORM BEHIND A LOOKUP ON THE DIGITS, FROM THE LIGHTER RECORD AND THE PAIR.** Two hypotheses
do not stand in the theorem's own lines: O (`IM.Open`: the description's return) and hS (`SiteAt`):
they come from the `variable` lines above, by `include O hS`. No instance of these hypotheses is
exhibited in this file. -/
theorem formOf_digitsS (hH : HeadReturns L b Z s) (hdg : s.digits = true) (Fr : Frame)
    (y₀ : Fr.E.Str) {a' : Place} {sub : ModelPart} {x : PlaceL} {told : List (List Oracle)}
    (F : FormRestDigitsS L b Z s a' sub x told) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS)
      (m : Mid (Local W₀ Rc Xi Tr) Xo) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn) (s' : FS),
      ThrS L.thread SaidOk b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m E ds y cols s' → L.thread.Form (b + 1) k s' y.2 :=
  fun blk hb k st m E ds y cols s' hAS hd hSt =>
    form_site_digits L o pol lay KL Fd base A B O hS hH hdg hb hAS.1 hd hSt F.hIO F.hHe Fr y₀ a'
      F.hk F.hk1 F.hfitS sub F.hsub F.hpcT F.hTab F.hlook told F.hbf F.hn
      (F.hObj blk hb k st m E ds y cols s' hAS hd hSt)
      (F.hRest blk hb k st m E ds y cols s' hAS hd hSt)
      (F.othersP blk hb k st m E ds y cols s' hAS hd hSt)

/-- **THE FORM BEHIND A LOOKUP ON THE CALLS, FROM THE RECORD AND THE PAIR.** Two hypotheses do not
stand in the theorem's own lines: O (`IM.Open`: the description's return) and hS (`SiteAt`): they
come from the `variable` lines above, by `include O hS`. No instance of these hypotheses is
exhibited in this file. -/
theorem formOf_calls (hdg : s.digits = false) {Fr : Frame} (y₀ : Fr.E.Str) {a' : Place}
    {sub : ModelPart} {x : PlaceL} {nsOf : Nat → Option Nat} {told : List (List Oracle)}
    (F : FormRestCalls L b Z s Fr a' sub x nsOf told) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ (k : Coins Bk) (st : FS)
      (m : Mid (Local W₀ Rc Xi Tr) Xo) (E : Env) (ds : List Fmt.Drawn)
      (y : List Played × Mid (Local W₀ Rc Xi Tr) Xo) (cols : List OpenedColumn) (s' : FS),
      ThrS L.thread SaidOk b k st m E → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m E ds y cols s' → L.thread.Form (b + 1) k s' y.2 :=
  fun blk hb k st m E ds y cols s' hAS hd hSt =>
    form_site_callsR L o pol lay KL Fd base A B O hS hdg hb hAS.1 hd hSt F.hIO F.hHe Fr y₀
      (Reach := ReachB L b (L.pubOf m.st.input.x))
      (reach_thrS (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hb).1) F.hst hAS) a' F.hk F.hk1
      F.hfitS sub F.hsub F.hpcT F.hlook F.hsx F.hled F.hfree F.hns told F.hbf F.hn F.hfit
      F.askFresh (F.bPub blk hb k st m E ds y cols s' hAS hd hSt)
      (F.bPubP blk hb k st m E ds y cols s' hAS hd hSt)

end ProofFile.Honest.K3.Law.AtThr

#print axioms ProofFile.Honest.K3.Law.AtThr.formOf_digits
#print axioms ProofFile.Honest.K3.Law.AtThr.formOf_digitsS
#print axioms ProofFile.Honest.K3.Law.AtThr.formOf_calls
