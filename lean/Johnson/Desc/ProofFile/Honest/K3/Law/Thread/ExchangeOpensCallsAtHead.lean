-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeOpensCallsAtHead.lean: the kind "lookup" (K3):
the frame's share `ExchangeAtS` (Honest/Thread/SharesS.lean) at a lookup ON THE CALLS, at the
frame's letters at the library's head (`lettersHead`, Honest/Thread/FirstHead.lean): at each of the
four items that the table's row opens. Two definitions; six theorems. In the names "headCalls"
says: at these letters, on the calls; a suffix says the sort of the link.

NOT IN FRONT OF A LAW OVER COINS. The ends speak under `ThrS` and the member's step at a run's coins
k, with Said a letter for a predicate on the coins: a condition on the run's coins, which only "the
thread stands at every k" would lift; no file shows that. hRun and R say what the Script's witness,
the hidden input and the prover's list are; the coins are bound inside. The head, hpo, hsite and the
readers' answers are public.

Why. `attention_letters`, `layers_letters` and `head_letters` (ExchangeAllAtLetters.lean) end in the
thread's sentence "the items hold" (`Thread.Items`) of the row's four items AT ONE STEP, from
`LeftAt` and premises on that step. The frame's share binds every step on the thread. Here the
binders of the share stand in front, `LeftAt`, the member's place and the ledger in front are had
from the thread and the step, and what else speaks of the run is asked under one name.

What is shown, at the border of a site s on the calls.
  `piece_headCalls`: the site's place has the piece 2 + shift sub, and so has the library's
    `pieceAt`, sub the sort of the site's link.
  `opens_headCalls_layers`, `opens_headCalls_attention`, `opens_headCalls_link24`: one for each sort
    of link: at every step on the thread the four items hold behind the step. Each calls its law of
    ExchangeAllAtLetters.lean once, with `left_thr_fast` (LeftThr.lean) for `LeftAt`, `SiteAt`'s
    fields for the member's place and `ledger_thr` (LedgerThr.lean) for the ledger in front.
  `AtCalls`: (definition) the premises at one witness, by what the public readers answer at the
    site's link: `AtAttention` at every answer of `attAt`; `AtLayers` at every answer of `layAt` and
    `tlAt`; `AtHead` where the link is `headLink`. At most one of the three speaks
    (`attAt_none_of_layAt`, Johnson/Desc/First/Look/K3PlaceAtCopies.lean; `attAt_head`,
    `layAt_head`, K3HeadFill.lean there).
  `CallsRunHead`: (definition) THE ONE NAMED BUNDLE at a site on the calls: `CallsRunAll`
    (ExchangeCallsAll.lean) at these letters, at the library's own readers, seats and tables, at
    `AtCalls`, at every sort that the letters' list of links gives at the site's link: there is one.
  `opens_headCalls`: the three joined: by the site's link: 24, odd, or even.
  `exchangeAtS_headCalls`: so `ExchangeAtS` at each of the four, at every family Said.

Hypotheses that remain. `hRun`: the bundle: the honest run's own facts at every step on the thread,
on the Script and the prover: nobody's. `R` : `SiteRest` at the fast filling's asked jobs. `hpo`:
the library's test `planesOk` at the site's shape and number of row bits: public. `hsite`, `hd`,
`hsub`: public; in the three by sort also what the public readers answer at the link. `HeadReturns`,
which `left_thr_fast` asks, is empty on the calls (`headReturns_onCalls`, HeadReturnsElse.lean).

Imported. In this folder: ExchangeCallsAll.lean, ExchangeAllAtLetters.lean, LeftThr.lean,
LedgerThr.lean, SiteAtHead.lean, FormRestAtHeadFacts.lean, HeadReturnsElse.lean, LinkLtHead.lean. Of
the frame's authors: Honest/Thread/SharesS.lean. The library's Johnson/P5J/AllItemsAt.lean
(`k03_attAt_some`, `k03_layAt_some`), Johnson/P1K8R/BlindOwesAt.lean (`headLink_at`) and
Johnson/Desc/First/Look/K3PlaceAtCopies.lean.

Users. ExchangeSharesCallsAtHead.lean in this folder.

Beside it. `exchangeAt_rider_layers` (ExchangeRiderLay.lean [not in this library]) ends in the share
at worth "rider" at a layers' link under another premise, hHot. Here that item stands under the
field cubes of `AtLayers`. Neither theorem calls the other.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

`SiteRest` has the field half: the list of halves holds, at the site's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. This pays nothing at a Script: each theorem is a conditional sentence, and every clause of
the bundle is a premise of a law of this folder, moved under a name. The items that the row reads
and leaves are not spoken of. The full size alone. The frame's letter for "keeps" by place is a
variable, Kp: nothing here reads it. No instance of the hypotheses beside the head is exhibited in
this file. Nothing shows that the thread holds at any run: where it holds at none the shares hold
emptily.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeCallsAll
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAllAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LedgerThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormRestAtHeadFacts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.HeadReturnsElse
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.P5J.AllItemsAt
import Johnson.P1K8R.BlindOwesAt
import Johnson.Desc.First.Look.K3PlaceAtCopies

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open OnBytes.Slice (GE)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (attAt layAt pubAt planesOk attAt_none_of_layAt)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (headLink k3SizesAt k3PolicyAt k3AdrAt)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "stepAt" => VerifiableInference.Desc.First.Look.stepOf
local notation "tlAtL" => VerifiableInference.Desc.First.Look.tlAt

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X : Type}
  {W₀' Rc' Xi' Tr' : Type} (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X)
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (cs : List (RiderCl (Local W₀ Rc ProofFile.Inst Tr) TS))
  (Kp : VerifiableInference.Desc.Place → TS → TS → Prop) (w : Local W₀ Rc ProofFile.Inst Tr)

local notation "LH" =>
  lettersHead h H Q test carryX item n₁ n₂ b₀ Vd (ridersOf cs) Kp w

/-- **The piece of a site on the calls**, in the place's own field and in the library's `pieceAt`.
Conditional on the head, the site, a sub-protocol of the lookups' lot at its place, and the link's
sort. -/
theorem piece_headCalls (s : Site) (hsite : s ∈ lookSites Zp) (lot : Block TS ProofFile.Cl)
    (hin : lot ∈ K3Lot.hear Zp) (hlp : lot.place = s.at_.place) (hd : s.digits = false)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub) :
    s.at_.place.piece = 2 + shift sub ∧
      VerifiableInference.Desc.K3.pieceAt Zp.p.X s.link false = 2 + shift sub := by
  obtain ⟨_, _, e3⟩ := site_border h s hsite lot hin hlp
  have hp := (place_at h s hsite lot hin hlp).2
  have hpiece : s.at_.place.piece =
      VerifiableInference.Desc.Sound.MgAt.pieceOf s.link s.digits := by
    rw [hp]
    rfl
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot hin hlp
  have es : sub' = sub := Option.some.inj (h1.symm.trans hsub)
  have hpcT : s.at_.place.piece = 2 + shift sub := by
    rw [h2, es, hd]
    rfl
  refine ⟨hpcT, ?_⟩
  rw [← hd, e3, ← hpiece]
  exact hpcT

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**At a layers' link: at every step on the thread the four items that the row opens hold behind the
step.** Conditional on the head, R, hpo, the public readers' answers and hRun. At the elder row. No
instance of the hypotheses beside the head is exhibited in this file. -/
theorem opens_headCalls_layers
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : layAt Zp.p.X s.link = some x) (ht : tlAtL Zp.p.X s.link = some tl)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunAll (LH) Said (borderOf s.link s.digits) s wit h.𝔇.Rd
      (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (1 + shift sub)
      (fun _ _ a θ hd' mk v => AtLayers s h.𝔇.sent h.𝔇.l3 x tl a θ hd' mk v
        (pubAt Zp.p.X (s.link / stepAt Zp.p.X)))) :
    ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
      (LH).thread.Items [Item.formsT s.link (2 + shift sub) "objects",
        .worth s.link (2 + shift sub) "planes", .worth s.link (2 + shift sub) "keys",
        .worth s.link (2 + shift sub) "rider"] k st' y.2 (En.add y.1) := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, SA, SB, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot _ wit R
  obtain ⟨hSet, hM, pa, ow, bs, o', h0, h1, h2, h3, h4, h5, h6, h7, hSd, hW⟩ :=
    hRun blk hblk k st m En ds y cols st' hA hdr hSt
  exact layers_letters h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite
    (attAt_none_of_layAt hx) hx ht sub hsub
    (piece_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot R.inLot R.lotPlace hd
      hsub).2
    k blk _ wit st st' m ds y cols En
    (left_thr_fast src o pol lay KL Fd base SA SB O hS (headReturns_onCalls _ _ _ s hd) hblk hA.1
      hdr hSt hSet hM)
    ((hS.place blk hblk).trans hS.lotPlace) (ledger_thr hS hA.1) hpo hd pa h0 h1 h2 h3 h4 ow bs o'
    _ h5 h6 h7 (Nat.le_refl _) hSd hW

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**At an attention link: the same.** Conditional on the same. At the elder row. -/
theorem opens_headCalls_attention
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {A : OnBytes.Attention.Shape}
    {tl : HTailF2} (hx : attAt Zp.p.X s.link = some (x, A, tl))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunAll (LH) Said (borderOf s.link s.digits) s wit h.𝔇.Rd
      (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (1 + shift sub)
      (fun _ _ a θ hd' mk v => AtAttention s h.𝔇.sent h.𝔇.l3 x tl a θ hd' mk v A)) :
    ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
      (LH).thread.Items [Item.formsT s.link (2 + shift sub) "objects",
        .worth s.link (2 + shift sub) "planes", .worth s.link (2 + shift sub) "keys",
        .worth s.link (2 + shift sub) "rider"] k st' y.2 (En.add y.1) := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, SA, SB, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot _ wit R
  obtain ⟨hSet, hM, pa, ow, bs, o', h0, h1, h2, h3, h4, h5, h6, h7, hSd, hW⟩ :=
    hRun blk hblk k st m En ds y cols st' hA hdr hSt
  exact attention_letters h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite hx sub hsub
    (piece_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot R.inLot R.lotPlace hd
      hsub).2
    k blk _ wit st st' m ds y cols En
    (left_thr_fast src o pol lay KL Fd base SA SB O hS (headReturns_onCalls _ _ _ s hd) hblk hA.1
      hdr hSt hSet hM)
    ((hS.place blk hblk).trans hS.lotPlace) (ledger_thr hS hA.1) hpo hd pa h0 h1 h2 h3 h4 ow bs o'
    _ h5 h6 h7 (Nat.le_refl _) hSd hW

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**At the head's link, which under the head is 24: the same, at the piece 3.** The clause at a
witness takes the request at the input's public part, and the reply's token as the state left has
it, 0 where the state has none: public; no hypothesis here says that the token is there. Conditional
on the same. At the elder row. -/
theorem opens_headCalls_link24
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    (hl : s.link = headLink Zp.p.X) (hsub : (LH).links[s.link]? = some .head)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunAll (LH) Said (borderOf s.link s.digits) s wit h.𝔇.Rd
      (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) 2
      (fun w' t a θ hd' mk v => @AtHead (k3SizesAt (P5J.At.X Zp)) (k3PolicyAt (P5J.At.X Zp))
        (h.𝔇.rq w'.x.pub) _ _ Zp s h.𝔇.sent h.𝔇.l3 (k3AdrAt (P5J.At.X Zp)) x₀ a θ hd' mk
        (t.replyTok?.getD 0) v)) :
    ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
      (LH).thread.Items [Item.formsT s.link 3 "objects", .worth s.link 3 "planes",
        .worth s.link 3 "keys", .worth s.link 3 "rider"] k st' y.2 (En.add y.1) := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, SA, SB, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot _ wit R
  obtain ⟨hSet, hM, pa, ow, bs, o', h0, h1, h2, h3, h4, h5, h6, h7, hSd, hW⟩ :=
    hRun blk hblk k st m En ds y cols st' hA hdr hSt
  exact head_letters h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite hl hsub
    k blk _ wit st st' m ds y cols En
    (left_thr_fast src o pol lay KL Fd base SA SB O hS (headReturns_onCalls _ _ _ s hd) hblk hA.1
      hdr hSt hSet hM)
    ((hS.place blk hblk).trans hS.lotPlace) (ledger_thr hS hA.1) hpo hd pa h0 h1 h2 h3 h4 ow bs o'
    _ h5 h6 h7 (Nat.le_refl _) hSd hW

/-- **The premises at one witness, by what the public readers answer at the site's link.** A
definition, meant as a hypothesis: equations on a witness; no file shows it of the Script's. w': the
input; t: the state that the member leaves. Three implications: `AtAttention` at every answer of
`attAt`; `AtLayers` at every answer of `layAt` and `tlAt`; `AtHead` where the link is `headLink`.
At most one of the three speaks (`attAt_none_of_layAt`,
Johnson/Desc/First/Look/K3PlaceAtCopies.lean; `attAt_head`, `layAt_head`, K3HeadFill.lean there).
Where none speaks it holds of everything; under the head, at a link below 25, just one does
(`k03_attAt_some`, `k03_layAt_some`, Johnson/P5J/AllItemsAt.lean; `headLink_at`,
Johnson/P1K8R/BlindOwesAt.lean). -/
def AtCalls (s : Site) (w' : Local W₀ Rc ProofFile.Inst Tr) (t : TS) (a : Ask) (θ : GE)
    (hd' : List Fmt.Drawn) (mk : Nat → GE) (v : WtF) : Prop :=
  (∀ x A tl, attAt Zp.p.X s.link = some (x, A, tl) →
    AtAttention s h.𝔇.sent h.𝔇.l3 x tl a θ hd' mk v A) ∧
  (∀ x tl, layAt Zp.p.X s.link = some x → tlAtL Zp.p.X s.link = some tl →
    AtLayers s h.𝔇.sent h.𝔇.l3 x tl a θ hd' mk v (pubAt Zp.p.X (s.link / stepAt Zp.p.X))) ∧
  (s.link = headLink Zp.p.X →
    @AtHead (k3SizesAt (P5J.At.X Zp)) (k3PolicyAt (P5J.At.X Zp)) (h.𝔇.rq w'.x.pub) _ _ Zp s
      h.𝔇.sent h.𝔇.l3 (k3AdrAt (P5J.At.X Zp)) x₀ a θ hd' mk (t.replyTok?.getD 0) v)

/-- **THE ONE NAMED BUNDLE at a site on the calls, at the frame's letters at the library's head**:
`CallsRunAll` at these letters, at the library's own readers, seats and tables, at `AtCalls`. A
definition, meant as a hypothesis: it holds equations on the Script's witness and on a run's coins.
It is nobody's: no file shows it. What `CallsRunAll`'s docstring says of the coin's default, of
`tabQ` and of the elder row holds here. Asked at every sort that the letters' list of links gives at
the site's link: `hsub_at` (FormRestAtHeadFacts.lean) shows one, and the equation allows no second.
-/
def CallsRunHead (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (s : Site) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask) : Prop :=
  ∀ sub, (LH).links[s.link]? = some sub →
    CallsRunAll (LH) Said (borderOf s.link s.digits) s wit h.𝔇.Rd
      (fun i => h.𝔇.N.sent i 0) (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (1 + shift sub) (AtCalls h s)

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**At a site on the calls, of whatever link: at every step on the thread the four items that the row
opens hold behind the step.** The three by sort, joined by the site's link: 24, odd, or even.
Conditional on the head, R, hpo and hRun. At the elder row. -/
theorem opens_headCalls
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s wit) :
    ∀ blk, (LH).thread.bs[borderOf s.link s.digits]? = some blk → ∀ k st m En ds y cols st',
      ThrS (LH).thread Said (borderOf s.link s.digits) k st m En →
      drawsFit blk.rounds ds = true → (LH).thread.Stepped blk k st m En ds y cols st' →
      (LH).thread.Items [Item.formsT s.link (2 + shift sub) "objects",
        .worth s.link (2 + shift sub) "planes", .worth s.link (2 + shift sub) "keys",
        .worth s.link (2 + shift sub) "rider"] k st' y.2 (En.add y.1) := by
  have hl25 := link_lt_head h s hsite
  have hR := hRun sub hsub
  by_cases e24 : s.link = 24
  · have hl : s.link = headLink Zp.p.X := e24.trans (P1K8T.headLink_at h).symm
    have hs24 : (LH).links[s.link]? = some ModelPart.head := by
      rw [e24]
      rfl
    obtain rfl : sub = ModelPart.head := Option.some.inj (hsub.symm.trans hs24)
    exact opens_headCalls_link24 h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R
      hd hpo hl hsub Said (hR.imp fun _ _ _ _ _ _ _ H' => H'.2.2 hl)
  · obtain ⟨g, e | e⟩ := Nat.even_or_odd' s.link
    · obtain ⟨x, tl, hx, ht⟩ := P5J.k03_layAt_some h (g := g) (by omega)
      rw [← e] at hx ht
      exact opens_headCalls_layers h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R
        hd hpo hsub hx ht Said (hR.imp fun _ _ _ _ _ _ _ H' => H'.2.1 x tl hx ht)
    · obtain ⟨x, A, tl, hx⟩ := P5J.k03_attAt_some h (g := g) (by omega)
      rw [← e] at hx
      exact opens_headCalls_attention h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit
        R hd hpo hsub hx Said (hR.imp fun _ _ _ _ _ _ _ H' => H'.1 x A tl hx)

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**The frame's share `ExchangeAtS` at each of the four.** Conditional on the same. At the elder row.
-/
theorem exchangeAtS_headCalls
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    {sub : ModelPart} (hsub : (LH).links[s.link]? = some sub)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s wit)
    {j : Item} (hj : j ∈ [Item.formsT s.link (2 + shift sub) "objects",
      .worth s.link (2 + shift sub) "planes", .worth s.link (2 + shift sub) "keys",
      .worth s.link (2 + shift sub) "rider"]) :
    ExchangeAtS (LH).thread Said (borderOf s.link s.digits) j :=
  fun blk hblk k st m En ds y cols st' hA hdr hSt ds' i hi => by
    obtain rfl := List.mem_singleton.1 hi
    exact opens_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R hd hpo
      hsub Said hRun blk hblk k st m En ds y cols st' hA hdr hSt ds' _ hj

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.piece_headCalls
#print axioms ProofFile.Honest.K3.Law.Exchange.opens_headCalls_layers
#print axioms ProofFile.Honest.K3.Law.Exchange.opens_headCalls_attention
#print axioms ProofFile.Honest.K3.Law.Exchange.opens_headCalls_link24
#print axioms ProofFile.Honest.K3.Law.Exchange.opens_headCalls
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAtS_headCalls
