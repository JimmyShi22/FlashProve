-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeByKind.lean: the kind "lookup" (K3): THE SHARES
OF THE EXCHANGE BY KIND: at every number at which the written list of places has a place of the kind
K3, all fifty: in the form in which the frame's gathering asks them, with "the place's kind is K3"
for "the place's kind is not the frame's". At the frame's letters at the library's head. Two
theorems; no definition. A join.

NOT IN FRONT OF A LAW OVER COINS. The ends speak under `ThrS` and the member's step at a run's coins
k, with Said a letter for a predicate on the coins: a condition on the run's coins, which only "the
thread stands at every k" would lift; no file shows that. hDig, hCalls and hR say what the Script's
witness, the hidden input and the prover's list are; the coins are bound inside. The head, hpo, the
sites' membership and the readers' answers are public. `k3_number` is a closed fact on a written
list: the mark is not meant for it.

Why. The frame's gathering takes the shares as one premise over all numbers whose place is not of
the kind frame; whoever pays that premise goes by cases on the place's kind and wants one law for
each kind. ExchangeSharesAtHead.lean has the shares at a site on the digits,
ExchangeSharesCallsAtHead.lean at a site on the calls. What parts these from the form by kind is the
step from a number to a site.

What is shown.
  `k3_number`: a number at which the written list has a place of the kind K3 is `borderOf l d` for
    a link l below 25 and a sort d. From `k3_place_full` and `ps_nodup` (SiteAtLetters.lean) and the
    library's `places_are_k3` (Johnson/Desc/Sound/MgAt/K3Open.lean). No premise beside the two on
    the number.
  `k3_exchange_by_kind`: THE TOP. By `k3_number`; a site stands at each link and sort
    (`site_at_all_fifty`, SiteAllFifty.lean); then `shares_headDigits` or `shares_headCalls`.

Hypotheses that remain. At every site: `hR`: there is a sub-protocol with `SiteRest`. At every site
on the digits: `hH` : `HeadReturns` (it speaks at link 24 alone) and `hDig` : `DigitsRunAll`
(ExchangeDigitsAll.lean), asked at every sort and every answer of `digAt` at the link. At every site
on the calls: `hpo`: the library's test `planesOk`; `hCalls` : `CallsRunHead`
(ExchangeOpensCallsAtHead.lean). hDig and hCalls are the honest run's own facts at every step on the
thread: nobody's. THE TWO ARE ASKED FROM TWO FRONTS: `DigitsRunAll` from the invariant `Thr` alone,
`CallsRunHead` from `ThrS`, the invariant together with Said: the first is the heavier premise.

Imported. In this folder: ExchangeSharesAtHead.lean, ExchangeSharesCallsAtHead.lean,
SiteAllFifty.lean, SiteAtLetters.lean, LinkLtHead.lean, FormRestAtHeadFacts.lean. The library's
Johnson/HB/LLHARD/Q38E/DigAtHead.lean (`Q38.digAt_at_head`) and Johnson/Desc/Sound/MgAt/K3Open.lean.

Users. None in this folder.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

`SiteRest` has the field half: the list of halves holds, at the site's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. This pays nothing at a Script: a conditional sentence; it touches nothing of what hDig and
hCalls ask. The Script Q and the book Bk are variables. That its end is the gathering's binder at
this kind is a matter of two texts: the gathering's file is not imported. The full size alone. No
instance of the hypotheses beside the head is exhibited in this file. Nothing shows that the thread
holds at any run: where it holds at none the shares hold emptily.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeSharesAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeSharesCallsAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAllFifty
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LinkLtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormRestAtHeadFacts
import Johnson.HB.LLHARD.Q38E.DigAtHead
import Johnson.Desc.Sound.MgAt.K3Open

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain Strs Place KindName)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (digAt planesOk)
open VerifiableInference.Desc.Sound (MsgT seatTab)
open VerifiableInference.Desc.Sound.MgAt (borderOf places_are_k3)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS parts4)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

/-- **A number of the kind K3 in the written list of places is the border of a link and a sort.** -/
theorem k3_number {b : Nat} {p : Place} (hb : P5J.At.ps[b]? = some p)
    (hk : p.kind = KindName.K3) : ∃ l, l < 25 ∧ ∃ d, b = borderOf l d := by
  obtain ⟨l, hl, d, rfl⟩ := k3_place_full (List.mem_of_getElem? hb) hk
  have h2 : P5J.At.ps[borderOf l d]? = some _ := places_are_k3 hl d
  exact ⟨l, hl, d, List.getElem?_inj (List.getElem?_eq_some_iff.1 hb).1 ps_nodup
    (hb.trans h2.symm)⟩

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

/-- The premises `hDig` and `hCalls` hold equations on the Script's witness and on a run's coins.
They are nobody's: no file shows them. This pays nothing at a Script.
**THE TOP BY KIND: the shares of the exchange at every number of the kind K3, all fifty.** A join of
`shares_headDigits` (ExchangeSharesAtHead.lean) and `shares_headCalls`. TWO MAKES IN ONE TOP: hDig,
`DigitsRunAll`, is asked from the invariant `Thr` alone, hCalls from `ThrS`, the invariant together
with Said: the first is the heavier premise; the frame's `exchangeAtS_of` carries its end over.
Conditional on the head and on: hR at every site; hH (it speaks at link 24 alone) and hDig at every
site on the digits; hpo and hCalls at every site on the calls. THE ELDER ROW: hR's field half says
that the prover's list holds `proverSideOfLookupInChainAtOneOwner` at the site's place; at a lot of rows that pass their tables
on this theorem cannot be called as it stands. The full size alone. No instance of the hypotheses
beside the head is exhibited in this file. -/
theorem k3_exchange_by_kind (src : Sources W₀' Xi' Tr')
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hR : ∀ s ∈ lookSites Zp, ∃ lot : Block TS ProofFile.Cl,
      SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked (wit s))
    (hH : ∀ s ∈ lookSites Zp, s.digits = true →
      HeadReturns (LH) (borderOf s.link s.digits) Zp s)
    (hDig : ∀ s ∈ lookSites Zp, s.digits = true → ∀ (sub : ModelPart) (x : PlaceL) (tl : HTailF2),
      (LH).links[s.link]? = some sub → digAt Zp.p.X s.link = some (x, tl) →
      DigitsRunAll (LH) (borderOf s.link s.digits) s (wit s) h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
        h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    (hpo : ∀ s ∈ lookSites Zp, s.digits = false → planesOk s.shape s.p.lm = true)
    (hCalls : ∀ s ∈ lookSites Zp, s.digits = false →
      CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s)) :
    ∀ b p, P5J.At.ps[b]? = some p → p.kind = KindName.K3 →
      ∀ j : Item, j ∈ ((LH).thread.row b).owes →
      (j ∈ (LH).thread.opened b →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said b j := by
  intro b p hb hk
  obtain ⟨l, hl, d, rfl⟩ := k3_number hb hk
  obtain ⟨s, hs, rfl, rfl, _, _⟩ := site_at_all_fifty h l hl d
  obtain ⟨lot, R⟩ := hR s hs
  rcases Bool.eq_false_or_eq_true s.digits with hd | hd
  · obtain ⟨sub, hsub, _⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hs lot
      R.inLot R.lotPlace
    obtain ⟨x, tl, hx⟩ := Q38.digAt_at_head h (Nat.le_of_lt_succ (link_lt_head h s hs))
    exact shares_headDigits h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hs lot (wit s) R
      (hH s hs hd) hd hsub hx (hDig s hs hd sub x tl hsub hx) Said
  · exact shares_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hs lot (wit s) R hd
      (hpo s hs hd) Said (hCalls s hs hd)

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.k3_number
#print axioms ProofFile.Honest.K3.Law.Exchange.k3_exchange_by_kind
