-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeSharesCallsAtHead.lean: the kind "lookup" (K3):
at a lookup ON THE CALLS, at the frame's letters at the library's head: the shares of the exchange
in the form in which the frame's gathering asks them of a house; at a site, and at all 25 numbers of
the lookups on the calls. Theorems alone. The fellow of ExchangeSharesAtHead.lean, which has the
like at the digits.

NOT IN FRONT OF A LAW OVER COINS. The ends speak under `ThrS` and the member's step at a run's coins
k, with Said a letter for a predicate on the coins: a condition on the run's coins, which only "the
thread stands at every k" would lift; no file shows that. hRun and hR (at a site: R) say what the
Script's witness, the hidden input and the prover's list are; the coins are bound inside. The head,
hpo, the sites' membership and the readers' answers are public.

Why. The gathering asks at each number b of a sub-protocol of a kind other than `frame`, at every
item j that the row at b owes: `ExchangeAtS` at j, unless j is open in front of b and is a pin,
pinI, pinW, or a constr at one of the library's `parts4`. On the calls a row owes the four items
that it opens and two or three that it reads and leaves: pin i 0, constr i small and, but at an
attention link, pinW (`calls_row`, CallsRow.lean). `exchangeAtS_headCalls`
(ExchangeOpensCallsAtHead.lean) has the share at the four. The others are of the excused sorts
(small is one of `parts4`); an item is excused only if it is shown to be open in front.

What is shown.
  `shares_headCalls`: the end of that binder at the border of a site s on the calls, at the family
    Said of the bundle. "Open in front" is shown inside: what a row asks is open in front where the
    frame's test on the rows accepts (`asked_of_fit`, ExchangeRow.lean); that test accepts at every
    n by the frame's `FirstRows.fwdFit_of_opens` (Honest/Thread/FirstFits.lean) at
    `ProofFile.Honest.K4.W.onePass_full` (Honest/K4/Law/W/OnePassFull.lean).
  `shares_headCalls_num`: the same at the number as the gathering writes it:
    14 * s.link + ixOf s.link false + 2, to which the library's `borderOf` unfolds.
  `shares_calls_all`: THE TOP: at every l below 25, at 14 * l + ixOf l false + 2. A site on the
    calls stands at each such link (`site_calls_head`, SiteThereHead.lean). These 25 numbers are 28
    g + 3 (the layers' links), 28 g + 17 (attention's), g below 12, and 340 (the head's).

Hypotheses that remain. Those of `exchangeAtS_headCalls`: `hRun` : `CallsRunHead`: the honest run's
own facts at every step on the thread: nobody's; `R` : `SiteRest`; `hpo`: the library's test
`planesOk`: public; `hsite`, `hd`: public. In the top each of the three is asked at every site on
the calls, R under "there is a sub-protocol"; wit, the reader of the input, may hang on the site.

Imported. In this folder: ExchangeOpensCallsAtHead.lean, CallsRow.lean, ExchangeRow.lean,
ExchangeParts.lean, SiteThereHead.lean. Of the frame's authors: Honest/Thread/FirstFits.lean. Of the
authors of K4's honest side: Honest/K4/Law/W/OnePassFull.lean: `onePass_full` is proved by
`decide +kernel`: an evaluation in Lean's kernel of a test on two written lists. The library's
Johnson/P5J/MeansQ.lean (`parts4`).

Users. ExchangeByKind.lean in this folder.

Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

`SiteRest` has the field half: the list of halves holds, at the site's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. A lot of rows that pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`,
Honest/K3/RowKeep.lean) lays another term there: no file shows the field at such a lot, so the
theorems of this file that bear it cannot be called there as they stand. Honest/K3/Law/Keep/ carries
plays and runs from the one row to the other (`lotsPlayed_whole`, `chain_lots`, `run_same`); no file
carries these sentences over.

Limits. This pays nothing at a Script: conditional sentences; they touch nothing of what hRun asks.
The Script Q and the book Bk are variables. The top fills the gathering's binder at 25 of its
numbers alone (i := ixOf l false); the others are other kinds' and this kind's digits. The full size
alone. No instance of the hypotheses beside the head is exhibited in this file. Nothing shows that
the thread holds at any run: where it holds at none the shares hold emptily.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOpensCallsAtHead
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CallsRow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeParts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.SiteThereHead
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OnePassFull
import Johnson.P5J.MeansQ

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (planesOk)
open VerifiableInference.Desc.Sound (MsgT)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS parts4)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place

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

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**The shares in the form of the gathering's binder, at the site's border.** At the four items that
the row opens: `exchangeAtS_headCalls`. At what it reads and leaves (pin, constr small, pinW): shown
to be open in front, so the binder's own premise excuses them. Conditional on the head, R, hpo and
hRun. At the elder row. -/
theorem shares_headCalls
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s wit) :
    ∀ j : Item, j ∈ ((LH).thread.row (borderOf s.link s.digits)).owes →
      (j ∈ (LH).thread.opened (borderOf s.link s.digits) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said (borderOf s.link s.digits) j := by
  intro j hj hmid
  obtain ⟨_, hk, _⟩ := site_border h s hsite lot R.inLot R.lotPlace
  have hpl := (place_at h s hsite lot R.inLot R.lotPlace).2
  have hl : s.at_.place.link = some s.link := by
    rw [hpl]
  obtain ⟨sub, hsub₀, _⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot
    R.inLot R.lotPlace
  have hsub : (LH).links[s.link]? = some sub := hsub₀
  have hpcT := (piece_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot R.inLot
    R.lotPlace hd hsub).1
  obtain ⟨_, ho, hc⟩ := calls_row (LH).links s.at_.place s.link sub hl hsub hpcT
  rw [owes_at_link (LH) hk hl, ho, hc] at hj
  rcases List.mem_append.1 hj with h3 | h3
  · exact exchangeAtS_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R hd
      hpo hsub Said hRun h3
  · have hopen : j ∈ (LH).thread.opened (borderOf s.link s.digits) :=
      asked_of_fit (LH).thread (n := borderOf s.link s.digits + 1)
        (FirstRows.fwdFit_of_opens ProofFile.Honest.K4.W.onePass_full _) (Nat.lt_succ_self _)
        (by rw [asks_at_link (LH) hk hl, hc]; exact List.mem_append_right _ h3)
    rcases List.mem_cons.1 h3 with e | h4
    · exact absurd e ((hmid hopen).1 _ _)
    · rcases List.mem_cons.1 h4 with e | h5
      · exact absurd e ((hmid hopen).2.2.2 _ _ (by decide))
      · split at h5
        · cases h5
        · exact absurd (List.mem_singleton.1 h5) (hmid hopen).2.2.1

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**The same at the number as the gathering writes it.** Conditional on the same. -/
theorem shares_headCalls_num
    (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hd : s.digits = false) (hpo : planesOk s.shape s.p.lm = true)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hRun : CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s wit) :
    ∀ j : Item, j ∈ ((LH).thread.row (14 * s.link + ixOf s.link false + 2)).owes →
      (j ∈ (LH).thread.opened (14 * s.link + ixOf s.link false + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said (14 * s.link + ixOf s.link false + 2) j := by
  have e : borderOf s.link s.digits = 14 * s.link + ixOf s.link false + 2 := by
    rw [hd]
    rfl
  rw [← e]
  exact shares_headCalls h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R hd hpo
    Said hRun

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is nobody's:
no file shows it. This pays nothing at a Script.
**THE TOP AT THE CALLS: the shares at all 25 numbers of the lookups on the calls.** Conditional on
the head and, at every site on the calls, on hR (`SiteRest`, seven fields, under "there is a
sub-protocol"), hpo (the library's test `planesOk`: public; no file shows it at a site on the calls)
and hRun. THE ELDER ROW: hR's field half says that the prover's list holds `proverSideOfLookupInChainAtOneOwner` at the site's
place; at a lot of rows that pass their tables on this theorem cannot be called as it stands. The
full size alone. No instance of the hypotheses beside the head is exhibited in this file. -/
theorem shares_calls_all (src : Sources W₀' Xi' Tr')
    (wit : Site → Local W₀ Rc ProofFile.Inst Tr → Ask)
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop)
    (hR : ∀ s ∈ lookSites Zp, s.digits = false → ∃ lot : Block TS ProofFile.Cl,
      SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked (wit s))
    (hpo : ∀ s ∈ lookSites Zp, s.digits = false → planesOk s.shape s.p.lm = true)
    (hRun : ∀ s ∈ lookSites Zp, s.digits = false →
      CallsRunHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w Said s (wit s)) :
    ∀ l, l < 25 → ∀ j : Item, j ∈ ((LH).thread.row (14 * l + ixOf l false + 2)).owes →
      (j ∈ (LH).thread.opened (14 * l + ixOf l false + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said (14 * l + ixOf l false + 2) j := by
  intro l hl
  obtain ⟨s, hs, rfl, e2, _, _⟩ := site_calls_head h l hl
  obtain ⟨lot, R⟩ := hR s hs e2
  exact shares_headCalls_num h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hs lot (wit s) R e2
    (hpo s hs e2) Said (hRun s hs e2)

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.shares_headCalls
#print axioms ProofFile.Honest.K3.Law.Exchange.shares_headCalls_num
#print axioms ProofFile.Honest.K3.Law.Exchange.shares_calls_all
