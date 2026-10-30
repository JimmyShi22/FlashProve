-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeSharesAtHead.lean: the kind "lookup" (K3): at a
lookup on the digits, at the frame's letters at the library's head: the shares of the exchange in
the form in which the frame's gathering asks them of a house. Theorems alone.

Why. The gathering `owesS_framesT` (Honest/Thread/GatherFramesT.lean; not
imported) asks at each number b of a sub-protocol of a kind other than `frame`: at every item j that
the row at b owes: `ExchangeAtS` at j, unless j is open in front of b and is a pin, pinI, pinW, or a
constr at one of the library's `parts4`. On the digits a row owes three items that it opens and
three pins that it reads and leaves. `exchangeAt_headDigits` (ExchangeOpensAtHead.lean) has the
share at the three. A pin is excused only if it is shown to be open in front.

What is shown.
  `shares_headDigits`: the end of that binder at the border of a site s on the digits, at every
    family Said. The binders are those of `exchangeAt_headDigits` up to hRun. "Open in front" is
    shown inside: what a row asks is open in front where the frame's test on the rows accepts
    (`asked_of_fit`, ExchangeRow.lean); that test accepts at every n by the frame's
    `FirstRows.fwdFit_of_opens` (Honest/Thread/FirstFits.lean) at `ProofFile.Honest.K4.W.onePass_full`
    (Honest/K4/Law/W/OnePassFull.lean).
  `shares_headDigits_num`: the same at the number as the gathering writes it:
    14 * s.link + ixOf s.link true + 2, to which the library's `borderOf` unfolds.
  `ix_lt`: ixOf l d is below `IM.nAt l`: so that number is one of the gathering's 14 * l + i + 2
    with i < IM.nAt l.

Hypotheses that remain: those of `exchangeAt_headDigits`: `hRun` : `DigitsRunAll`: the honest run's
own facts at every step on the thread: nobody's; `hH` : `HeadReturns`: at link 24 not paid; `R` :
`SiteRest`; `hsite`, `hd`, `hsub`, `hx`: public.

Imported, and built over. ExchangeOpensAtHead.lean in this folder. Three other files:
Honest/Thread/SharesS.lean and Honest/Thread/FirstFits.lean, on the frame's side;
Honest/K4/Law/W/OnePassFull.lean, on K4's honest side.
`onePass_full` is proved by `decide +kernel`: an evaluation in Lean's kernel of a
test on two written lists. No control stands beside it in that file.
The library's Johnson/P5J/MeansQ.lean (`parts4`) and Johnson/IMR/WrittenList.lean (`IM.nAt`).


Conditional on the head `P5J.AtMgA`. That it holds at the goals' two named sets of public files is a
sealed theorem (`headMember_named`, AtFullSide/Top/HeadMemberAtGap.lean), with that file's own
limits; this file does not call it.

`SiteRest` has the field half: the list of halves holds, at the site's place, the elder row
`proverSideOfLookupInChainAtOneOwner` at these summands. Who pays the field, each at the fast summands and under hypotheses on
the list: where the list of lots holds `theLot` or `theLotInst` itself: `half_field_theLot`
(HalfAtSite.lean [not in this library]), `half_field_theLotInst` (HalfOfLotInst.lean
[not in this library]); where it holds a lot with the halves of `theLotInst` at the public part:
`half_like_ok`, `half_field_like` (HalfOfLotLike.lean [not in this library]). A lot of rows that
pass their tables on (`proverSideOfLookupInChainKeepingTablesAtOneOwner`, Honest/K3/RowKeep.lean) lays another term there: no file shows
the field at such a lot, so the theorems of this file that bear it cannot be called there as they
stand. Honest/K3/Law/Keep/ carries plays and runs from the one row to the other (`lotsPlayed_whole`,
`chain_lots`, `run_same`); no file carries these sentences over.

Limits. This pays nothing at a Script: a conditional sentence; it touches nothing of what hRun asks.
It fills the gathering's binder at 25 of its numbers alone (i := ixOf l true); the others are other
kinds' and this kind's calls. The full size alone. No instance of the hypotheses beside the head is
exhibited in this file. Nothing shows that the thread holds at any run.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeOpensAtHead
import Johnson.Desc.ProofFile.Honest.Thread.SharesS
import Johnson.Desc.ProofFile.Honest.Thread.FirstFits
import Johnson.Desc.ProofFile.Honest.K4.Law.W.OnePassFull
import Johnson.P5J.MeansQ
import Johnson.IMR.WrittenList

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (digAt)
open VerifiableInference.Desc.Sound (MsgT seatTab digits_row)
open VerifiableInference.Desc.Sound.MgAt (borderOf ixOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS parts4)
open ProofFile.Honest.FirstThread (lettersHead Script WtF)
open ProofFile.Honest.K3.Law.AtThr

/-- The lookup's index in its segment is below the number of the segment's sub-protocols in front of
its batching. -/
theorem ix_lt (l : Nat) (d : Bool) : ixOf l d < IM.nAt l := by
  unfold ixOf IM.nAt
  split_ifs <;> omega

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

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The shares in the form of the gathering's binder, at the site's border.** Conditional on what
this file's head lists: hRun first. No instance of the hypotheses beside the head is exhibited in
this file. -/
theorem shares_headDigits (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
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
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot
    R.inLot R.lotPlace
  have es : sub' = sub := Option.some.inj (h1.symm.trans hsub)
  have hpcT : s.at_.place.piece = 7 + shift sub := by
    rw [h2, es, hd]
    rfl
  obtain ⟨_, ho, hc⟩ := digits_row (LH).links s.at_.place s.link sub hl hsub hpcT
  rw [owes_at_link (LH) hk hl, ho, hc] at hj
  rcases List.mem_append.1 hj with h3 | h3
  · exact exchangeAtS_of _ Said
      (exchangeAt_headDigits h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R hH hd
        hsub hx hRun h3)
  · have hopen : j ∈ (LH).thread.opened (borderOf s.link s.digits) :=
      asked_of_fit (LH).thread (n := borderOf s.link s.digits + 1)
        (FirstRows.fwdFit_of_opens ProofFile.Honest.K4.W.onePass_full _) (Nat.lt_succ_self _)
        (by rw [asks_at_link (LH) hk hl, hc]; exact List.mem_append_right _ h3)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h3
    rcases h3 with e | e | e
    · exact absurd e ((hmid hopen).1 _ _)
    · exact absurd e ((hmid hopen).1 _ _)
    · exact absurd e ((hmid hopen).1 _ _)

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The same at the number as the gathering writes it.** Conditional on the same. -/
theorem shares_headDigits_num (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub))
    (Said : Nat → Coins Bk → Mid (Local W₀ Rc ProofFile.Inst Tr) X → Prop) :
    ∀ j : Item, j ∈ ((LH).thread.row (14 * s.link + ixOf s.link true + 2)).owes →
      (j ∈ (LH).thread.opened (14 * s.link + ixOf s.link true + 2) →
        (∀ m t, j ≠ Item.pin m t) ∧ j ≠ Item.pinI ∧ j ≠ Item.pinW ∧
        ∀ m q, q ∈ parts4 → j ≠ Item.constr m q) →
      ExchangeAtS (LH).thread Said (14 * s.link + ixOf s.link true + 2) j := by
  have e : borderOf s.link s.digits = 14 * s.link + ixOf s.link true + 2 := by
    rw [hd]
    rfl
  rw [← e]
  exact shares_headDigits h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w src s hsite lot wit R hH hd
    hsub hx hRun Said

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.ix_lt
#print axioms ProofFile.Honest.K3.Law.Exchange.shares_headDigits
#print axioms ProofFile.Honest.K3.Law.Exchange.shares_headDigits_num
