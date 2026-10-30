-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeAtHead.lean: the kind "lookup" (K3): THE DEBT
`Exchange` (Honest/Thread/Pays.lean) AT A LOOKUP ON THE DIGITS, AT THE FRAME'S LETTERS AT THE
LIBRARY'S HEAD (`lettersHead`, Honest/Thread/FirstHead.lean): `exchange_digits_text_fast`
(ExchangeDigitsFast.lean), which holds at the first chain's letters, a variable, IS CALLED HERE.

  `exchange_headDigits`   THE CALL, at a site's own border

WHAT STAYS, THE HEAVIEST FIRST:
  hRun          `DigitsRunAll` (ExchangeDigitsAll.lean): AT EVERY STEP ON THE THREAD: the ask is
                settled; the site's data stand between the stages; the readers' forms at the state
                behind; the book and the starts fit; THE SENDER LAYS THE MASK'S ROW; `AtDigits` at
                the script's witness: THE HONEST RUN'S OWN FACTS, on the script and the prover:
                nobody's yet
  hBack         the link's three pins go back along the library's same-but
  hfit, hb      the thread's rows fit forward up to a number beyond the border (public, with code)
  hx, hsub      the plan's record at the digits; the link's sort (public)
  the site; R (`SiteRest`, at the fast filling's asked jobs); hH; hbase
PAID INSIDE, of the top's twenty hypotheses eleven: the description's return and `SiteAt`
(`siteAt_lettersHead`); the written place, its link and its piece (`site_border`, `place_at`,
`hsub_at`); the composed meaning's lookup clause (`k3At_lettersAt`); its text on forms
(`formsText_lettersAt`: so the top's seven letters are laid as the head's own data); which runs the
item "objects" names, and that neither is ahead (`runs_digits`, `ah_objects`, `ah_guests`).

FROM THE THREAD ALONE. AT THE DIGITS ALONE. THE FULL SIZE ALONE. No instance of the hypotheses
beside the head is exhibited in this file.

THE FRAME'S LETTER FOR "keeps" BY PLACE IS A VARIABLE, Kp: nothing here reads it.

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

Limits. Nothing shows that the thread holds at any run, or that hRun can be had. Nothing on
soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeDigitsFast
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormsAtLetters
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.FormRestAtHeadFacts
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.RidersAtHeadForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (digAt)
open VerifiableInference.Desc.Sound (MsgT GoesBack seatTab)
open VerifiableInference.Desc.Sound.MgAt (borderOf)
open VerifiableInference.OnPublicFiles (SameBut relOf)
open OnBytes.Maker (WholeD)
open P5J (AtMgA CellsM TS)
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

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**THE DEBT `Exchange` AT A LOOKUP ON THE DIGITS, AT THE FRAME'S LETTERS AT THE LIBRARY'S HEAD.**
CONDITIONAL ON what this file's head lists: hRun first. No instance of the hypotheses beside the
head is exhibited in this file. -/
theorem exchange_headDigits (src : Sources W₀' Xi' Tr') (s : Site) (hsite : s ∈ lookSites Zp)
    (lot : Block TS ProofFile.Cl) (wit : Local W₀ Rc ProofFile.Inst Tr → Ask)
    (R : SiteRest Zp cF H.first s lot ((fastFill (Rc := Rc') src).jobs s).asked wit)
    (hH : HeadReturns (LH) (borderOf s.link s.digits) Zp s) (hd : s.digits = true) {sub : ModelPart}
    (hsub : (LH).links[s.link]? = some sub) {n : Nat}
    (hfit : fwdFit (LH).thread.start (LH).thread.row n = true)
    (hb : borderOf s.link s.digits < n) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Zp.p.X s.link = some (x, tl)) (nT : Nat)
    (hbase : nT ≤ treesTo (LH).bs (borderOf s.link s.digits))
    (hBack : ∀ w', ∀ i ∈ [Item.pin s.link 2, .pin s.link 0, .pin s.link 1],
      GoesBack (relOf SameBut nT) (i.holds (LH).N ((LH).mg w')))
    (hRun : DigitsRunAll (LH) (borderOf s.link s.digits) s wit h.𝔇.sent h.𝔇.l3 x tl h.𝔇.Rd
      h.𝔇.N.group (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) (6 + shift sub)) :
    Exchange (LH).thread (borderOf s.link s.digits) := by
  obtain ⟨o, pol, lay, KL, Fd, Bs, base, A, B, O, hS⟩ :=
    siteAt_lettersHead h H Q test carryX item n₁ n₂ b₀ Vd cs Kp w s hsite lot _ wit R
  obtain ⟨_, hk, e3⟩ := site_border h s hsite lot R.inLot R.lotPlace
  have hp := (place_at h s hsite lot R.inLot R.lotPlace).2
  have hl : s.at_.place.link = some s.link := by
    rw [hp]
  have hpiece : s.at_.place.piece =
      VerifiableInference.Desc.Sound.MgAt.pieceOf s.link s.digits := by
    rw [hp]
    rfl
  obtain ⟨sub', h1, h2⟩ := hsub_at h H.first Q _ _ test carryX item n₁ n₂ _ _ _ s hsite lot
    R.inLot R.lotPlace
  have es : sub' = sub := Option.some.inj (h1.symm.trans hsub)
  have hpcT : s.at_.place.piece = 7 + shift sub := by
    rw [h2, es, hd]
    rfl
  have hpc : VerifiableInference.Desc.K3.pieceAt Zp.p.X s.link true = 7 + shift sub := by
    rw [← hd, e3, ← hpiece]
    exact hpcT
  exact exchange_digits_text_fast src o pol lay KL Fd base A B O hS hH hd hk hl hsub hpcT hfit hb
    (fun w' => k3At_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ w') hx hpc nT hbase
    hBack h.𝔇.runs h.𝔇.Rd h.𝔇.N.sent h.𝔇.N.group h.𝔇.ah (seatTab h.𝔇.cs h.𝔇.arr h.𝔇.ms) h.𝔇.wt
    (fun w' => formsText_lettersAt h H.first Q _ _ test carryX item n₁ n₂ _ _ _ w')
    (6 + shift sub) (runs_digits h s.link sub hsub) (ah_objects h _) (ah_guests h _) hRun

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.exchange_headDigits
