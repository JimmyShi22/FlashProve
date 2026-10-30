-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeDigitsFast.lean: the honest side of the kind
"lookup" (K3): THE FRAME'S SENTENCE "THE EXCHANGE" AT THE DESCRIPTION'S OWN MEMBER AT A LINK'S
LOOKUP ON THE DIGITS, AT THE FAST SUMMANDS. Two theorems: the fellows of `exchange_digits_all` and
`exchange_digits_text` (ExchangeDigitsAll.lean, ExchangeDigitsText.lean in this folder), made of
their texts by program: two words turned in each.

WHY. These two take `SiteAt` AT THE SPECIFICATION'S SUMMANDS: its field on the list of halves then
says that the letters' list holds the row with these summands. The lot of the lookups lays
 THE FAST SUMMANDS (Honest/K3/LotFilled.lean): the two fillings are two
structures of functions that agree at a run alone: SO WHERE THAT LOT IS SEATED THE TWO CAN NEVER
BE CALLED. Here the same sentences stand at the fast summands, over `left_thr_fast`
(Honest/K3/Law/Thread/LeftThr.lean), whose premises are the same.

  `exchange_digits_all_fast`    all three items that the row opens concluded
  `exchange_digits_text_fast`   the same, with the premise on the field "forms" under its name

WHAT STAYS A PREMISE: as the two fellows' heads list. No instance of these hypotheses is exhibited
in this file.

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

Limits. `Exchange` is a premise's form of the frame's. Nothing on soundness, completeness or any
other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeDigitsText

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes (E zeroE)
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (Sent digAt)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (MsgT MsgQ GoesBack digits_row formsQ formsQA)
open VerifiableInference.OnPublicFiles (K3At K3Letters SameBut relOf)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok W₀' Rc' Xi' Tr' : Type} {D : Sent}
  {Lk : K3Letters Cells Tok} {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT}

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**CONDITIONAL ON what this file's head lists: THE EXCHANGE at the description's own member at a
link's lookup on the digits, all three items that the row opens concluded.** AT THE FAST SUMMANDS,
which the lots lay (`theLot`, `theLotInstFast`). No instance of these hypotheses is exhibited
in this file. -/
theorem exchange_digits_all_fast (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument)
    (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub} {Bs : PureBase}
    (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → Ask}
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hH : HeadReturns L b Z s) (hd : s.digits = true) {a : Place} {sub : ModelPart} {n : Nat}
    (hk : L.ps[b]? = some a) (hl : a.link = some s.link) (hsub : L.links[s.link]? = some sub)
    (hpcT : a.piece = 7 + shift sub)
    (hfit : fwdFit L.thread.start L.thread.row n = true) (hb : b < n)
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Z.p.X s.link = some (x, tl)) (hpc : pieceOf Z.p.X s.link true = 7 + shift sub)
    (nT : Nat) (hbase : nT ≤ treesTo L.bs b)
    (hBack : ∀ w, ∀ i ∈ [Item.pin s.link 2, .pin s.link 0, .pin s.link 1],
      GoesBack (relOf SameBut nT) (i.holds L.N (L.mg w)))
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hT : ∀ w, (L.Mg w).forms = fun i k r a y v =>
      (∀ p ∈ runs i k r,
        if ah p.1 p.2 = true then formsQA (sent i) (own i) (Rd i) p.1 p.2 a.2 (tabOf v)
        else formsQ (Rd i) (own i) p.1 p.2 a.2 (tabOf v)) ∧ (r = "weights" → wt i a y v))
    (piece : Nat)
    (hr : runs s.link (7 + shift sub) "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false)
    (hRun : DigitsRunAll L b s wit D Lk x tl Rd own tabOf piece) : Exchange L.thread b := by
  obtain ⟨_, ho, hc⟩ := digits_row L.links a s.link sub hl hsub hpcT
  refine exchange_row hk hl hfit hb ?_ ?_
  · intro blk hblk k st m En ds y cols st' hA hdr hSt
    rw [ho]
    obtain ⟨hSet, hM, pa, ow, bs, o', h0, h1, h2, h3, h4, h5, h6, h7, hSd, hW⟩ :=
      hRun blk hblk k st m En ds y cols st' hA hdr hSt
    exact allOpenings_digitsLookup L Z s hS.site hK hx _ hpc k blk _ wit st st' m ds y cols En
      (left_thr_fast src o pol lay KL Fd base A B O hS hH hblk hA hdr hSt hSet hM)
      ((hS.place blk hblk).trans hS.lotPlace) (ledger_thr hS hA) hd runs Rd sent own ah tabOf wt
      hT piece hr ha1 ha2 pa h0 h1 h2 h3 h4 ow bs o' _ h5 h6 h7 (Nat.le_refl _) hSd hW
  · rw [hc]
    exact carried_site o pol lay KL Fd base A B O hS nT hbase _ hBack

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**`exchange_digits_all_fast` with the premise on the field "forms" under its name.** CONDITIONAL ON
what that theorem's file lists. AT THE FAST SUMMANDS, which the elder lots lay (`theLot`,
`theLotInstFast`). No instance of these hypotheses is exhibited in this file. -/
theorem exchange_digits_text_fast (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument)
    (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub} {Bs : PureBase}
    (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → Ask}
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hH : HeadReturns L b Z s) (hd : s.digits = true) {a : Place} {sub : ModelPart} {n : Nat}
    (hk : L.ps[b]? = some a) (hl : a.link = some s.link) (hsub : L.links[s.link]? = some sub)
    (hpcT : a.piece = 7 + shift sub)
    (hfit : fwdFit L.thread.start L.thread.row n = true) (hb : b < n)
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Z.p.X s.link = some (x, tl)) (hpc : pieceOf Z.p.X s.link true = 7 + shift sub)
    (nT : Nat) (hbase : nT ≤ treesTo L.bs b)
    (hBack : ∀ w, ∀ i ∈ [Item.pin s.link 2, .pin s.link 0, .pin s.link 1],
      GoesBack (relOf SameBut nT) (i.holds L.N (L.mg w)))
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hF : ∀ w, FormsText (L.Mg w) runs Rd sent own ah tabOf wt) (piece : Nat)
    (hr : runs s.link (7 + shift sub) "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false)
    (hRun : DigitsRunAll L b s wit D Lk x tl Rd own tabOf piece) : Exchange L.thread b :=
  exchange_digits_all_fast src o pol lay KL Fd base A B O hS hH hd hk hl hsub hpcT hfit hb hK hx hpc
    nT hbase hBack runs Rd sent own ah tabOf wt (fun w => formsText_gives (hF w)) piece hr ha1 ha2
    hRun

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.exchange_digits_all_fast
#print axioms ProofFile.Honest.K3.Law.Exchange.exchange_digits_text_fast
