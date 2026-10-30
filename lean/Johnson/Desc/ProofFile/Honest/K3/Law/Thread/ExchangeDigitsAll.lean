-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeDigitsAll.lean: the honest side of the kind
"lookup" (K3): THE FRAME'S SENTENCE "THE EXCHANGE" (`Exchange`, Honest/Thread/Pays.lean) AT THE
DESCRIPTION'S OWN MEMBER AT A LINK'S LOOKUP ON THE DIGITS, WITH ALL THREE ITEMS THAT THE ROW OPENS
CONCLUDED. An assembly of other files' theorems. One definition (the premises on a run, under a
name), one theorem.

  `DigitsRunAll`          THE PREMISES THAT SPEAK OF A RUN, by name
  `exchange_digits_all`   CONDITIONAL, see below: `Exchange L.thread b`

WHAT IS JOINED. `exchange_row` (Honest/K3/Law/Thread/ExchangeRow.lean): the sentence from what the
table's row opens and what it reads and leaves. The library's `digits_row`
(Johnson/Desc/Sound/DigitsRow.lean): these two lists. `allOpenings_digitsLookup`
(Honest/K3/Law/Thread/ExchangeAll.lean): the three items that the row opens, from `LeftAt`;
`left_thr_spec` (LeftThr.lean) and `ledger_thr` (LedgerThr.lean) hand it `LeftAt` and the ledger in
front out of the thread and the member's step. `carried_site` (CarriedSite.lean): the three items
that the row reads and leaves.

WHAT STAYS A PREMISE. The description's return; `SiteAt` at the specification's summands;
`HeadReturns`; where the member stands; the frame's test on the rows; the library's `K3At` at the
items' meaning; the public data's entry for the place, and the piece's number. hBack: THE THREE
ITEMS THAT THE ROW READS AND LEAVES ARE PINS: at a pin the frame's honest letters lay a letter of
their own. At the library's composed meaning that sentence is shown at pins, under hypotheses
(`mgAll_pin_back`, `mgAll_pinW_back`, Johnson/Desc/Sound/MgAt/K3Rides.lean); at the honest letters'
own letter for a pin: at `pinW` and `pinI` `plainItemGoesBack` shows it, at `lettersHead` under
`P5J.AtMgA` (Honest/K3/Term/LookupPlainItemsRidePast.lean); at `pin m t` no file shows it.
`DigitsRunAll`, at every run that the sentence binds: the input no longer moves; the relation after
the challenge; two tests on the book; and what follows. Of the filling: at every input the field
"forms" of the items' meaning is the library's text, at letters for its runs, readers and tables;
the name "objects" stands for two runs, "objects" and "guests"; neither is of the sort that is read
at the sender's own tables. Of the state that the member leaves (inside `DigitsRunAll`): a segment
is open; the reader answers at "objects" with the rows of the structure that the seat reads as
heard, and at "guests" with no form; the public test on forms accepts at both runs. THE SENDER'S LAW
AND THE TIES AT THE WITNESS ARE ASKED AT EACH CONTINUATION OF THE CHALLENGES HEARD, AT THAT
CONTINUATION'S OWN TABLES. No instance of these hypotheses is exhibited in this file.
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
import Johnson.Desc.Sound.DigitsRow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeRow
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.CarriedSite
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LeftThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.LedgerThr
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeAll

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
open VerifiableInference.Desc.K9 (segAt? Readers formsIn)
open VerifiableInference.Desc.K9L (maskOracle)
open VerifiableInference.Desc.Sound (MsgT MsgQ GoesBack digits_row formsQ formsQA dataQ tabQ)
open VerifiableInference.OnPublicFiles (K3At K3Letters SameBut relOf)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "PartK" => VerifiableInference.Desc.K9.Part
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok W₀' Rc' Xi' Tr' : Type} {D : Sent}
  {Lk : K3Letters Cells Tok} (L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT)

/-- **THE PREMISES THAT SPEAK OF A RUN**, at every run that the frame's sentence binds at the member
number b. Rd, own, tabOf: the readers, the seats and the tables of the field's text. piece: the
number under which the two runs stand. `SenderLays` is asked at s.p.first + s.at_.face.slots
entries: no more. At a site, under this definition's two tests (`bookFits`, `startsFit`), that
reading never takes the default: `named_reads_site` (Honest/K3/Law/BookFenceSite.lean). The table is
read through the library's `tabQ` (Johnson/Desc/Sound/FormsQ.lean), which is 0 where
`seatAt own book o` finds no seat: no hypothesis here names `seatAt`; the public test on forms
(`formsIn`) is what stands beside it. -/
def DigitsRunAll (b : Nat) (s : Site) (wit : Local W₀ Rc Xi Tr → Ask) (D : Sent)
    (Lk : K3Letters Cells Tok) (x : PlaceL) (tl : HTailF2) (Rd : Nat → Readers)
    (own : Nat → List (Nat × Nat)) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (piece : Nat) : Prop :=
  ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m En ds y cols st', Thr L.thread b k st m En →
    drawsFit blk.rounds ds = true → L.thread.Stepped blk k st m En ds y cols st' →
    Ask.Settled s.at_.base (wit m.st.input) ∧ (siteData s (wit m.st.input) m.st.heard ds).Mid ∧
    ∃ (a : PartK) (ow : Addr) (base : Due) (o : Nat), segAt? st' = some a ∧
      (∀ g', (seatOf K3Lot.ofForm s.digits).heard st' = some g' →
        (Rd s.link).forms piece "objects" st' = some { forms := g'.rows.toList, late := [] }) ∧
      (Rd s.link).forms piece "guests" st' = some { forms := [], late := [] } ∧
      formsIn (Rd s.link) (own s.link) piece "objects" st' = true ∧
      formsIn (Rd s.link) (own s.link) piece "guests" st' = true ∧
      bookFits Bk (Bk.rowsOf 0) (dueAt Bk.first) s.at_ = true ∧
      startsFit Bk s.at_ s.p.first ow base = true ∧ maskOracle a.L.check.frame = some o ∧
      (∀ ds', SenderLays
        (tabQ (own s.link) a.d.st a.d.book
          (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))))
        o 1 (s.p.first + s.at_.face.slots) base.e
        (fun i => rd ((coinsE (k.look 0 ow).2).getD i zeroE))) ∧
      ∀ ds', AtDigits s D Lk x tl (wit m.st.input)
        (up (ptsOf s.at_.face s.at_.base (m.st.heard ++ ds)).theta) m.st.heard
        (dataQ (own s.link) a (tabOf (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds')))).mask
        (L.Q.wit k y.2.st.input (y.2.st.heard ++ ds'))

variable {L}

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**CONDITIONAL ON what this file's head lists: THE EXCHANGE at the description's own member at a
link's lookup on the digits, all three items that the row opens concluded.** No instance of these
hypotheses is exhibited in this file. -/
theorem exchange_digits_all (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument)
    (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub} {Bs : PureBase}
    (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → Ask}
    (hS : SiteAt L b Z Bs ch s lot ((specFill (Rc := Rc') src).jobs s).asked wit D Lk)
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
      (left_thr_spec src o pol lay KL Fd base A B O hS hH hblk hA hdr hSt hSet hM)
      ((hS.place blk hblk).trans hS.lotPlace) (ledger_thr hS hA) hd runs Rd sent own ah tabOf wt
      hT piece hr ha1 ha2 pa h0 h1 h2 h3 h4 ow bs o' _ h5 h6 h7 (Nat.le_refl _) hSd hW
  · rw [hc]
    exact carried_site o pol lay KL Fd base A B O hS nT hbase _ hBack

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.exchange_digits_all
