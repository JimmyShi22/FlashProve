-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/Thread/ExchangeOpensDigits.lean: the honest side of the kind
"lookup" (K3): at the description's own member at a link's lookup on the digits, at the fast
summands: what the table's row opens, apart from what it reads and leaves. Two theorems; the first
chain's letters are a variable.

Why. `exchange_digits_all_fast` and `exchange_digits_text_fast` (ExchangeDigitsFast.lean in this
folder) end at the frame's `Exchange` (Honest/Thread/Pays.lean): all that the row owes: the three
items that it opens and the three pins that it reads and leaves. Their proof has two goals. The
second (the pins) takes `hBack`, which no file shows at the honest letters' own letter for a pin
(CarriedSite.lean's head says what the library has). The frame now asks a
house for shares, item by item (`ExchangeAt`, Honest/Thread/Shares.lean), and takes the pins on
itself. So the first goal stands here by itself.

What is shown.
  `opens_digits_fast`: at every step on the thread the three items that the row opens hold behind
    the step. The binders are those of `exchange_digits_text_fast` less a, n, hk, hl, hsub, hpcT,
    hfit, hb, nT, hbase and hBack; the proof is that of the first goal of
    `exchange_digits_all_fast`, to the letter but for one rewriting that the written list spares.
  `exchangeAt_digits_fast`: so `ExchangeAt` at each of the three.

Hypotheses that remain: as the heads of ExchangeDigitsFast.lean and ExchangeDigitsAll.lean list them
for the first goal. The heaviest is `hRun` : `DigitsRunAll`: the honest run's own facts at every
step on the thread: nobody's. The letter sub stands in hpc, in hr and in the end; hpc pins it.

Imported. ExchangeDigitsFast.lean; Honest/Thread/Shares.lean.

Users. ExchangeOpensAtHead.lean in this folder.

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

Limits. This pays nothing at a Script: it strikes premises of a conditional sentence. From the
thread alone (`Thr`): so, by the frame's `exchangeAtS_of` (Honest/Thread/SharesS.lean), at every
family Said. `ExchangeAt` is a premise's form of the frame's. No instance of these hypotheses is
exhibited in this file. Nothing shows that the thread holds at any run.

Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.Thread.ExchangeDigitsFast
import Johnson.Desc.ProofFile.Honest.Thread.Shares

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Law.Exchange
open OnBytes.Model (HTailF2)
open VerifiableInference.Desc (Block Chain FileDescription Strs Wit)
open VerifiableInference.Desc.First (Item ModelPart shift)
open VerifiableInference.Desc.First.Look (Sent digAt)
open VerifiableInference.Desc.K9 (Readers)
open VerifiableInference.Desc.Sound (MsgT MsgQ)
open VerifiableInference.OnPublicFiles (K3At K3Letters)
open ProofFile.Honest.FirstThread (Letters)
open ProofFile.Honest.K3.Law.AtThr

local notation "FS" => VerifiableInference.Desc.First.S
local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "pieceOf" => VerifiableInference.Desc.K3.pieceAt

variable {Bk : ProverCoinCounts} {W₀ Rc Xi Tr Xo P Cells Tok W₀' Rc' Xi' Tr' : Type} {D : Sent}
  {Lk : K3Letters Cells Tok} {L : Letters Bk ProofFile.Cl W₀ Rc Xi Tr Xo P Cells Tok MsgT}

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**At every step on the thread the three items that the row opens hold behind the step.** At the
fast summands. Conditional on what this file's head lists; sub is pinned by hpc. No instance of
these hypotheses is exhibited in this file. -/
theorem opens_digits_fast (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument)
    (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub} {Bs : PureBase}
    (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → Ask}
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hH : HeadReturns L b Z s) (hd : s.digits = true) {sub : ModelPart}
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Z.p.X s.link = some (x, tl)) (hpc : pieceOf Z.p.X s.link true = 7 + shift sub)
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hF : ∀ w, FormsText (L.Mg w) runs Rd sent own ah tabOf wt) (piece : Nat)
    (hr : runs s.link (7 + shift sub) "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false)
    (hRun : DigitsRunAll L b s wit D Lk x tl Rd own tabOf piece) :
    ∀ blk, L.thread.bs[b]? = some blk → ∀ k st m En ds y cols st',
      Thr L.thread b k st m En → drawsFit blk.rounds ds = true →
      L.thread.Stepped blk k st m En ds y cols st' →
      L.thread.Items [Item.forms s.link (7 + shift sub) "objects",
        .worth s.link (7 + shift sub) "planes", .worth s.link (7 + shift sub) "keys"] k st' y.2
        (En.add y.1) := by
  intro blk hblk k st m En ds y cols st' hA hdr hSt
  obtain ⟨hSet, hM, pa, ow, bs, o', h0, h1, h2, h3, h4, h5, h6, h7, hSd, hW⟩ :=
    hRun blk hblk k st m En ds y cols st' hA hdr hSt
  exact allOpenings_digitsLookup L Z s hS.site hK hx _ hpc k blk _ wit st st' m ds y cols En
    (left_thr_fast src o pol lay KL Fd base A B O hS hH hblk hA hdr hSt hSet hM)
    ((hS.place blk hblk).trans hS.lotPlace) (ledger_thr hS hA) hd runs Rd sent own ah tabOf wt
    (fun w => formsText_gives (hF w)) piece hr ha1 ha2 pa h0 h1 h2 h3 h4 ow bs o' _ h5 h6 h7
    (Nat.le_refl _) hSd hW

/-- The premise `hRun` holds equations on the Script's witness and on a run's coins. It is
nobody's: no file shows it. This pays nothing at a Script.
**The frame's share `ExchangeAt` at each of the three.** Conditional on the same. No instance
of these hypotheses is exhibited in this file. -/
theorem exchangeAt_digits_fast (src : Sources W₀' Xi' Tr') (o : SecondHashFunctionArgument)
    (pol lay KL : ByteArray) (Fd : FileDescription Inst) {Z : Pub} {Bs : PureBase}
    (base : List (Block FS ProofFile.Cl)) {ch : Chain FS ProofFile.Cl} (A : SharedSeat) (B : SecondSeat)
    (O : IM.Open o pol lay KL Fd Z Bs base ch A B) {b : Nat} {s : Site} {lot : Block FS ProofFile.Cl}
    {wit : Local W₀ Rc Xi Tr → Ask}
    (hS : SiteAt L b Z Bs ch s lot ((fastFill (Rc := Rc') src).jobs s).asked wit D Lk)
    (hH : HeadReturns L b Z s) (hd : s.digits = true) {sub : ModelPart}
    (hK : ∀ w, K3At Z.p.X D Lk (L.Mg w)) {x : PlaceL} {tl : HTailF2}
    (hx : digAt Z.p.X s.link = some (x, tl)) (hpc : pieceOf Z.p.X s.link true = 7 + shift sub)
    (runs : Nat → Nat → String → List (Nat × String)) (Rd : Nat → Readers)
    (sent : Nat → Nat → List (Nat × Nat)) (own : Nat → List (Nat × Nat))
    (ah : Nat → String → Bool) (tabOf : Wit Cells Tok MsgT → Nat × Nat → MsgQ)
    (wt : Nat → P × FS → Strs → Wit Cells Tok MsgT → Prop)
    (hF : ∀ w, FormsText (L.Mg w) runs Rd sent own ah tabOf wt) (piece : Nat)
    (hr : runs s.link (7 + shift sub) "objects" = [(piece, "objects"), (piece, "guests")])
    (ha1 : ah piece "objects" = false) (ha2 : ah piece "guests" = false)
    (hRun : DigitsRunAll L b s wit D Lk x tl Rd own tabOf piece)
    {j : Item} (hj : j ∈ [Item.forms s.link (7 + shift sub) "objects",
      .worth s.link (7 + shift sub) "planes", .worth s.link (7 + shift sub) "keys"]) :
    ExchangeAt L.thread b j :=
  fun blk hblk k st m En ds y cols st' hA hdr hSt ds' i hi => by
    obtain rfl := List.mem_singleton.1 hi
    exact opens_digits_fast src o pol lay KL Fd base A B O hS hH hd hK hx hpc runs Rd sent own ah
      tabOf wt hF piece hr ha1 ha2 hRun blk hblk k st m En ds y cols st' hA hdr hSt ds' _ hj

end ProofFile.Honest.K3.Law.Exchange

#print axioms ProofFile.Honest.K3.Law.Exchange.opens_digits_fast
#print axioms ProofFile.Honest.K3.Law.Exchange.exchangeAt_digits_fast
