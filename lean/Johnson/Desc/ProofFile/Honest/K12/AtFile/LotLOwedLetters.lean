-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/LotLOwedLetters.lean

It states no goal. No property of the protocol is claimed.

Three things that the tie of the words at
the first chain's closing proximity test (words_carrying; not beneath this file) asks of the code
switch's lot beside the tie itself, AT LETTERS: at any place p of the kind, any book, any chain
number up to 1. One definition with code, a public test; five theorems.

  `switchLotReady`            THE PUBLIC TEST: six clauses on the book, the place and the segments
  `handed_isSome_counts`      the frame hands the switch's part its coins just where the library's
                              test on counts, `lendsPart`, accepts
  `handed_isSome_book`        at the first and the shared chain these counts are the book's: no
                              run's coins on the right
  `handed_of_book`            so, where that test accepts, something is handed at every run's coins
  `switchRowsLaid_returns`    the lot's rows return at all that can be handed, all challenges, and
                              every input whose public instance passes `publicOk`
  `switch_lot_returns`        THE THREE TOGETHER, under `switchLotReady` and `publicOk`

By what. `lendPart_ok_iff` (Honest/Small/LendsRow.lean) · `K1.look_due` (Honest/K1/ScriptAtLaw.lean)
· `rows_isSome` (Honest/K2/Law/LotsAnswer.lean) · `noWord_yes` (Honest/K2/Law/Counts.lean).

Hypotheses of `switch_lot_returns`. hc: the chain's number is 0 or 1. hready: the public test. hpub:
the filling's public test at the input's public instance.

Limits.
- `switchLotReady` is evaluated at no book and no place here.
- hpub reads the instance: whoever wants the rows at a stand of a thread owes that the thread's
  valid inputs pass it.
- At the lot's own closing `lotClosingAt` alone.
- On whether something is handed and whether the rows return: nothing on what they are.
- Nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.LotsAnswer
import Johnson.Desc.ProofFile.Honest.Small.LendsRow
import Johnson.Desc.ProofFile.Honest.K1.ScriptAtLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open ProofFile.Honest.K2.Law (SwitchCoins)

variable {W₀ Rc Xi Tr : Type} {Bk : ProverCoinCounts}

/-- **The frame hands the switch's part its coins just where the library's test on counts
accepts.** -/
theorem handed_isSome_counts (ch : ℕ) (p : K2.SwitchPlace) (k : Coins Bk) :
    (K2.handed ch p k).isSome =
      lendsPart Bk (Bk.rowsOf ch) (fun o => (k.look ch o).1) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) := by
  have i := lendPart_ok_iff Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
    (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries)
  unfold K2.handed
  cases hx : lendPart Bk (Bk.rowsOf ch) (k.look ch) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) with
  | ok y => exact (i.1 ⟨y, hx⟩).symm
  | error e =>
    cases hb : lendsPart Bk (Bk.rowsOf ch) (fun o => (k.look ch o).1) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) with
    | false => rfl
    | true =>
      obtain ⟨y, hy⟩ := i.2 hb
      rw [hx] at hy
      cases hy

/-- **At the first and the shared chain the counts are the book's**: no run's coins occur on the
right. -/
theorem handed_isSome_book (ch : ℕ) (hc : ch ≤ 1) (p : K2.SwitchPlace) (k : Coins Bk) :
    (K2.handed ch p k).isSome =
      lendsPart Bk (Bk.rowsOf ch) (dueAt (Bk.rowsOf ch)) ⟨p.place, 0⟩
        (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) := by
  rw [handed_isSome_counts, show (fun o => (k.look ch o).1) = dueAt (Bk.rowsOf ch) from
    funext fun o => ProofFile.Honest.K1.look_due k ch hc o]

/-- **Where the book's counts fit, something is handed at every run's coins.** -/
theorem handed_of_book (ch : ℕ) (hc : ch ≤ 1) (p : K2.SwitchPlace)
    (hb : lendsPart Bk (Bk.rowsOf ch) (dueAt (Bk.rowsOf ch)) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) = true)
    (k : Coins Bk) : ∃ c, K2.handed ch p k = some c :=
  Option.isSome_iff_exists.1 (by rw [handed_isSome_book ch hc p k, hb])

/-- **The lot's rows return**, at all that can be handed, at all challenges. -/
theorem switchRowsLaid_returns (D : RowDataOf Xi) (readers : Local W₀ Rc Xi Tr → Readers)
    (lay : OnBytes.Params.ReqLayout) (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (hok : K2.closingOk K2.freshTable (segs.take p.link) p = true)
    (hserves : p.sizes.serves = true) (hroomy : p.sizes.roomy = true)
    (hfits : K2.placeFits p = true) (w : Local W₀ Rc Xi Tr)
    (hpub : K2.publicOk D lay p (segs.take p.link) w.x = true)
    (c : SwitchCoins p.sizes p.others p.foldVars p.carries) (hd : List Fmt.Drawn) :
    ∃ V, K2.switchRowsLaid D readers (K2.lotClosingAt lay segs) p c w hd = .ok V := by
  have e := K2.Law.rows_isSome D readers lay segs p hok c w hd
  rw [hserves, hroomy, hpub, hfits] at e
  cases hV : K2.switchRowsLaid D readers (K2.lotClosingAt lay segs) p c w hd with
  | ok V => exact ⟨V, rfl⟩
  | error m =>
    rw [hV] at e
    cases e

/-- **THE PUBLIC TEST**: on the book, the chain's number, the segments and the place: no input, no
coin, no challenge. Its clauses: the book's counts fit what the switch's part takes and carries ·
the closing returns at zeros · the two tests of the part on the sizes · the sending passes the shared
sending's test · every message with a main row is sampled · the sending has two messages or more. -/
def switchLotReady (Bk : ProverCoinCounts) (ch : ℕ) (segs : List K2.SegmentPub) (p : K2.SwitchPlace) : Bool :=
  lendsPart Bk (Bk.rowsOf ch) (dueAt (Bk.rowsOf ch)) ⟨p.place, 0⟩
      (K2.switchPart (K2.coreSender K2.freshTable) p.sizes p.others p.foldVars p.carries) &&
    K2.closingOk K2.freshTable (segs.take p.link) p && p.sizes.serves && p.sizes.roomy &&
    K2.placeFits p && K2.noWord (K2.switchSent p.sizes p.others) &&
    decide (1 < (K2.switchSent p.sizes p.others).size)

/-- **THE THREE TOGETHER.** Under the public test, at every run's coins, every input whose public
instance passes the filling's test and every list of challenges: the part is handed coins, and at
them the lot's rows return; no message with a main row goes unsampled; the sending has messages 0
and 1. -/
theorem switch_lot_returns (ch : ℕ) (hc : ch ≤ 1) (D : RowDataOf Xi)
    (readers : Local W₀ Rc Xi Tr → Readers) (lay : OnBytes.Params.ReqLayout)
    (segs : List K2.SegmentPub) (p : K2.SwitchPlace)
    (hready : switchLotReady Bk ch segs p = true) :
    K2.NoWord (K2.switchSent p.sizes p.others) ∧ 0 < (K2.switchSent p.sizes p.others).size ∧
      1 < (K2.switchSent p.sizes p.others).size ∧
      ∀ (k : Coins Bk) (w : Local W₀ Rc Xi Tr),
        K2.publicOk D lay p (segs.take p.link) w.x = true → ∀ hd : List Fmt.Drawn,
          ∃ (c : SwitchCoins p.sizes p.others p.foldVars p.carries)
            (V : ℕ → Johnson.Prover.Send.Rows), K2.handed ch p k = some c ∧
              K2.switchRowsLaid D readers (K2.lotClosingAt lay segs) p c w hd = .ok V := by
  unfold switchLotReady at hready
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hready
  obtain ⟨⟨⟨⟨⟨⟨hb, hok⟩, hs⟩, hr⟩, hf⟩, hn⟩, h1⟩ := hready
  refine ⟨K2.noWord_yes hn, by omega, h1, fun k w hpub hd => ?_⟩
  obtain ⟨c, hH⟩ := handed_of_book ch hc p hb k
  obtain ⟨V, hV⟩ := switchRowsLaid_returns D readers lay segs p hok hs hr hf w hpub c hd
  exact ⟨c, V, hH, hV⟩

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.handed_isSome_counts
#print axioms ProofFile.Honest.K12.AtProof.handed_isSome_book
#print axioms ProofFile.Honest.K12.AtProof.handed_of_book
#print axioms ProofFile.Honest.K12.AtProof.switchRowsLaid_returns
#print axioms ProofFile.Honest.K12.AtProof.switchLotReady
#print axioms ProofFile.Honest.K12.AtProof.switch_lot_returns
