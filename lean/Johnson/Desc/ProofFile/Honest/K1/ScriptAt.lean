-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/ScriptAt.lean: THE SHARED "SENDING" (the kind K1) IN THE FRAME FOR
THE HONEST SIDE: WHAT A SENDING's MESSAGES, PADS AND TABLES ARE, AS FUNCTIONS OF THE PART's COINS,
THE INPUT AND THE CHALLENGES HEARD IN FRONT: made of rowsR (Honest/K1/Coins.lean): terms for the
threads' Script (Honest/Thread/First.lean) at K1's seats. Definitions with code; no theorem.

  rowsMsg       rows read as a witness's message (MsgT, Johnson/Desc/Sound/MsgSig.lean): the mask
                rows' and the main rows' entries. THE TWO KINDS OF TAILS STAND IN NO MESSAGE
  lentCut       a part's own coins off a run's coins, at the chain number ch: lendPart's own term
                (Honest/Frame.lean); none where the book has them not. NO DEFAULT IS LAID
  bookCovers    A PUBLIC TEST: the book's count at the address covers the count asked: no run in it.
                TO BE A NAMED PREMISE OF EVERY LAW OVER THESE COINS (lentCut_isSome,
                Honest/K1/ScriptAtLaw.lean: at the first and the shared chain the cut is there
                just where it accepts: at all coins or at none)
  rowsLaid      the rows that the part lays: rowsR at the job's letters, at what was heard in front
  scriptMsg     the place's message number n
  scriptPad     AT THE PLACES THAT THE LIBRARY's padB NAMES (Johnson/Desc/SeatAt.lean): the same
                rows at no data: it reads no input and no challenge; ELSEWHERE 0: no coin is due
                there
  wordlessTable, scriptTable   a table of no word · the place's tree number tau: its sender's place
                and treeTables' table; beyond the plan's trees the table of no word
  answersAtMostOne   A PUBLIC TEST: no message of the plan has more than one answer

rowsLaid, scriptMsg, scriptPad and scriptTable take the part's own cut c: by type and by text they
read no other coin of the run. Which coin is WRITTEN where is rowsR's rule alone: this file adds
none. The laws on it: CoinLaw, MaskLaw, PadLaw, DataLaw, RideLaw, CoinsIn (Honest/K1/).

Limits. Of Front the terms lay "own" := a letter and "seen" := nothing (Seen.bare []: no round
shown, no column handed; written out, not left to Front's default): a stand-in: they are the part's
own rows where the job's data reads of Front what was heard alone (rowsLaid_part). WHERE NO TABLE
RIDES A MASK ROW's ENTRIES ARE COINS AT ALL PLACES BELOW THE MASK CODE's MESSAGE LENGTH (mask_coin,
Honest/K1/MaskLaw.lean); A RIDING TABLE's ARE LAID OF FEWER COINS (Ride.lay, Honest/K1/Coins.lean):
BOTH STAND IN scriptMsg. AT A MESSAGE WITH MAIN ROWS AND NO ANSWER EVERY MAIN ENTRY BELOW THE CODE's
MESSAGE LENGTH IS A COIN (word_coin_e, word_coin_f, Honest/K1/CoinLaw.lean) AND STANDS IN scriptMsg.
AT A MESSAGE OF MORE THAN ONE ANSWER rowsR WRITES PAD COINS OFF padB's PLACES ("AT ONE ANSWER"):
THEY STAND IN scriptMsg (by the two texts; no law says it): answersAtMostOne is the test beside it;
it is proved true at no plan here. Nothing here holds these terms against any Script. Nothing on any
property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.Part
import Johnson.Desc.Sound.MsgSig

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes OnBytes.Slice OnBytes.Means VerifiableInference.Desc
open VerifiableInference.Desc.Sound (MsgT)
open Johnson.Prover.Send (Rows shapeAt)

variable {Bk : ProverCoinCounts} {W X : Type}

/-- Rows read as a witness's message: mask row or main row (true: mask), row, place. -/
def rowsMsg (s : OracleShape) (R : Rows) : MsgT :=
  fun mask r j => if mask then R.mask r j else R.main (s.mainDeg == 3) r j

/-- **A part's own coins off a run's coins**, at the chain number ch: lendPart's own term. none
where the book has them not: whether it is none is public (lentCut_isSome, at ch ≤ 1). At ch ≥ 2
Coins.look reads all three chains' tables, the first that has a row at the address: no seat of K1's
stands there, and no law here speaks of it. -/
def lentCut (k : Coins Bk) (ch : Nat) (a : Addr) (d : Due) : Option (Cs d) :=
  (k.look ch a).2.cut ⟨0, 0⟩ d

/-- **A PUBLIC TEST**: the book's count at the address covers d. COVERS, NOT EQUALS: the frame's
lendPart refuses unless the part takes JUST the book's count: at a book with more the cut is there
and the frame lends nothing. -/
def bookCovers (Bk : ProverCoinCounts) (ch : Nat) (a : Addr) (d : Due) : Bool :=
  decide (d.f ≤ (dueAt (Bk.rowsOf ch) a).f ∧ d.e ≤ (dueAt (Bk.rowsOf ch) a).e)

/-- **The rows that the part lays**, of its coins, the input and the challenges heard in front.
Front's "seen" is a stand-in, Seen.bare []: read by no job whose data reads of Front what was heard
alone. -/
def rowsLaid (J : SendJob W X) (own₀ : X) (c : Cs (dueR J.P J.ride)) (w : W)
    (h : List Fmt.Drawn) : Nat → Rows :=
  rowsR J.P J.ride (J.data w { heard := h, own := own₀, seen := .bare [] }) c

/-- The place's message number n. -/
def scriptMsg (J : SendJob W X) (own₀ : X) (n : Nat) (c : Cs (dueR J.P J.ride)) (w : W)
    (h : List Fmt.Drawn) : MsgT :=
  rowsMsg (shapeAt J.P n) (rowsLaid J own₀ c w h n)

/-- **The pad's own component**: at padB's places the same rows at no data; elsewhere 0. -/
def scriptPad (J : SendJob W X) (n : Nat) (c : Cs (dueR J.P J.ride)) : MsgT :=
  fun mask r j =>
    if padB J.P.codes (shapeAt J.P n) mask r j then
      rowsMsg (shapeAt J.P n) (rowsR J.P J.ride (fun _ _ _ => none) c n) mask r j
    else 0

/-- A table of no word. -/
def wordlessTable : Table := ⟨0, 0, fun _ i => i.elim0⟩

/-- The place's tree number τ. BEYOND THE PLAN's NUMBER OF TREES IT IS wordlessTable ([τ]?.getD): a
law on it speaks below that number. -/
def scriptTable (J : SendJob W X) (own₀ : X) (τ : Nat) (c : Cs (dueR J.P J.ride)) (w : W)
    (h : List Fmt.Drawn) : Place × Table :=
  (J.P.place, ((treeTables J.P (rowsLaid J own₀ c w h))[τ]?).getD wordlessTable)

/-- **A PUBLIC TEST**: no message of the plan has more than one answer. -/
def answersAtMostOne (P : K1.Par) : Bool :=
  (List.range P.sent.size).all fun n => decide ((shapeAt P n).answers ≤ 1)

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.rowsMsg
#print axioms ProofFile.Honest.K1.lentCut
#print axioms ProofFile.Honest.K1.bookCovers
#print axioms ProofFile.Honest.K1.rowsLaid
#print axioms ProofFile.Honest.K1.scriptMsg
#print axioms ProofFile.Honest.K1.scriptPad
#print axioms ProofFile.Honest.K1.wordlessTable
#print axioms ProofFile.Honest.K1.scriptTable
#print axioms ProofFile.Honest.K1.answersAtMostOne
