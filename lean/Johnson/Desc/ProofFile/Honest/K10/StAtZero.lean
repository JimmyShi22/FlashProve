-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/StAtZero.lean: the closing of a segment (K10): a second filler for the third parameter
of the lot's honest side (`stAt`, Honest/K10/SeatLotT.lean): the verifier's statement in front of the round "BAT", with
every row's target wiped, reckoned by the description's own fold at made-up columns. Five definitions with code; no
theorem. It is laid in no lot.

Why. This filler reads no opened column (of a `Seen`: the rounds alone): a choice of its text, not a need: where columns
are handed, a filler could fold at them. The fold over the members in front of a closing (`frontState`,
Honest/K10/StAt.lean) is owed columns at each link's round "LOC". `Block.step` (Johnson/Desc/Block.lean) asks of the
columns that it is handed their key, position and width, which the library's `groupsOf` reckons of the declared rounds
and the positions drawn: all of it is shown. So a list of columns of these keys, positions and widths can be made of the
rounds shown; no column's words are read, and zeros are laid for them.

  `zeroCols`      the columns that a list of members is owed along a chain's rounds, with zeros for words: member by
                 member, as `foldBlocks` deals the rounds: `groupsOf` at the member's own rounds
  `wipeRow`, `wipeSt`   a row, and a statement, with each row's target set to zero: the groups' open rows and the
                 oracles' sample rows
  `stAtZeroBy`    the filler's form, general in the state and in what is read off it: `frontState` at `zeroCols`
  `stAtZero`      the filler at the first chain's state: the statement wiped, and the live group's number

What it reads: the public instance (through start), the place's numbers and the rounds shown. Of its four arguments none
is a witness or a coin: by its type, Xi read as the public instance's type: what is laid for Xi no type says; the third,
a `Seen`, holds, where they are handed, the opened columns too, whose words in a real run are made of the tables: these
are not read, by `stAtZeroBy`'s text alone: no type guards it: the weaker ground; bs and start are letters too, and a
value laid for them may close over anything. The list of challenges is not read.

This filler goes INTO A LOT OF A FILLING AT WHICH ANYTHING ON HIDING IS SAID OR COUNTED: NOT BEFORE (L0) · (L1) ·
(L2) ARE THEOREMS; and, since `closeAsk`
(Honest/K10/Job.lean) makes nothing of any refusal of the filler: NEVER A LAW ON HIDING COUNTED AT A CLOSING, NOR "the
honest prover's closing", WITHOUT closeAtHand … = true BY NAME AT THE STANDS SPOKEN OF. (L0): the columns that a run's
verifier is handed have the shape of `zeroCols` at the rounds seen. (L1): the fold at two lists of columns of one shape
ends in states that agree but for targets. (L2): `closeAsk` is one at two statements that agree once wiped. On hiding
this file says nothing of its own.

At a laying bs and start are to be named: they are letters here.

Limits. Nothing is proved in this file. What is proved toward the three lemmas stands elsewhere. Of (L0), in pieces and
at the rounds that the verifier folds: `zero_shape`, `fold_take` (Honest/K10/WipeFold.lean) and `front_of_chain`
(Honest/K10/ZeroTie.lean); from these rounds to any list that begins alike as far as the members in front take rounds:
`front_same`, `zeroCols_same` (Honest/K10/RoundsStretch.lean); that the rounds seen begin so is the frame's matter and
is shown nowhere; (L1): `front_zero` (WipeFold.lean), `stAtZero_is` (Honest/K10/WipeS.lean) and, with a lemma for each
kind of member in front, `keeps_at_closing`, `stAtZero_at_closing` (Honest/K10/Wipe/SeatWipe.lean); (L2):
`closeAsk_congr`, `closeAsk_wiped` (Honest/K10/AskWipe.lean); the three joined: `closeAsk_zero` (ZeroTie.lean),
`closeAsk_at_closing` (SeatWipe.lean). Whether they meet the rulings above is the review's to say, not this file's. The
state from which the statement is read holds false targets from the second link on: whoever reads more of it than this
file does reads made-up values. No property of the protocol is claimed: nothing is said on its soundness, completeness,
binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.StAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open OnBytes (Statement Row zeroE)
open VerifiableInference.Desc (Block Place OpenedColumn foldBlocks groupsOf)
open VerifiableInference.Desc.First.Close (Par)

/-- **The columns that a list of members is owed along a chain's rounds, with zeros for words.** -/
def zeroCols {σ Cl : Type} (firstTree : Nat) : List (Block σ Cl) → List Fmt.RoundView → List OpenedColumn
  | [], _ => []
  | b :: l, rs =>
    ((groupsOf firstTree b.rounds ((rs.take b.rounds.length).map (·.drawn))).flatMap id).map
        (fun c => (c.1, c.2.1, List.replicate c.2.2 0)) ++
      zeroCols firstTree l (rs.drop b.rounds.length)

/-- A row with its target set to zero. -/
def wipeRow (r : Row) : Row := { r with target := zeroE }

/-- **A statement with every row's target set to zero.** -/
def wipeSt (S : Statement) : Statement :=
  { S with
    oracles := S.oracles.map fun o => { o with sampleRows := o.sampleRows.map wipeRow }
    groups := S.groups.map fun G => { G with rows := G.rows.map wipeRow } }

/-- **The filler's form** (its type is `StAtOf Xi`, Honest/K10/Seat.lean, written out). read: what is read off the
state. The list of challenges is not read. -/
def stAtZeroBy {σ Cl Xi : Type} (read : σ → Statement × Nat) (bs : List (Block σ Cl)) (start : Xi → σ) :
    Xi → Par → Seen → List Fmt.Drawn → Except String (Statement × Nat) :=
  fun x P seen _ =>
    (frontState 0 bs (start x) (closePlace P) seen.rounds
      (zeroCols 0 (bs.takeWhile (·.place != closePlace P)) seen.rounds)).map read

/-- **The filler**, at the first chain's state. -/
def stAtZero {Cl Xi : Type} (bs : List (Block VerifiableInference.Desc.First.S Cl))
    (start : Xi → VerifiableInference.Desc.First.S) :
    Xi → Par → Seen → List Fmt.Drawn → Except String (Statement × Nat) :=
  stAtZeroBy (fun s => (wipeSt s.st, s.live.frame.group)) bs start

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.zeroCols
#print axioms ProofFile.Honest.K10.wipeRow
#print axioms ProofFile.Honest.K10.wipeSt
#print axioms ProofFile.Honest.K10.stAtZeroBy
#print axioms ProofFile.Honest.K10.stAtZero
