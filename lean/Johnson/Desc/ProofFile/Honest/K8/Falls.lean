-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K8/Falls.lean: THE SMALLNESS TEST: ITS TWO TESTS ON VALUES BEHIND ITS
OWN PLACE, EACH AS A FALL IN THE FRAME's FORM (Johnson/Desc/ProofFile/Honest/Side.lean: `Fall`): a
place, a test with code on the verifier's state in front of that place and on the place's own
challenges, and a stated number. DEFINITIONS ALONE. NO LAW IS STATED HERE, AND NONE OF THE LIBRARY's
GOALS. NO NUMBER HERE IS HELD AGAINST ITS TEST.

A fall is seated at the member that refuses. In a segment with o = 0 (feed-forward, attention) or
o = 1 (the output head), behind the kind's own place (piece 5 + o):
  `batchPlace link o`   the batching's member, piece 8 + 2 o: there "K8.equations" is gathered
  `quietPlace link o`   the member without a round behind it, piece 9 + 2 o: there "K8.tests" is run
  `frontShare columns tau`   A STATED NUMBER, OF TWO HALVES: columns of 2^tau, and
                        columns * (tau - 1) of the p^3 elements of the extension field. IT IS NO
                        FALL's SHARE ANY MORE: see below
  `frontFallShare columns tau`   THE FIRST FALL's STATED NUMBER: the second half alone, times
                        ((2^128 + 1) / 2^128)^3, written as two natural numbers
  `k8FrontFall`         the first fall: `k8Front` (Honest/K8/Share.lean): a column of the drawn
                        matrix has the weight 0 at the batching element
  `k8ShareFall`         THIS KIND's SHARE OF THE SECOND: `k8Share nU`: one of seven tests on the
                        ledger's weights says no. It reads the state alone: that member has no
                        challenge. Its stated number is a parameter: `k8FallShare`
                        (Honest/K8/FallShare.lean) is meant
WHAT STANDS BEHIND THE NUMBERS. `frontShare`: its two halves are counted apart, in other files: a
column of a typed matrix, each matrix counted once, is all 0
(Johnson/Desc/K8/Honest/DeadColumn.lean); where no column is, at most columns * (tau - 1) values of
the batching element give some column the weight 0 (Honest/K8/FrontCount.lean). NOT SHOWN BY THESE
TWO: the way from the typed matrix to a written
round. (NOT SHOWN either: their sum over the two rounds, which are not neighbours; no fall states
that sum any more.) WHY THE FALL STATES THE SECOND HALF ALONE: "a column is all 0" is an event of
the kind's own round, in front of the batching: it is a mark with a place and a stated number of its
own, columns of 2^tau (Johnson/P1K8R/DeadMark.lean), and is counted once, there. WHY THE FACTOR:
where the batching element is read off a string of hash blocks and not typed, the count of the
second half bears the factor (1 + 1 / 2^128)^3 (Johnson/P1K8R/FrontBlocks.lean: `front_gate_blocks`,
by its statement): so the number that is stated is the one that is counted there, AT STATES ALL OF
WHOSE COLUMNS ARE LIVE, in that file's own scope; at typed challenges it is the larger of the two.
`k8FallShare`: the format's own counts, written down; of the seven tests one has a count in Lean
(Johnson/Desc/K8/Honest/FallFew.lean).
Limits. At the second place other kinds' tests can refuse too: whoever lays that place's falls
together lays this one among them (the frame's `fallOf` takes the first that says something). That
member has no side: which law reads its fall is the frame's to say. The pieces' numbers are written
here a second time; nothing holds them against a description's list.
-/
import Johnson.Desc.ProofFile.Honest.K8.Share
import Johnson.Desc.ProofFile.Honest.K8.FallShare
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K8
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S)

/-- The place of a segment's batching. -/
def batchPlace (link o : Nat) : Place := ⟨1, some link, 8 + 2 * o, .K9⟩

/-- The place of the member without a round behind a segment's batching. -/
def quietPlace (link o : Nat) : Place := ⟨1, some link, 9 + 2 * o, .frame⟩

/-- A stated number of two halves, at typed challenges: of the mark "a column is all 0", and of the
first fall. columns: of all matrices of the place's list. -/
def frontShare (columns tau : Nat) : Odds :=
  (⟨columns, 2 ^ tau⟩ : Odds).plus ⟨columns * (tau - 1), Code.pGold ^ 3⟩

/-- **The first fall's stated number**: columns * (tau - 1) of p^3, times
((2^128 + 1) / 2^128)^3. -/
def frontFallShare (columns tau : Nat) : Odds :=
  ⟨columns * (tau - 1) * (2 ^ 128 + 1) ^ 3, Code.pGold ^ 3 * 2 ^ 384⟩

/-- **The first fall**, at the batching's member. -/
def k8FrontFall (link o columns tau : Nat) : Fall S :=
  { place := batchPlace link o, test := k8Front, share := frontFallShare columns tau }

/-- **This kind's share of the second fall**, at the member without a round. -/
def k8ShareFall (link o : Nat) (nU : Array Nat) (share : Odds) : Fall S :=
  { place := quietPlace link o, test := fun s _ => k8Share nU s, share := share }

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.batchPlace
#print axioms ProofFile.Honest.K8.quietPlace
#print axioms ProofFile.Honest.K8.frontShare
#print axioms ProofFile.Honest.K8.frontFallShare
#print axioms ProofFile.Honest.K8.k8FrontFall
#print axioms ProofFile.Honest.K8.k8ShareFall
