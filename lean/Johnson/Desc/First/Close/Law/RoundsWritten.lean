-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/RoundsWritten.lean (kind K10; TOWARD THE FIRST HALF of the row
K10_rounds): THEOREMS BY AN EVALUATION IN LEAN's KERNEL: IN THE TWO WRITTEN EXAMPLES OF A PROOF
FILE's ROUNDS, EVERY ROUND THAT BEARS ONE OF THE CLOSING's THREE NAMES IS THE FORMAT's OWN ROUND OF
THAT NAME; AND HOW THE CLOSINGS STAND. Statements and proofs; the definitions and the evaluations
stand in the folder Written/, cut so that no file is heavy: along the full size's 48,293 rounds the
kernel compares CODES (`codeOf`: 1, 2, 3 for the three names) and the names only at the 136 distinct
rounds; the closings are taken from the list's nine parts (`closingsC_append`: two lists' closings
in a row, if the first list's last code is 0). NO TEXT OF THE DESCRIPTION STANDS BENEATH THIS FILE,
and no Mathlib.

K10's law (`k10_piece_fmt`, RoundsPay.lean, beside this file) asks of the closing's three written
rounds that each is the format's own: `Fmt.M2.rBatN n`, `Fmt.M1.rEps`, `Fmt.M1.rTwo` (`IsRd`): an
equation of whole entries: so no proof of work at any of them, and n the entry's number of rows; and
that n is at most 2^57 or 2^56. THE NUMBERS are the library's written lists
(Johnson/G/DryProofLit.lean: `dryProofFull`, `dryProofSmall`: the first chain's list). No file is
read here. The form follows the neighbour kind's Johnson/Desc/First/Batch/Law/Condition.lean.
  `closeRoundOk r`: the test: a round named "BAT" is `rBatN` at its own rows, opens no stored table,
    and batches 2 to 2^56 rows; one named "FOLD epsilon" is `rEps` of that name; one named "FOLD
    round" is `rTwo` of that name; each opens no stored table.
  `full_closeRounds`, `small_closeRounds`: every round of the first chain's list passes.
    `closeRound_written`: THE FORM FOR A LAW TO SPEND: of a member of one of the two lists, name by
    name.
  `foldsAt`, `closingsOf l`: at each round "BAT": its rows; and, IF THE NEXT ROUND IS "FOLD
    epsilon", how many rounds "FOLD round" follow that one (else none). `full_closings`,
    `small_closings`: 26 and 6 closings, every one in that order: the rows batched and the number of
    fold rounds: (6, 8), then (3295, 7) and (1324, 8) in turn, (1322, 8), (659, 1); and (6, 9),
    (1536, 7), (882, 9), (1536, 7), (880, 8), (656, 1).
  `closeRound_control`: THE TEST CAN SAY NO: the small size's second chain's list does not pass (a
    round "FOLD epsilon" there sends 56 bytes).
Limits. (0) THE ROW's SECOND HALF, THE ERROR AT EACH ROUND, IS NOT HERE AT ALL:
the row asks that the closing's rounds have the proved block's shape AND
that its error at each round is at most the price that the plan's accounting gives that entry. Here
is no count, no price, no field's size, no description and no declared round: the form alone, at two
written lists, by name and membership, whatever the place. What the law has on the error stands in
AtPiecePriced.lean and the files above it (beside this file): at most the cap of 128 bits a round,
from the written places' counts; that is not the plan's price either. (1) That the written lists are
a file's plan's: by their own file's head they were written from a print of the dry runs at one
made-up request and the key of zeros; at the small example a test that a build runs holds them
against the program's dry runs; at the full size no such test runs. (2) That a description's block
of kind K10 stands just at these rounds is not said: the last closing of each list is the last
group's, another kind's. (3) The other two chains' lists are not treated: in the second a round
"FOLD epsilon" sends 56 bytes (by evaluation outside this file). (4) That the rows which a closing
batches number the entry's rows is the run's matter. Nothing on soundness of the protocol.

-/
import Johnson.Desc.First.Close.Law.Written.FullOk
import Johnson.Desc.First.Close.Law.Written.SmallOk
import Johnson.Desc.First.Close.Law.Written.FullClosings
import Johnson.Desc.First.Close.Law.Written.SmallClosings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes.Params (Rounds)
open Johnson.G (dryProofFull dryProofSmall)

/-- **The form for a law to spend.** -/
theorem closeRound_written (r : Fmt.Round × List Fmt.Stored)
    (h : r ∈ dryProofFull.1 ++ dryProofSmall.1) :
    (r.1.entry.name = "BAT" → r.1 = Fmt.M2.rBatN r.1.entry.rows ∧ r.2 = [] ∧
      2 ≤ r.1.entry.rows ∧ r.1.entry.rows ≤ 2 ^ 56) ∧
    (r.1.entry.name = "FOLD epsilon" → r.1 = Fmt.M1.rEps "FOLD epsilon" ∧ r.2 = []) ∧
    (r.1.entry.name = "FOLD round" → r.1 = Fmt.M1.rTwo "FOLD round" ∧ r.2 = []) := by
  have hr : closeRoundOk r = true := by
    rcases List.mem_append.1 h with h | h
    · exact List.all_eq_true.1 full_closeRounds r h
    · exact List.all_eq_true.1 small_closeRounds r h
  unfold closeRoundOk at hr
  simp only [Bool.and_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq, decide_eq_true_eq,
    List.isEmpty_iff] at hr
  obtain ⟨⟨h1, h2⟩, h3⟩ := hr
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · rcases h1 with h1 | h1
    · exact absurd e h1
    · exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩
  · rcases h2 with h2 | h2
    · exact absurd e h2
    · exact h2
  · rcases h3 with h3 | h3
    · exact absurd e h3
    · exact h3

/-- **A round of each of the three names is a member of the small size's list**: so none of
`closeRound_written`'s three premises on a name is idle. -/
theorem closeRound_members :
    (Fmt.M2.rBatN 6, []) ∈ dryProofSmall.1 ∧ (Fmt.M1.rEps "FOLD epsilon", []) ∈ dryProofSmall.1 ∧
      (Fmt.M1.rTwo "FOLD round", []) ∈ dryProofSmall.1 := small_members

/-- **The test can say no**: the second chain's list of the small size does not pass it. -/
theorem closeRound_control : dryProofSmall.2.1.all closeRoundOk = false := small_control

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.closeRound_written
#print axioms VerifiableInference.Desc.First.Close.closeRound_members
#print axioms VerifiableInference.Desc.First.Close.closeRound_control
#print axioms VerifiableInference.Desc.First.Close.full_closings
#print axioms VerifiableInference.Desc.First.Close.small_closings
