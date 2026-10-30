-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Small/RoundsOfCut.lean: CONDITIONAL. One statement with its proof; no
definition. No kind is named in the code. By the writers of the feed-forward layers' own rounds
(sub-protocol K4). It stands over Honest/BookCutsLaw.lean.

What is here. ONE OF THE TESTS THAT `chainSteps` (Honest/Frame.lean) MAKES AT A SUB-PROTOCOL WITH A
PROVER's SIDE, THAT ON THE NUMBER OF ROUNDS, FOLLOWS FROM hc: where the numbers of moves of the
side's parts, which are the right side of its test on the cut, are the sub-protocol's cut
(`partsCut`, Honest/BookOf.lean), the side has as many rounds as the sub-protocol. The cut adds up
to the number of the sub-protocol's rounds: `partsCut_sum` (Honest/BookCutsLaw.lean, of other
writers), called here; a side's number of rounds (`Placed.rounds`) is the sum of its parts' numbers
of moves.

  `rounds_of_cut`   **THE STATEMENT.**

Not shown here. THAT ANY SIDE's PARTS HAVE THE CUT AS THEIR NUMBERS OF MOVES: hc is a premise, each
kind's own. hc is not the test on the cut: that test compares the same list with the book's cut at
the place, and no book is named here. The other tests of `chainSteps`. Nothing on soundness, on
completeness or on any other property.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.BookCutsLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block)

/-- CONDITIONAL on hc. **A SIDE WHOSE PARTS' NUMBERS OF MOVES ARE THE SUB-PROTOCOL's CUT HAS AS MANY
ROUNDS AS THE SUB-PROTOCOL.** -/
theorem rounds_of_cut {V W X S Cl : Type} {g : Placed V W X} {b : Block S Cl}
    (hc : g.parts.map (·.moves.length) = partsCut b) : g.rounds = b.rounds.length := by
  have h1 := (partsCut_sum b).1
  rw [← hc, List.foldl_map] at h1
  exact h1

end ProofFile.Honest

#print axioms ProofFile.Honest.rounds_of_cut
