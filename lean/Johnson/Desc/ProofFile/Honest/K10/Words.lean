-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K10/Words.lean: what the fold's rounds send at the closing of a segment: the
shared fold's prover on words (Johnson/Prover/Link/FoldWordsE.lean, FoldWordsOf.lean)
laid into the kind's callers' parameter (`FoldWords`, Honest/K10/Job.lean). This file defines part of
the honest prover. Definitions with code; no theorem.

  `foldWords`   the two functions: "FOLD epsilon": `foldSigmaE`; a "FOLD round": `foldRoundE`: at the data
                that the closing hands over, argument for argument
  `askFits`     the named premise on the data's sizes, as a test with code: the four arrays have 2^k rows
                of l entries and 2^h rows of lz entries (`FoldSizes`, FoldWordsOf.lean, of these arrays):
                outside it the values of `foldWords` mean nothing
  `closeFold`   the fold's part at a job, with the older caller: `foldShell J foldWords`. Not the row's: that is
                `foldShellT true J foldWords` (Honest/K10/Sim.lean)

Limits. No theorem here. That these words read, in the field, as the sum of the hiding polynomial and as the honest
round polynomials is a law of Johnson/Prover/Link/FoldWordsShows.lean, under its named premise on the sizes. That
`closeAsk` makes data of these sizes is shown, under the facts on the record in front, inside Honest/K10/AskLaw.lean's
`tables_law`, at l and lz the powers of two of the layout; `askFits` itself is tried at the toys. `closeFold` does not
ask `askFits`: of the four sizes three are so by the making of the data (`closeAsk`: the row written out; the two
tables), and the fourth, of the row's coefficients on the mask table, `closeAsk` asks aloud. The cost of a round is that
text's: for tests, not for the sizes of the programs. No property of the protocol is claimed: nothing is said on its
soundness, completeness, binding or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K10.Job
import Johnson.Prover.Link.FoldWordsE

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K10
open Johnson.Prover.Link (foldSigmaE foldRoundE)

/-- **What the fold's rounds send.** -/
def foldWords : FoldWords :=
  ⟨fun A => foldSigmaE A.k A.w,
    fun A eps gs => foldRoundE A.k A.h A.c A.d A.m A.mu A.keptV A.w eps gs⟩

/-- **The data's four arrays have the sizes of the tables**: l, lz: the message lengths of the two
codes. -/
def askFits (l lz : Nat) (A : FoldAsk) : Bool :=
  A.c.size == 2 ^ A.k * l && A.m.size == 2 ^ A.k * l && A.d.size == 2 ^ A.h * lz &&
    A.mu.size == 2 ^ A.h * lz

/-- **The fold's part at a job, with the older caller. Not the row's**: that is `foldShellT true J foldWords`
(Honest/K10/Sim.lean). -/
def closeFold {V W X : Type} (J : CloseJob W) : Part V W X := foldShell J foldWords

end ProofFile.Honest.K10

#print axioms ProofFile.Honest.K10.foldWords
#print axioms ProofFile.Honest.K10.askFits
#print axioms ProofFile.Honest.K10.closeFold
