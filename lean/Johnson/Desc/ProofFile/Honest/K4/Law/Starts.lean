-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/Starts.lean: NO HYPOTHESIS. PUBLIC NUMBERS ALONE.

What is here. The honest side finds a round by its name's ordinal in the verifier's table (`starts`,
`rowsNamed`, Johnson/Desc/K4/Honest/Front.lean); Law/StartsAre.lean writes these numbers out
(`k4StartAt`, `starts_eq`, `bats_eq`); the statements on slots name the rounds by formulas of their
own (`rJ1` … `rE`, Law/SlotsUnder.lean; `rowsRound`, Law/RowsLedger.lean), which `k4_row_nums`
(Law/SlotsTrue.lean) shows to be the rounds in front of the row's parts. THESE ARE THE SAME NUMBERS:
arithmetic, over Law/StartsAre.lean's two statements. For whoever goes from the public test
`k4MakersFit` (Honest/K4/Part.lean), which asks each maker at the challenges in front of its part,
counted by the first way, to a statement that names that prefix by the last. Four statements with
their proofs.

  `k4StartAt_eq`   the seven numbers written out are rJ1 … rJ6 and rE + 1
  `k4_starts`   the first rounds of the seven masked sumchecks
  `k4_batches`   the four rounds that batch rows
  `k4_termsEnds`   the number, in the first chain, of the round that holds the second token
      sumcheck's end values

Not shown here. Numbers of rows of the verifier's table of rounds of the layers' own rounds
(sub-protocol K4), at every plan: nothing on what a round holds, nothing on any run. Nothing on
soundness, on completeness or on any other property.

Kin. Sought: by statement, to the letter and up to the bound letters, and by short name, among the
theorems of the library and of files that are no part of it yet, as they lay with the writer: no
hit, and no short name of the four stands elsewhere.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.SlotsUnder
import Johnson.Desc.ProofFile.Honest.K4.Law.StartsAre
import Johnson.Desc.ProofFile.Honest.K4.Part

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4 (k0)
open OnBytes.Desc.First.K4.Honest

/-- **The seven numbers written out are the numbers by which the statements on slots name the
sumchecks' first rounds.** -/
theorem k4StartAt_eq (Q : K4Pub) :
    k4StartAt Q 0 = rJ1 Q.g ∧ k4StartAt Q 1 = rJ2 Q.P Q.g ∧ k4StartAt Q 2 = rJ3 Q.P Q.g ∧
    k4StartAt Q 3 = rJ4 Q.P Q.g ∧ k4StartAt Q 4 = rJ5 Q.P Q.hp Q.g ∧
    k4StartAt Q 5 = rJ6 Q.P Q.hp Q.g ∧ k4StartAt Q 6 = rE Q.P Q.hp Q.g + 1 := by
  unfold rE rJ6 rJ5 rJ4 rJ3 rJ2 rJ1 rowsRound
  simp only [k4StartAt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> first | trivial | omega

/-- **The first rounds of the seven masked sumchecks**, as the honest side finds them in the
verifier's table. -/
theorem k4_starts (Q : K4Pub) :
    starts Q = [rJ1 Q.g, rJ2 Q.P Q.g, rJ3 Q.P Q.g, rJ4 Q.P Q.g, rJ5 Q.P Q.hp Q.g, rJ6 Q.P Q.hp Q.g,
      rE Q.P Q.hp Q.g + 1] := by
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := k4StartAt_eq Q
  rw [starts_eq, ← e0, ← e1, ← e2, ← e3, ← e4, ← e5, ← e6]
  rfl

/-- **The four rounds that batch rows**: the first two send the norms' sums and the row products;
the third stands in front of the batched sumcheck; the fourth in front of the merge. -/
theorem k4_batches (Q : K4Pub) :
    rowsNamed Q .batSigma = [k0 Q.g, rowsRound Q.P Q.g, rJ3 Q.P Q.g + (Q.P.y.h.lt + 3),
      rE Q.P Q.hp Q.g] := by
  obtain ⟨_, e1, _, e3, _, _, e6⟩ := k4StartAt_eq Q
  rw [bats_eq, e1, e3, e6]
  rfl

/-- **The round that holds the second token sumcheck's end values**, by its number in the first
chain. -/
theorem k4_termsEnds (Q : K4Pub) :
    k4TermsEnds Q = Q.r0 + rJ3 Q.P Q.g + Q.P.y.h.lt + 2 := by
  unfold k4TermsEnds
  rw [k4_starts]
  rfl

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4StartAt_eq
#print axioms ProofFile.Honest.K4.k4_starts
#print axioms ProofFile.Honest.K4.k4_batches
#print axioms ProofFile.Honest.K4.k4_termsEnds
