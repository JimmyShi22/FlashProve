-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Law/TableFitsFree.lean: The six: NO HYPOTHESIS; `tableFits_of`:
CONDITIONAL. Seven statements with their proofs.

What is here. OF THE ELEVEN CLAUSES OF `k4TableFits` (Honest/K4/Part.lean: the first of the four
public tests on the parts of the feed-forward layers' own rounds, the sub-protocol K4) SIX ARE TRUE
AT EVERY PUBLIC DATA, WITH NO HYPOTHESIS: seven masked sumchecks begin in the verifier's table of
rounds; seven shapes are typed; the rounds named "zero" are three in the first group and one in
another; those named "BAT-sigma" are four; those named "join" are two; behind the second token
sumcheck's first round stand its lt rounds and two more in front of the batched sumcheck's first.
`tableFits_of`: SO THE TEST IS TRUE WHERE THE FIVE OTHERS ARE, each in the test's own text. How. The
numbers of these rounds are laws on the table (Law/StartsAre.lean, Law/PtsVals.lean).

  `starts_seven`, `shapes_seven`, `zeros_count`, `bats_four`, `joins_two`, `terms_room`   the six
  `tableFits_of`   **the test, from the five others**

Not shown here. THE FIVE OTHERS: that K4 covers the plan (`covers`); that the group stands in the
list of tails; that each matrix which an earlier sub-proof has committed names an owner in front;
that each part has as many moves as the cut says; that each part spends as many mask entries as the
table's rounds send (these last two: Law/TableFitsRows.lean, with no hypothesis). Nothing on
soundness, on completeness or on any other property.

Kin. Sought: by statement, to the letter and up to the bound letters, among the theorems of the
library and of files that are no part of it yet, as they lay with the writer: no hit; no short name
of the seven stands elsewhere.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.ZeroSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes.Desc.First.K4.Honest

variable (Q : K4Pub)

theorem starts_seven : ((starts Q).length == 7) = true := by
  rw [starts_eq]
  rfl

theorem shapes_seven : ((k4Shapes Q).length == 7) = true := rfl

theorem zeros_count :
    ((rowsNamed Q .zero).length == (if Q.g == 0 then 3 else 1)) = true := by
  rw [zeros_eq]
  by_cases hg : (Q.g == 0) = true <;> simp [hg]

theorem bats_four : ((rowsNamed Q .batSigma).length == 4) = true := by
  rw [bats_eq]
  rfl

theorem joins_two : ((rowsNamed Q .join).length == 2) = true := by
  rw [joins_eq]
  rfl

theorem terms_room :
    decide ((starts Q).getD 2 0 + Q.P.y.h.lt + 2 < (starts Q).getD 3 0) = true := by
  rw [start_at Q 2 (by omega), start_at Q 3 (by omega), decide_eq_true_eq]
  simp only [k4StartAt]
  omega

variable {Q}

/-- CONDITIONAL on the five clauses named. **THE TEST ON THE TABLE IS TRUE WHERE ITS FIVE OTHER
CLAUSES ARE.** -/
theorem tableFits_of (h1 : OnBytes.Desc.First.K4.covers Q.P = true)
    (h7 : decide (Q.g < Q.P.tails.size) = true)
    (h8 : ((Q.P.tails.getD Q.g {}).mats.all fun M =>
      M.kind != 1 || (decide (256 ≤ M.aId) && decide (M.aId / 256 - 1 < Q.g) &&
        decide (M.aId % 256 < (Q.P.tails.getD (M.aId / 256 - 1) {}).mats.size))) = true)
    (h10 : ((k4RowIn Q).map (·.moves.length) == cutOf Q) = true)
    (h11 : ((k4RowIn Q).map (fun p => (p.spends.map (·.2.e)).foldl (· + ·) 0) ==
      k4SumsBy ((OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).map (·.sent)) (cutOf Q)) = true) :
    k4TableFits Q = true := by
  unfold k4TableFits
  simp only [Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, starts_seven Q⟩, shapes_seven Q⟩, zeros_count Q⟩, bats_four Q⟩, joins_two Q⟩,
    h7⟩, h8⟩, terms_room Q⟩, h10⟩, h11⟩

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.starts_seven
#print axioms ProofFile.Honest.K4.shapes_seven
#print axioms ProofFile.Honest.K4.zeros_count
#print axioms ProofFile.Honest.K4.bats_four
#print axioms ProofFile.Honest.K4.joins_two
#print axioms ProofFile.Honest.K4.terms_room
#print axioms ProofFile.Honest.K4.tableFits_of
