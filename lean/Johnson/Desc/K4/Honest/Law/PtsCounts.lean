-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K4/Honest/Law/PtsCounts.lean.

What is here. How many rows the four stretches of the verifier's table of rounds have that
Johnson/Desc/K4/Honest/Law/PtsSizes.lean names, as numbers of the plan. Statements and proofs.

  `rowB`   the number of the table's first batching round: 3 in the first group of layers, else 1
  `masked_rows`, `layer_rows`   a masked sumcheck's rounds; a product level's
  `preJoin_length`, `preTerms_length`, `preStack_length`, `preJoin2_length`   the four stretches

Limits. Counts of rows alone. No property is claimed.
-/
import Johnson.Desc.K4.Honest.Law.PtsSizes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Desc.First.K4.Honest.PtsLaw
open OnBytes.Desc.First.K4 (masked layerRds)

/-- The number of the table's first batching round. -/
def rowB (Q : K4Pub) : Nat := if Q.g == 0 then 3 else 1

/-- A masked sumcheck of k variables has k + 3 rounds. -/
theorem masked_rows (k a b c : Nat) : (masked k a b c).length = k + 3 := by
  simp [masked]

/-- A product level of mu variables has mu + 4 rounds. -/
theorem layer_rows (mu : Nat) : (layerRds mu).length = mu + 4 := by
  simp [layerRds, masked_rows]

/-- The first round named "join" is row number rowB + 1. -/
theorem preJoin_length (Q : K4Pub) : (preJoin Q).length = rowB Q + 1 := by
  unfold preJoin rowB
  split <;> rfl

/-- The second token sumcheck begins at this row. -/
theorem preTerms_length (Q : K4Pub) :
    (preTerms Q).length = rowB Q + Q.P.rd.muV + Q.P.y.h.lt + 10 := by
  simp only [preTerms, List.length_append, preJoin_length, layer_rows, masked_rows,
    List.length_cons, List.length_nil]
  omega

/-- The batched sumcheck begins at this row. -/
theorem preStack_length (Q : K4Pub) :
    (preStack Q).length = rowB Q + Q.P.rd.muV + 2 * Q.P.y.h.lt + 14 := by
  simp only [preStack, List.length_append, preTerms_length, masked_rows, List.length_cons,
    List.length_nil]
  omega

/-- The second round named "join" is this row. -/
theorem preJoin2_length (Q : K4Pub) :
    (preJoin2 Q).length =
      rowB Q + Q.P.rd.muV + 2 * Q.P.y.h.lt + Q.hp.lamS + Q.P.rd.muH + 21 := by
  simp only [preJoin2, List.length_append, preStack_length, layer_rows, masked_rows]
  omega

end OnBytes.Desc.First.K4.Honest.PtsLaw

#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.masked_rows
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.layer_rows
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin_length
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preTerms_length
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preStack_length
#print axioms OnBytes.Desc.First.K4.Honest.PtsLaw.preJoin2_length
