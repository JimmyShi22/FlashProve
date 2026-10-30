-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Flat/Last/RowZeroWeights.lean: THE ROW WEIGHTS' TWO READERS ARE ONE, WHERE (Eval) IS LAID:
the table's owner's gLaid Pw get q (Johnson/Desc/Sound/AtOcEnd.lean: off the reader laidOf) and row
0's gOfS (get q).2 (Johnson/Desc/Third/Law/Row0DotOm.lean: off the record's first pending row). One
theorem: a joining.

OBJECT   the two definitions' own texts.
USER     the tie g' = g of dot_at_point (Johnson/Flat/Last/RowZeroAtJoint.lean), at the owner's
         meant letter gOf := gLaid Pw get. Nobody calls it yet.
FIELD    leads3_last_chains_table (Johnson/Goal/Skeleton/ProofFile.lean), through row 0's dot.

  gLaid_is_gOfS   EvalLaid Pw (get q).2 → gLaid Pw get q = gOfS (get q).2: by laidOf_ok
                  (Johnson/Desc/K13/Law/LaidAt.lean): the record's rows are the one row that the
                  reader gives.
What is not claimed. Outside EvalLaid the two part (0 against the first pending row's weights).
Nothing on soundness.

-/
import Johnson.Desc.Sound.AtOcEnd
import Johnson.Desc.Third.Law.Row0DotOm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc
open VerifiableInference.Desc.Third.Law (gOfS)
open VerifiableInference.Desc.K13 (Where)
open VerifiableInference.Desc.K13.Law (EvalLaid laidOf_ok)
open _root_.Desc.K14.Law (gLaid)

/-- **The row weights' two readers are one, where (Eval) is laid.** -/
theorem gLaid_is_gOfS {P₁ P₀ : Type} (Pw : Where) (get : P₁ → P₀ × First.S) (q : P₁)
    (hL : EvalLaid Pw (get q).2) : gLaid Pw get q = gOfS (get q).2 := by
  obtain ⟨D, hD, _, hrows, _⟩ := laidOf_ok hL
  funext y
  unfold gLaid gOfS
  rw [hD, hrows]
  rfl

end VerifiableInference.OnPublicFiles.Last
