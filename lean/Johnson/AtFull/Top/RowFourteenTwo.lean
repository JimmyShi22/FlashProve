-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Top/RowFourteenTwo.lean: THE FOURTEENTH ENTRY TEST ACCEPTS, FROM TWO PREMISES:
`rowsMadeB_of_three` (Johnson/AtFull/Top/RowFourteenThree.lean) with its closed premise `rowsWB =
true` paid by `rowsWB_true` (Johnson/AtFull/Rows/Rows.lean). One call. A law file; no running text
imports it.

Statement.
  `rowsMadeB_of_two`: the four fields of Z's planner's value that do not hang on the digest are the
    written ones · the arms' test `armsB` accepts at Z's public data ⊢ rowsMadeB Z = true. General
    in Z.

Limits. Both premises are premises: shown here at no files. It stands on some eighty files, most of
them closed facts by Lean's kernel, which are imported as checked at their own compile. No use of
protocolDataWellFormed, of the pin, of the return of verify-on-bytes's planner or of the scope. The full size
alone. Nothing on soundness.
-/
import Johnson.AtFull.Top.RowFourteenThree
import Johnson.AtFull.Rows.Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFull.Top
open Johnson.G.MadeFree (freeOf)
open VerifiableInference.PlanWritten.Joined (writtenMade)
open VerifiableInference.Desc.LinkJoin

/-- **The fourteenth entry test accepts, from two premises.** -/
theorem rowsMadeB_of_two {Z : ProofFile.Pub} (e1 : freeOf Z.made.p.chains.made = writtenMade)
    (ha : armsB Z.made.p.X = true) : rowsMadeB Z = true :=
  rowsMadeB_of_three e1 ha rowsWB_true

end AtFull.Top

#print axioms AtFull.Top.rowsMadeB_of_two
