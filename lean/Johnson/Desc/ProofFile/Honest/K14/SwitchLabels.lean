-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/SwitchLabels.lean: THE VERDICTS OF THE BOOK's MAKERS' TEST
isSwitch (Honest/BookRows.lean) AT THE NINE LABELS OF THE WRITTEN LIST OF THE SHARED CHAIN's
SENDINGS (proofSends1, Johnson/G/SendsWritten.lean): "the folded row" and "Omega" are no switch's;
the seven behind are. Two statements with their proofs; no definition.

How. isSwitch counts the pieces into which String.splitOn cuts the label. Lean's kernel does not
evaluate String.splitOn; the library has it in a form that the kernel evaluates, with the equation
between the two at all strings (splitOn_eq, Johnson/Unfolds/SplitOn.lean): one rewriting with that,
then an evaluation by the kernel.

  two_no_switch   isSwitch rejects "the folded row" and "Omega"
  rest_switches   it accepts every label behind the second in the written list

What is not claimed. Nothing on any other label. No property.
-/
import Johnson.Desc.ProofFile.Honest.BookRows
import Johnson.G.SendsWritten
import Johnson.Unfolds.SplitOn

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14

/-- The maker's test rejects the two sendings' labels. -/
theorem two_no_switch : isSwitch "the folded row" = false ∧ isSwitch "Omega" = false := by
  simp only [isSwitch, Johnson.Unfolds.splitOn_eq]
  decide +kernel

/-- It accepts every label behind the second in the written list of the shared chain's sendings. -/
theorem rest_switches :
    ((Johnson.G.proofSendsFull.2.1.sends.drop 2).all fun s => isSwitch s.label) = true := by
  simp only [isSwitch, Johnson.Unfolds.splitOn_eq]
  decide +kernel

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.two_no_switch
#print axioms ProofFile.Honest.K14.rest_switches
