-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HB/LLHARD/KB4/CSent.lean: conjunct 14 of the tests on the plan at WK: sentFit: what the
blocks say of a tree where it is sent agrees with the shape at every opening of it, and every tree
that is sent is opened somewhere. By an evaluation in Lean's kernel at the written declared rounds.
Negative tests: the third chain's rounds struck (a gross bend); and one number moved: a tree's width
as told.
Limits. At the closed description WK (WK.lean) and the written declared rounds alone. That a key
file's description passes the test at any public files is another file's, under named equations.
Nothing on soundness.

-/
import Johnson.HB.LLHARD.KB4.WK
import Johnson.HB.LLHARD.KB4.AtDecl

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.KB4

open VerifiableInference.Desc VerifiableInference.Desc.Key
open Johnson.KB8 (declKeyFull)

set_option maxRecDepth 1000000 in
theorem sent_full : sentAt declKeyFull (sentOf WK.first.blocksInOrder) (sentOf WK.shared.blocksInOrder)
    (sentOf WK.second.blocksInOrder) = true := by decide +kernel

theorem WK_sent : WK.sentFit = true := by
  rw [sentFit_at, WK_decl]
  exact sent_full

set_option maxRecDepth 1000000 in
theorem sent_bent : sentAt (declKeyFull.1, declKeyFull.2.1, []) (sentOf WK.first.blocksInOrder)
    (sentOf WK.shared.blocksInOrder) (sentOf WK.second.blocksInOrder) = false := by decide +kernel

set_option maxRecDepth 1000000 in
/-- One number moved: the width that the blocks tell of the first chain's second tree: 78 for 77. -/
theorem sent_width_bent : sentAt declKeyFull ((sentOf WK.first.blocksInOrder).set 1 (22, 78))
    (sentOf WK.shared.blocksInOrder) (sentOf WK.second.blocksInOrder) = false := by decide +kernel

end Johnson.KB4

#print axioms Johnson.KB4.sent_full
#print axioms Johnson.KB4.WK_sent
#print axioms Johnson.KB4.sent_bent
#print axioms Johnson.KB4.sent_width_bent
