-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K10/PaysByDigest.lean: the closing of a segment (K10): the written tables behind the comparison of triples, each held against its
maker by Lean's kernel.

  `dgW`, `digest_written`   of the 189 written messages of the first chain's sendings (`sentFirstW`) what PaysByTriples.lean
                     reads: each label is read once
  `foldsW`, `folds_written`, `bfW`, `bf_written`   the fold behind each of the 25 segments' fresh tables and the part that sends
                     what it leaves; at every other round `bfW` is the finder itself
  `lpW`, `pars_written`   the link and the piece of the 25 closings
  **`triples_written`**   at the 25 closings: the triples that the book lays are the triples that the part states
  `triples_bent`     IT CAN FAIL: against the stated list less its first member it rejects at every closing

How the written tables came: the first by a program from the text of `sentFirstW`, the other two from a print by Lean's
evaluator. Neither is trusted: each is held against its maker by the kernel.

Limits. Facts on written values alone, at the full size.
-/
import AtFullSide.K10.PaysWritten
import AtFullSide.K10.PaysByTriples

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K10
open ProofFile.Honest ProofFile.Honest.K10 AtFullSide.K14
open VerifiableInference.Desc.ReqLit (shapeFull)
open Johnson.G (codesFull2)
open P2Law.ProofPlan (WP)

/-- What is read of the 189 written messages. -/
def dgW : List Dg :=
  [⟨some 0, false, false, 0, ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 0, ⟨23214, 8411⟩⟩⟩,
   ⟨some 0, false, false, 0, ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 0, false, false, 0, ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 0, true, false, 0, ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 3, ⟨0, 236⟩⟩⟩,
   ⟨some 0, false, true, 0, ⟨⟨⟨1, some 0, 1, .K1⟩, 0⟩, 4, ⟨0, 311⟩⟩⟩,
   ⟨some 0, false, false, 1218, ⟨⟨⟨1, some 0, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 0, false, false, 1221, ⟨⟨⟨1, some 0, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 1, false, false, 1980, ⟨⟨⟨1, some 1, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 1, false, false, 1980, ⟨⟨⟨1, some 1, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 1, false, false, 1980, ⟨⟨⟨1, some 1, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 1, false, false, 1980, ⟨⟨⟨1, some 1, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 1, true, false, 1980, ⟨⟨⟨1, some 1, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 1, false, false, 3128, ⟨⟨⟨1, some 1, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 1, false, false, 3131, ⟨⟨⟨1, some 1, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 2, false, false, 3859, ⟨⟨⟨1, some 2, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 2, false, false, 3859, ⟨⟨⟨1, some 2, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 2, false, false, 3859, ⟨⟨⟨1, some 2, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 2, false, false, 3859, ⟨⟨⟨1, some 2, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 2, false, false, 3859, ⟨⟨⟨1, some 2, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 2, true, false, 3859, ⟨⟨⟨1, some 2, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 2, false, false, 5075, ⟨⟨⟨1, some 2, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 2, false, false, 5078, ⟨⟨⟨1, some 2, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 3, false, false, 5837, ⟨⟨⟨1, some 3, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 3, false, false, 5837, ⟨⟨⟨1, some 3, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 3, false, false, 5837, ⟨⟨⟨1, some 3, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 3, false, false, 5837, ⟨⟨⟨1, some 3, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 3, true, false, 5837, ⟨⟨⟨1, some 3, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 3, false, false, 6985, ⟨⟨⟨1, some 3, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 3, false, false, 6988, ⟨⟨⟨1, some 3, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 4, false, false, 7716, ⟨⟨⟨1, some 4, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 4, false, false, 7716, ⟨⟨⟨1, some 4, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 4, false, false, 7716, ⟨⟨⟨1, some 4, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 4, false, false, 7716, ⟨⟨⟨1, some 4, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 4, false, false, 7716, ⟨⟨⟨1, some 4, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 4, true, false, 7716, ⟨⟨⟨1, some 4, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 4, false, false, 8932, ⟨⟨⟨1, some 4, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 4, false, false, 8935, ⟨⟨⟨1, some 4, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 5, false, false, 9694, ⟨⟨⟨1, some 5, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 5, false, false, 9694, ⟨⟨⟨1, some 5, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 5, false, false, 9694, ⟨⟨⟨1, some 5, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 5, false, false, 9694, ⟨⟨⟨1, some 5, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 5, true, false, 9694, ⟨⟨⟨1, some 5, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 5, false, false, 10842, ⟨⟨⟨1, some 5, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 5, false, false, 10845, ⟨⟨⟨1, some 5, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 6, false, false, 11573, ⟨⟨⟨1, some 6, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 6, false, false, 11573, ⟨⟨⟨1, some 6, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 6, false, false, 11573, ⟨⟨⟨1, some 6, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 6, false, false, 11573, ⟨⟨⟨1, some 6, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 6, false, false, 11573, ⟨⟨⟨1, some 6, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 6, true, false, 11573, ⟨⟨⟨1, some 6, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 6, false, false, 12789, ⟨⟨⟨1, some 6, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 6, false, false, 12792, ⟨⟨⟨1, some 6, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 7, false, false, 13551, ⟨⟨⟨1, some 7, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 7, false, false, 13551, ⟨⟨⟨1, some 7, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 7, false, false, 13551, ⟨⟨⟨1, some 7, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 7, false, false, 13551, ⟨⟨⟨1, some 7, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 7, true, false, 13551, ⟨⟨⟨1, some 7, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 7, false, false, 14699, ⟨⟨⟨1, some 7, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 7, false, false, 14702, ⟨⟨⟨1, some 7, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 8, false, false, 15430, ⟨⟨⟨1, some 8, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 8, false, false, 15430, ⟨⟨⟨1, some 8, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 8, false, false, 15430, ⟨⟨⟨1, some 8, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 8, false, false, 15430, ⟨⟨⟨1, some 8, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 8, false, false, 15430, ⟨⟨⟨1, some 8, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 8, true, false, 15430, ⟨⟨⟨1, some 8, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 8, false, false, 16646, ⟨⟨⟨1, some 8, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 8, false, false, 16649, ⟨⟨⟨1, some 8, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 9, false, false, 17408, ⟨⟨⟨1, some 9, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 9, false, false, 17408, ⟨⟨⟨1, some 9, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 9, false, false, 17408, ⟨⟨⟨1, some 9, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 9, false, false, 17408, ⟨⟨⟨1, some 9, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 9, true, false, 17408, ⟨⟨⟨1, some 9, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 9, false, false, 18556, ⟨⟨⟨1, some 9, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 9, false, false, 18559, ⟨⟨⟨1, some 9, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 10, false, false, 19287, ⟨⟨⟨1, some 10, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 10, false, false, 19287, ⟨⟨⟨1, some 10, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 10, false, false, 19287, ⟨⟨⟨1, some 10, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 10, false, false, 19287, ⟨⟨⟨1, some 10, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 10, false, false, 19287, ⟨⟨⟨1, some 10, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 10, true, false, 19287, ⟨⟨⟨1, some 10, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 10, false, false, 20503, ⟨⟨⟨1, some 10, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 10, false, false, 20506, ⟨⟨⟨1, some 10, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 11, false, false, 21265, ⟨⟨⟨1, some 11, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 11, false, false, 21265, ⟨⟨⟨1, some 11, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 11, false, false, 21265, ⟨⟨⟨1, some 11, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 11, false, false, 21265, ⟨⟨⟨1, some 11, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 11, true, false, 21265, ⟨⟨⟨1, some 11, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 11, false, false, 22413, ⟨⟨⟨1, some 11, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 11, false, false, 22416, ⟨⟨⟨1, some 11, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 12, false, false, 23144, ⟨⟨⟨1, some 12, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 12, false, false, 23144, ⟨⟨⟨1, some 12, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 12, false, false, 23144, ⟨⟨⟨1, some 12, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 12, false, false, 23144, ⟨⟨⟨1, some 12, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 12, false, false, 23144, ⟨⟨⟨1, some 12, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 12, true, false, 23144, ⟨⟨⟨1, some 12, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 12, false, false, 24360, ⟨⟨⟨1, some 12, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 12, false, false, 24363, ⟨⟨⟨1, some 12, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 13, false, false, 25122, ⟨⟨⟨1, some 13, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 13, false, false, 25122, ⟨⟨⟨1, some 13, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 13, false, false, 25122, ⟨⟨⟨1, some 13, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 13, false, false, 25122, ⟨⟨⟨1, some 13, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 13, true, false, 25122, ⟨⟨⟨1, some 13, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 13, false, false, 26270, ⟨⟨⟨1, some 13, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 13, false, false, 26273, ⟨⟨⟨1, some 13, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 14, false, false, 27001, ⟨⟨⟨1, some 14, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 14, false, false, 27001, ⟨⟨⟨1, some 14, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 14, false, false, 27001, ⟨⟨⟨1, some 14, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 14, false, false, 27001, ⟨⟨⟨1, some 14, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 14, false, false, 27001, ⟨⟨⟨1, some 14, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 14, true, false, 27001, ⟨⟨⟨1, some 14, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 14, false, false, 28217, ⟨⟨⟨1, some 14, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 14, false, false, 28220, ⟨⟨⟨1, some 14, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 15, false, false, 28979, ⟨⟨⟨1, some 15, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 15, false, false, 28979, ⟨⟨⟨1, some 15, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 15, false, false, 28979, ⟨⟨⟨1, some 15, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 15, false, false, 28979, ⟨⟨⟨1, some 15, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 15, true, false, 28979, ⟨⟨⟨1, some 15, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 15, false, false, 30127, ⟨⟨⟨1, some 15, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 15, false, false, 30130, ⟨⟨⟨1, some 15, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 16, false, false, 30858, ⟨⟨⟨1, some 16, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 16, false, false, 30858, ⟨⟨⟨1, some 16, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 16, false, false, 30858, ⟨⟨⟨1, some 16, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 16, false, false, 30858, ⟨⟨⟨1, some 16, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 16, false, false, 30858, ⟨⟨⟨1, some 16, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 16, true, false, 30858, ⟨⟨⟨1, some 16, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 16, false, false, 32074, ⟨⟨⟨1, some 16, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 16, false, false, 32077, ⟨⟨⟨1, some 16, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 17, false, false, 32836, ⟨⟨⟨1, some 17, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 17, false, false, 32836, ⟨⟨⟨1, some 17, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 17, false, false, 32836, ⟨⟨⟨1, some 17, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 17, false, false, 32836, ⟨⟨⟨1, some 17, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 17, true, false, 32836, ⟨⟨⟨1, some 17, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 17, false, false, 33984, ⟨⟨⟨1, some 17, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 17, false, false, 33987, ⟨⟨⟨1, some 17, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 18, false, false, 34715, ⟨⟨⟨1, some 18, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 18, false, false, 34715, ⟨⟨⟨1, some 18, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 18, false, false, 34715, ⟨⟨⟨1, some 18, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 18, false, false, 34715, ⟨⟨⟨1, some 18, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 18, false, false, 34715, ⟨⟨⟨1, some 18, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 18, true, false, 34715, ⟨⟨⟨1, some 18, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 18, false, false, 35931, ⟨⟨⟨1, some 18, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 18, false, false, 35934, ⟨⟨⟨1, some 18, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 19, false, false, 36693, ⟨⟨⟨1, some 19, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 19, false, false, 36693, ⟨⟨⟨1, some 19, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 19, false, false, 36693, ⟨⟨⟨1, some 19, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 19, false, false, 36693, ⟨⟨⟨1, some 19, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 19, true, false, 36693, ⟨⟨⟨1, some 19, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 19, false, false, 37841, ⟨⟨⟨1, some 19, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 19, false, false, 37844, ⟨⟨⟨1, some 19, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 20, false, false, 38572, ⟨⟨⟨1, some 20, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 20, false, false, 38572, ⟨⟨⟨1, some 20, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 20, false, false, 38572, ⟨⟨⟨1, some 20, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 20, false, false, 38572, ⟨⟨⟨1, some 20, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 20, false, false, 38572, ⟨⟨⟨1, some 20, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 20, true, false, 38572, ⟨⟨⟨1, some 20, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 20, false, false, 39788, ⟨⟨⟨1, some 20, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 20, false, false, 39791, ⟨⟨⟨1, some 20, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 21, false, false, 40550, ⟨⟨⟨1, some 21, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 21, false, false, 40550, ⟨⟨⟨1, some 21, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 21, false, false, 40550, ⟨⟨⟨1, some 21, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 21, false, false, 40550, ⟨⟨⟨1, some 21, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 21, true, false, 40550, ⟨⟨⟨1, some 21, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 21, false, false, 41698, ⟨⟨⟨1, some 21, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 21, false, false, 41701, ⟨⟨⟨1, some 21, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 22, false, false, 42429, ⟨⟨⟨1, some 22, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 22, false, false, 42429, ⟨⟨⟨1, some 22, 1, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 22, false, false, 42429, ⟨⟨⟨1, some 22, 1, .K2⟩, 0⟩, 2, ⟨22776, 8411⟩⟩⟩,
   ⟨some 22, false, false, 42429, ⟨⟨⟨1, some 22, 1, .K2⟩, 0⟩, 3, ⟨1974, 0⟩⟩⟩,
   ⟨some 22, false, false, 42429, ⟨⟨⟨1, some 22, 1, .K2⟩, 0⟩, 4, ⟨660, 0⟩⟩⟩,
   ⟨some 22, true, false, 42429, ⟨⟨⟨1, some 22, 1, .K2⟩, 0⟩, 5, ⟨0, 236⟩⟩⟩,
   ⟨some 22, false, false, 43645, ⟨⟨⟨1, some 22, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 22, false, false, 43648, ⟨⟨⟨1, some 22, 6, .K1⟩, 0⟩, 0, ⟨6792, 0⟩⟩⟩,
   ⟨some 23, false, false, 44407, ⟨⟨⟨1, some 23, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 23, false, false, 44407, ⟨⟨⟨1, some 23, 1, .K2⟩, 0⟩, 1, ⟨1974, 0⟩⟩⟩,
   ⟨some 23, false, false, 44407, ⟨⟨⟨1, some 23, 1, .K2⟩, 0⟩, 2, ⟨660, 0⟩⟩⟩,
   ⟨some 23, false, false, 44407, ⟨⟨⟨1, some 23, 1, .K2⟩, 0⟩, 3, ⟨9198, 8411⟩⟩⟩,
   ⟨some 23, true, false, 44407, ⟨⟨⟨1, some 23, 1, .K2⟩, 0⟩, 4, ⟨0, 234⟩⟩⟩,
   ⟨some 23, false, false, 45555, ⟨⟨⟨1, some 23, 4, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 23, false, false, 45558, ⟨⟨⟨1, some 23, 6, .K1⟩, 0⟩, 0, ⟨3069, 0⟩⟩⟩,
   ⟨some 24, false, false, 46287, ⟨⟨⟨1, some 24, 2, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 24, false, false, 46287, ⟨⟨⟨1, some 24, 2, .K2⟩, 0⟩, 1, ⟨660, 0⟩⟩⟩,
   ⟨some 24, false, false, 46287, ⟨⟨⟨1, some 24, 2, .K2⟩, 0⟩, 2, ⟨22557, 8411⟩⟩⟩,
   ⟨some 24, true, false, 46287, ⟨⟨⟨1, some 24, 2, .K2⟩, 0⟩, 3, ⟨0, 236⟩⟩⟩,
   ⟨some 24, false, false, 47451, ⟨⟨⟨1, some 24, 5, .K1⟩, 0⟩, 0, ⟨0, 220⟩⟩⟩,
   ⟨some 24, false, false, 47454, ⟨⟨⟨1, some 24, 7, .K1⟩, 0⟩, 0, ⟨5259, 0⟩⟩⟩,
   ⟨some 25, false, false, 48235, ⟨⟨⟨1, none, 1, .K2⟩, 0⟩, 0, ⟨0, 439⟩⟩⟩,
   ⟨some 25, true, false, 48235, ⟨⟨⟨1, none, 1, .K2⟩, 0⟩, 1, ⟨0, 222⟩⟩⟩,
   ⟨none, false, false, 48290, ⟨⟨⟨1, none, 4, .K1⟩, 0⟩, 0, ⟨0, 3882⟩⟩⟩,
   ⟨none, true, false, 48290, ⟨⟨⟨1, none, 4, .K1⟩, 0⟩, 1, ⟨0, 121⟩⟩⟩]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **The written rows are the messages' own.** -/
theorem digest_written : sentFirstW.map dg = dgW := by
  unfold dg linkOf
  simp only [Johnson.Unfolds.splitOn_eq, Johnson.Unfolds.slice_toNat?_eq]
  decide +kernel

/-- The round of each segment's fresh table, the fold behind it, and the part that sends what the
fold leaves. -/
def foldsW : List (Nat × Addr × Addr) :=
  [(0, ⟨⟨1, some 0, 11, .K10⟩, 0⟩, ⟨⟨1, some 1, 1, .K2⟩, 0⟩),
   (1980, ⟨⟨1, some 1, 11, .K10⟩, 0⟩, ⟨⟨1, some 2, 1, .K2⟩, 0⟩),
   (3859, ⟨⟨1, some 2, 11, .K10⟩, 0⟩, ⟨⟨1, some 3, 1, .K2⟩, 0⟩),
   (5837, ⟨⟨1, some 3, 11, .K10⟩, 0⟩, ⟨⟨1, some 4, 1, .K2⟩, 0⟩),
   (7716, ⟨⟨1, some 4, 11, .K10⟩, 0⟩, ⟨⟨1, some 5, 1, .K2⟩, 0⟩),
   (9694, ⟨⟨1, some 5, 11, .K10⟩, 0⟩, ⟨⟨1, some 6, 1, .K2⟩, 0⟩),
   (11573, ⟨⟨1, some 6, 11, .K10⟩, 0⟩, ⟨⟨1, some 7, 1, .K2⟩, 0⟩),
   (13551, ⟨⟨1, some 7, 11, .K10⟩, 0⟩, ⟨⟨1, some 8, 1, .K2⟩, 0⟩),
   (15430, ⟨⟨1, some 8, 11, .K10⟩, 0⟩, ⟨⟨1, some 9, 1, .K2⟩, 0⟩),
   (17408, ⟨⟨1, some 9, 11, .K10⟩, 0⟩, ⟨⟨1, some 10, 1, .K2⟩, 0⟩),
   (19287, ⟨⟨1, some 10, 11, .K10⟩, 0⟩, ⟨⟨1, some 11, 1, .K2⟩, 0⟩),
   (21265, ⟨⟨1, some 11, 11, .K10⟩, 0⟩, ⟨⟨1, some 12, 1, .K2⟩, 0⟩),
   (23144, ⟨⟨1, some 12, 11, .K10⟩, 0⟩, ⟨⟨1, some 13, 1, .K2⟩, 0⟩),
   (25122, ⟨⟨1, some 13, 11, .K10⟩, 0⟩, ⟨⟨1, some 14, 1, .K2⟩, 0⟩),
   (27001, ⟨⟨1, some 14, 11, .K10⟩, 0⟩, ⟨⟨1, some 15, 1, .K2⟩, 0⟩),
   (28979, ⟨⟨1, some 15, 11, .K10⟩, 0⟩, ⟨⟨1, some 16, 1, .K2⟩, 0⟩),
   (30858, ⟨⟨1, some 16, 11, .K10⟩, 0⟩, ⟨⟨1, some 17, 1, .K2⟩, 0⟩),
   (32836, ⟨⟨1, some 17, 11, .K10⟩, 0⟩, ⟨⟨1, some 18, 1, .K2⟩, 0⟩),
   (34715, ⟨⟨1, some 18, 11, .K10⟩, 0⟩, ⟨⟨1, some 19, 1, .K2⟩, 0⟩),
   (36693, ⟨⟨1, some 19, 11, .K10⟩, 0⟩, ⟨⟨1, some 20, 1, .K2⟩, 0⟩),
   (38572, ⟨⟨1, some 20, 11, .K10⟩, 0⟩, ⟨⟨1, some 21, 1, .K2⟩, 0⟩),
   (40550, ⟨⟨1, some 21, 11, .K10⟩, 0⟩, ⟨⟨1, some 22, 1, .K2⟩, 0⟩),
   (42429, ⟨⟨1, some 22, 11, .K10⟩, 0⟩, ⟨⟨1, some 23, 1, .K2⟩, 0⟩),
   (44407, ⟨⟨1, some 23, 11, .K10⟩, 0⟩, ⟨⟨1, some 24, 2, .K2⟩, 0⟩),
   (46287, ⟨⟨1, some 24, 13, .K10⟩, 0⟩, ⟨⟨1, none, 1, .K2⟩, 0⟩)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem folds_written :
    (foldsW.all fun x => behindFold (planOf WP.first.blocksInOrder) x.1 == some x.2) = true := by
  decide +kernel

/-- The finder, read off the written table where that has the round. -/
def bfW (r : Nat) : Option (Addr × Addr) :=
  match foldsW.find? fun x => x.1 == r with
  | some x => some x.2
  | none => behindFold (planOf WP.first.blocksInOrder) r

theorem bf_written : behindFold (planOf WP.first.blocksInOrder) = bfW := by
  funext r
  unfold bfW
  cases hf : foldsW.find? fun x => x.1 == r with
  | none => rfl
  | some x =>
    have h0 : (x.1 == r) = true :=
      List.find?_some (p := fun y : Nat × Addr × Addr => y.1 == r) hf
    have h1 : x.1 = r := beq_iff_eq.1 h0
    have h2 := beq_iff_eq.1 (List.all_eq_true.1 folds_written x (List.mem_of_find?_eq_some hf))
    rw [← h1]
    exact h2

/-- The link and the piece of the 25 closings. -/
def lpW : List (Nat × Nat) := (List.range 24).map (fun l => (l, 11)) ++ [(24, 13)]

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
theorem pars_written : parsW.map (fun P => (P.link, P.piece)) = lpW := by decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- **At the 25 closings the triples that the book lays are the triples that the part states.** -/
theorem triples_written : (lpW.all fun x =>
    pickAt bfW dgW ⟨⟨1, some x.1, x.2, .K10⟩, 0⟩ ==
      borneOf shapeFull codesFull2 (fun j t => (sendW j).getD t default) x.1) = true := by
  decide +kernel

set_option maxRecDepth 1000000 in
set_option maxHeartbeats 0 in
/-- IT CAN FAIL: against the stated list less its first member it rejects at every closing. -/
theorem triples_bent : (lpW.any fun x =>
    pickAt bfW dgW ⟨⟨1, some x.1, x.2, .K10⟩, 0⟩ ==
      (borneOf shapeFull codesFull2 (fun j t => (sendW j).getD t default) x.1).drop 1) = false := by
  decide +kernel

end AtFullSide.K10

#print axioms AtFullSide.K10.digest_written
#print axioms AtFullSide.K10.folds_written
#print axioms AtFullSide.K10.bf_written
#print axioms AtFullSide.K10.pars_written
#print axioms AtFullSide.K10.triples_written
#print axioms AtFullSide.K10.triples_bent
