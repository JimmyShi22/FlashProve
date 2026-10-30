-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Loose.H2K12.K12RowSkelW
/-
K12RowSkelWNo.lean: THE NEGATIVE TEST
OF skelL_full (K12RowSkelW.lean), alone in its file, since it is an evaluation in Lean's kernel.
  skelL_full_no    at the written member with its list idx one pair shorter the skeleton of the
                   lot's sub-protocol is NOT k12SkelW: the comparison rejects. A true statement
                   about a bent value. The bend is planL_full_no's (K12RowAlone.lean): there
                   the test on the list of rounds rejects
No soundness statement. Nothing on hiding.

-/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K12

open H2K.Member (piLFull)

theorem skelL_full_no :
    decide (ProofFile.Sk.skel (lotB { piLFull with idx := piLFull.idx.dropLast }) = k12SkelW) =
      false := by
  decide +kernel

end H2K12

#print axioms H2K12.skelL_full_no
