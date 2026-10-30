-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NoWorkRatesLink.lean: the error count of the link's second round.



The written link is the link between two stored tables as an interactive protocol in the format's
types (OnBytes/Slice/README.md has the vocabulary).
The record of sizes and the round are variables.









Main theorem.
 `nw_entry2`   the second round, with lists of one member: its error count is 0.






What this file does not claim: that lists of at most one member, at which `nw_entry2` is stated,
are right for the tables' code, and that any description has such a round. Nothing on any other
round of the link. The bound speaks of one round: it is no bound on the chance of a false proof.

-/
import OnBytes.Slice.NoWorkRatesNum
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Slice.RatesTail

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Rom Prob Compile Compile.Batch Run Run.PQ Cb Cb.Ood Blocks
open scoped ENNReal

/-! ### The counts among the typed values -/

/-! ### The second round -/

/-- The second round: the two folded rows are sent. With lists of one member nothing can go
wrong. -/
theorem nw_entry2 (S : Sz) (d : PQ.RD) :
    ((ldSendFamErr S.lk.N S.seeds (fun _ => 1) * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) =
      0 := by
  rewrite [errSend_one, zero_mul, Nat.cast_zero]
  rfl

end OnBytes.Slice

#print axioms OnBytes.Slice.nw_entry2
