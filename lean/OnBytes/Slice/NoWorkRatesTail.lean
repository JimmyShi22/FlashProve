-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/NoWorkRatesTail.lean: a kind of round of the written link whose error count is at
most 2^-128 as a share of its challenge values.


The written link is the link between two stored tables as an interactive protocol in the format's
types (OnBytes/Slice/README.md has the vocabulary).

This file treats a round that draws one element of
the extension field.
OnBytes/Slice/RatesTail.lean has the like at the small test configuration, with 2^-31. The round is
a variable that meets `NwRound` (OnBytes/Slice/NoWorkRatesRound.lean).

Main theorem.
 `nw_elem_round`   a round that draws one element, with five hash blocks and a count of at most
                  2^32.




What this file does not claim: that the count is right for the codes, and that any
description has such rounds. Nothing on the hash function: a share is a count among all strings of
hash blocks. The bound speaks of one round: it is no bound on the chance of a false proof.
-/
import OnBytes.Slice.NoWorkRatesNum
import OnBytes.Slice.NoWorkRatesRound
import OnBytes.Slice.RatesTail

set_option autoImplicit false

namespace OnBytes.Slice
open Iop Prob Run
open scoped ENNReal

/-- A round that draws one element, with five hash blocks, no test bit and a count e of at most
2^32: e * w is at most 2^-128 times the number of the round's challenge values (w: the number in the
law of the format's sampler). -/
theorem nw_elem_round (d : PQ.RD) (hd : NwRound d [.elem, .trits 0] 5) (e : ℕ) (he : e ≤ 2 ^ 32) :
    ((e * (bsRound .two d.entry d.kind).w : ℕ) : ℝ≥0∞) ≤
      (2 : ℝ≥0∞)⁻¹ ^ 128 * (Fintype.card (wRound d).Chal : ℝ≥0∞) :=
  nw_entry hd e e (Fintype.card GE) card_GE_pos (le_of_eq (congrArg (e * ·) nVals_elem.symm))
    (nw_elem_num e _ he card_GE_big)

end OnBytes.Slice

#print axioms OnBytes.Slice.nw_elem_round
