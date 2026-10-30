-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/AtFull/Rows/TailHome.lean: THE TAIL RETURNS AT rowsW's WRITTEN VALUES: the premise ht of
rows_of_partsL (Twin.lean), to the letter, WITH NO PREMISE LEFT: tailL_of_facts (TailAtW.lean) at
the seven closed facts, one a chain, each decided by Lean's kernel in a file of its own (CT0 … CT6).
One theorem. A law file; no running text imports it.
  `tailL_cut`  MAIN: (tailFrom cW sW (twinsL cW (List.replicate 25 1) 13)).toOption.isSome = true.
Why seven facts and not one. The same sentence as ONE closed fact (no such proof is in this library)
is costly: of two reported runs of Lean's kernel one died after 488 s at 56.4 GB (its cap: 64 GiB),
one decided it in 915 s at a peak of 84.2 GB (not measured again here).
Limits. At the written values alone, and at twinsL: its chains "key 0" and "proof 0" are the light
twins (Twin.lean), which are no part of the protocol; rows_of_partsL carries the answer to the real
chains, at eleven more premises. That rowsWB = true is not said here: this is one of its premises.
It stands on p0_W, p1_W, p2_W and sendsFrom_of_parts (see TailAtW.lean). Nothing on what a radius
means. Nothing on soundness or on hiding.

-/
import Johnson.AtFull.Rows.CT0
import Johnson.AtFull.Rows.CT1
import Johnson.AtFull.Rows.CT2
import Johnson.AtFull.Rows.CT3
import Johnson.AtFull.Rows.CT4
import Johnson.AtFull.Rows.CT5
import Johnson.AtFull.Rows.CT6

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.LinkJoin

/-- **The tail returns at the written values, at twinsL (two of the seven are light twins).** -/
theorem tailL_cut :
    (tailFrom cW sW (twinsL cW (List.replicate 25 1) 13)).toOption.isSome = true :=
  tailL_of_facts tail_key0 tail_key1 tail_key2 tail_entry tail_proof0 tail_proof1 tail_proof2

end VerifiableInference.Desc.LinkJoin

#print axioms VerifiableInference.Desc.LinkJoin.tailL_cut
