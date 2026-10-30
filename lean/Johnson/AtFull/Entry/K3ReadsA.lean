-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3ReadsA.lean: A CLOSED FACT, BY LEAN's KERNEL, no free letter: at what the
public part's makers return at the full size (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean),
the test `readsAB` (K3Places.lean) says yes: at the twelve attention segments the place of the
lookup on the calls and the structure of the approximate range proof, narrowed, are the written
`cFull i` and `mFull` (Johnson/AtFull/ProofRows/K3Full.lean). One theorem.
Limits. At the makers' twins and the written scan: the tie to the public part's own value is
`at_witnesses`' (K3AtX0.lean). That such a test can say no is shown in K3No.lean. Nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.K3Places
import Johnson.AtFull.Public.AtWitnesses

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry
open Johnson.AtFull.Public (atMakers)

/-- **The twelve attention segments' lookups on the calls.** -/
theorem readsA_W : atMakers (fun _ _ A => readsAB A) = true := by
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.readsA_W
