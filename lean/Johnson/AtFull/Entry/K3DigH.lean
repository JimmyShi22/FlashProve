-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Entry/K3DigH.lean: A CLOSED FACT, BY LEAN's KERNEL, no free letter: at what the
public part's makers return at the full size (`atMakers`, Johnson/AtFull/Public/AtWitnesses.lean),
and at the closed plan `HW` of the model's head, its ledger trimmed
(Johnson/AtFull/Head/PlanAtFull.lean), the test `digHB` (K3Places.lean) says yes: at segment 24 the
place of the lookup on the digits and the structure of the approximate range proof, narrowed, are
the written `pFull 24` and `tFull 24` (Johnson/AtFull/ProofRows/K3Full.lean). One theorem.
Limits. At the makers' twins and the written scan: the tie to the public part's own value is
`at_witnesses`' (K3AtX0.lean). That such a test can say no is shown in K3No.lean. Nothing on
soundness, on a binding of the commitment (the opening form, `BindsWith`), on correctness of
extraction, on completeness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.AtFull.Entry.K3Places
import Johnson.AtFull.Public.AtWitnesses
import Johnson.AtFull.Head.PlanAtFull

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace Johnson.AtFull.Entry
open Johnson.AtFull.Public (atMakers)

/-- **The head's segment's digits.** -/
theorem digH_W : atMakers (fun L _ _ => digHB
    { _root_.AtFull.Head.HW with Fp := _root_.AtFull.Head.HW.Fp.trimL } L.wsLay.lk) = true := by
  decide +kernel

end Johnson.AtFull.Entry

#print axioms Johnson.AtFull.Entry.digH_W
