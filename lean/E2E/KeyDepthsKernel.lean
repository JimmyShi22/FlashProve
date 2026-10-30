-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
E2E/KeyDepthsKernel.lean

Two closed questions for `DepthsDeclared` at the key file's shared chain, BY THE KERNEL's OWN
EVALUATION. It imports KeyDepthsGuards.lean.

  `depths_twelve`, `depths_bent`   every opening before border 12 is at `depthOf`'s depth; control
  `takes_two`, `takes_five`, `takes_bent`   the sendings' coins lie within the book; control

Limits. Closed numbers. Nothing on completeness, on soundness or on what is hidden.
-/
import E2E.KeyDepthsGuards

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 1000000

namespace AtPublicFiles.KeyOpens
open ProofFile.Honest.K14 (jobU jobOmega sendPlace)
open AtPublicFiles.KeyBook (atFull keyBook)
open AtPublicFiles.AtFiles.Full (QK)

theorem depths_twelve : depthsR keyR depthOf 12 = true := by decide +kernel

theorem depths_bent : depthsR keyR (depthOf.set 7 20) 11 = false := by decide +kernel

theorem takes_two : atFull (fun K => takesFit (keyBook K) ⟨sendPlace 2, 0⟩ (jobU ⟨QK, 0⟩)) = true := by
  decide +kernel

theorem takes_five :
    atFull (fun K => takesFit (keyBook K) ⟨sendPlace 5, 0⟩ (jobOmega ⟨QK, 0⟩)) = true := by
  decide +kernel

theorem takes_bent :
    atFull (fun K => !takesFit (keyBook K) ⟨sendPlace 3, 0⟩ (jobU ⟨QK, 0⟩)) = true := by
  decide +kernel

end AtPublicFiles.KeyOpens

#print axioms AtPublicFiles.KeyOpens.depths_twelve
#print axioms AtPublicFiles.KeyOpens.depths_bent
#print axioms AtPublicFiles.KeyOpens.takes_two
#print axioms AtPublicFiles.KeyOpens.takes_five
#print axioms AtPublicFiles.KeyOpens.takes_bent
