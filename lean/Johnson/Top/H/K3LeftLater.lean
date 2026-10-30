-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/K3LeftLater.lean: the kind "lookup" (K3): THE CROSSING: the four statements of part
(II) of Johnson/Top/H/K3LeftStatement.lean, proved: HeardIs passes to later ledgers; so the row out
and its fourth item at a later ledger give those at an earlier one; what stands for some rounds at a
ledger stands for them at a later one. Theorems with their proofs.

Limits. Ties: no error term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Top.H.K3LeftStatement

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel
open Cb.Fo.Pin

/-- HeardIs passes to later ledgers: four of its fields name the ledger, each through a sentence on
all later ledgers. -/
theorem heardIsLater : HeardIsLater := fun K _ ρ g F G En hL h =>
  { h with
    rows := fun i hi => RowIs.later ρ (h.rows i hi) hL
    lvStart := FormIs.later ρ h.lvStart hL
    sBitAt := FormIs.later ρ h.sBitAt hL
    cEnd := FormIs.later ρ h.cEnd hL }

/-- **The row out at a later ledger gives the row out at an earlier one.** -/
theorem k3OutBack : K3OutBack := fun K _ ρ h lm first ν Kv g F G hL H =>
  ⟨fun rs hI => H.1 rs (heardIsLater K ρ g F G _ hL hI),
    fun rs hI => H.2.1 rs (heardIsLater K ρ g F G _ hL hI),
    fun rs hI => H.2.2 rs (heardIsLater K ρ g F G _ hL hI)⟩

theorem k3OutRiderBack : K3OutRiderBack := fun r lm first st m g F G hL H rs hI =>
  H rs (heardIsLater _ Reading.gl g F G _ hL hI)

theorem k3StandsLater : K3StandsLater := fun K _ ρ h lm first g F G hL H =>
  H.elim fun rs hI => ⟨rs, heardIsLater K ρ g F G _ hL hI⟩

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.heardIsLater
#print axioms VerifiableInference.OnPublicFiles.k3OutBack
#print axioms VerifiableInference.OnPublicFiles.k3OutRiderBack
#print axioms VerifiableInference.OnPublicFiles.k3StandsLater
