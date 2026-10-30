-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Unfolds/SizesFull.lean: `hParO` at the second hash function RETURNS AT THE STORED FULL-SIZE
EXAMPLE's THREE FILES, from one premise: the layout file's size.
  `hPar_zFull_of_lay`: from `VerifierAndGoals.storedPublicFiles.lay.size = 224975`: by `hParO_returns` and `tkOk_full`
    (Johnson/Unfolds/SecondHashFunctionTree.lean) and the two sizes that the kernel bears as they stand
    (`size_pol`, `size_KL`: Johnson/Unfolds/Sizes/).
It is p7 of the ledger of `publicOfO` (see Johnson/Unfolds/LedgerTables.lean) at `storedPublicFiles`.
Limits. THE THIRD SIZE IS A PREMISE: as it stands the kernel did not bear it in our trials
(its stack ended, also at larger stacks). Nothing on the digest's value.

-/
import Johnson.Unfolds.SecondHashFunctionTree
import Johnson.Unfolds.Sizes.Pol
import Johnson.Unfolds.Sizes.KL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Unfolds
open OnBytes
open VerifiableInference.PlanWritten

/-- **p7 at the stored full-size files, from the layout file's size.** -/
theorem hPar_zFull_of_lay (h : VerifierAndGoals.storedPublicFiles.lay.size = 224975) :
    ∃ x, hParO secondHashFunction VerifierAndGoals.storedPublicFiles.pol VerifierAndGoals.storedPublicFiles.KL (some VerifierAndGoals.storedPublicFiles.lay) = .ok x :=
  hParO_returns (by rw [size_pol]; decide) (by rw [size_pol]; exact tkOk_full.1)
    (by rw [size_KL]; exact tkOk_full.2.1) (by rw [h]; decide)
    (by rw [h]; exact tkOk_full.2.2)

end Johnson.Unfolds

#print axioms Johnson.Unfolds.hPar_zFull_of_lay
