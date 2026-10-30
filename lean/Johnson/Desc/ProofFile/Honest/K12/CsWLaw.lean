-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/CsWLaw.lean: each definition of CsW.lean equals its original at
`Fld.two`, as functions, for all arguments and without hypothesis. Imports Mathlib (through
HalveWLaw.lean and FastLaw.lean).

  `foldVW_eq`      `foldVW = foldV .two`
  `foldRowsW_eq`   `foldRowsW = foldRowsA .two`
  `csW_eq`         `csW = csFast .two`
  `csW_own`        so `csW = csOwnG .two`, the original of Fmt/M1Cs.lean

By what. Both sides are unfolded, and `foldLowW_eq` (HalveWLaw.lean) rewrites one into the other.
The last by `csFast_eq` (FastLaw.lean).

Limits. Nothing on cost.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.CsW
import Johnson.Desc.ProofFile.Honest.K12.HalveWLaw
import Johnson.Desc.ProofFile.Honest.K12.FastLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Fmt (Fld)
open Fmt.M1 (E Stage foldV csOwnG)

theorem foldVW_eq : foldVW = foldV .two := by
  funext g v
  unfold foldVW foldV
  rw [foldLowW_eq]

theorem foldRowsW_eq : foldRowsW = foldRowsA .two := by
  funext g rows n
  unfold foldRowsW foldRowsA
  rw [foldVW_eq]

/-- **The two tables on 64-bit words alone are those of `csFast` at `Fld.two`.** -/
theorem csW_eq : csW = csFast .two := by
  funext old new g M Rh W Sg P Pi free pad
  unfold csW csFast
  rw [foldRowsW_eq]

/-- So they are those of `csOwnG` at `Fld.two`. -/
theorem csW_own : csW = csOwnG .two := by
  rw [csW_eq, csFast_eq]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.foldVW_eq
#print axioms ProofFile.Honest.K12.Light.foldRowsW_eq
#print axioms ProofFile.Honest.K12.Light.csW_eq
#print axioms ProofFile.Honest.K12.Light.csW_own
