/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao
-/
/-
Adapted from ArkLib (https://github.com/Verified-zkEVM/ArkLib), file
ArkLib/Data/Polynomial/Differential/Types.lean, commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13.
Licence: Apache-2.0, see ThirdParty/ArkLib/LICENSE.
Changes ("this Mathlib" is Mathlib at commit 5e932f97dd25535344f80f9dd8da3aab83df0fe6, which this
library uses):
* All 2 declarations of the file are kept. ArkLib's comment at the top of the file is unchanged.
* ArkLib is written for Lean 4.34 and its module system. This is an ordinary file for Lean 4.29.1:
  the words of the module system are removed, the import lines are set for this Mathlib, and the
  modules of ArkLib have the prefix ThirdParty.
-/

import Mathlib.RingTheory.MvPolynomial.Basic

/-!
# Finite-jet polynomial relations

This file defines the variables and polynomial type for relations in an independent coordinate
and a finite Hasse jet. The representation is shared by polynomial interpolation and differential
root-finding arguments.

The definitions are adapted, with permission, from `kz99/rs-ld-mca`.
-/

namespace PolynomialDifferential

/-- Variables `X, Y₀, ..., Y_d`. `none` denotes `X`; `some j` denotes `Y_j`. -/
abbrev JetVariable (d : ℕ) := Option (Fin (d + 1))

/-- A polynomial in `X, Y₀, ..., Y_d` over `F`. -/
abbrev DifferentialPolynomial (F : Type*) [CommSemiring F] (d : ℕ) :=
  MvPolynomial (JetVariable d) F

end PolynomialDifferential
