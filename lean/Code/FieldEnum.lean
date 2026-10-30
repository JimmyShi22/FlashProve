-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Code/FieldEnum.lean: enumerations, as data (`FinEnum` instances), of cubic extensions.

A cubic extension `Cubic K c` (Code/Field.lean) is enumerated through its three coordinates.
Such instances are what `Num.ofFinEnum` (Iop/Num.lean) and `Ser.ofFinEnum` (Iop/Ser.lean) take.
-/
import Code.Field
import Mathlib.Data.FinEnum

namespace Code

instance Cubic.finEnum (K : Type) (c : K) [FinEnum K] : FinEnum (Cubic K c) :=
  FinEnum.ofEquiv (K × K × K) Cubic.equivProd

end Code
