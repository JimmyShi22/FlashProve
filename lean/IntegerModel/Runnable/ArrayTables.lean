-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- IntegerModel/Runnable/ArrayTables.lean: the library's five reference tables (tbRef,
Inst/Model/TablesRef.lean) for the array program, read from the library's packed numbers. No theorem
says that the numbers are the rounded values of the real functions.
Core Lean and the data file Inst/Model/TablesData.lean (which imports nothing). The accessors are
copied from Inst/Model/TablesRef.lean; that they are the same functions (cos and sin: refC and refS
at layer 0) is a theorem: IntegerModel/Runnable/AtModelSizes.lean, lookupTables_eq. -/
import Inst.Model.TablesData
import IntegerModel.Runnable.ArrayModel

namespace ArrayProgram

/-- entry k of the data a, at b bits for each entry, in blocks of 1,024 entries -/
def dec (a : Array Nat) (b k : Nat) : Nat := (a.getD (k / 1024) 0 >>> (b * (k % 1024))) % 2 ^ b

def lookupTables : Tables where
  silu i := clamp 4095
    ((dec Inst.Model.Data.silu 13
        (min (max (i - 2 ^ 15) (-2 ^ 14)) (2 ^ 14 - 1) + 2 ^ 14).toNat : Int) - 4095)
  sigmoid i := 16 * min (dec Inst.Model.Data.sigm 13 (i - 2 ^ 14).toNat : Int) 4096
  exp u := max 1 (min (dec Inst.Model.Data.exp 13 u.toNat : Int) 4096)
  expRows := 2307
  cos i j := clamp 4096 ((dec Inst.Model.Data.cos 14 (64 * i + j) : Int) - 4096)
  sin i j := clamp 4096 ((dec Inst.Model.Data.sin 14 (64 * i + j) : Int) - 4096)

end ArrayProgram
