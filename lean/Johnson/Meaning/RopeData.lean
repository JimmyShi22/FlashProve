-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Meaning/RopeData.lean: the library's stored rotary words, pair by pair, and the test that
one pair's list of Johnson/Meaning/RopeLists.lean is the stored one. Definitions alone.
-/
import Johnson.Meaning.RopeLists
import Inst.Model.TablesRef

set_option autoImplicit false

namespace Meaning.Rope

open OnBytes.Model.Layer (fxOne)
open Inst.Model (dec)

/-- The library's stored words of pair i: the list, over the 1024 tokens t, of the entry of Data.cos
and that of Data.sin at 64 t + i. -/
def dataRow (i : ℕ) : List (ℕ × ℕ) :=
  (List.range 1024).map fun t =>
    (dec Inst.Model.Data.cos 14 (64 * t + i), dec Inst.Model.Data.sin 14 (64 * t + i))

/-- The test on pair i, at the stored example's numbers (cs 12, theta0 500000, 64 pairs, 1024
tokens): the list recursion gives the stored words, and no stored word passes 8192. -/
def rowOK (i : ℕ) : Bool :=
  decide (rowOf 12 1024 (xAt (uOf 500000 64) i fxOne) = dataRow i) &&
    (dataRow i).all fun w => decide (w.1 ≤ 8192) && decide (w.2 ≤ 8192)

end Meaning.Rope
