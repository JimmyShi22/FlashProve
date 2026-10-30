-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/T2/Idx.lean.
The assumed statement's count at the encoded index's code [2^32, k = 446693374 as degree bound] at
the radius 2852142980, the largest with m ≤ 24 (625 k n ≤ 576 (n - e)^2), and the sum of eleven such
counts with 26 · 11 at 128 bits.
-/
import Cb.Ld.LdBldCode
import Cb.Gen.JohnsonList
import Cb.Ref.GlRefNumMca
import Cb.Ld.LdKappaTowN

set_option autoImplicit false

namespace Cb.Gl.Bld.J
open Cb.Gl.Ref Cb.Gl.Bld

theorem cnt_32_446693374_2852142980_132 : ⌊bchksBound (2 ^ 32) 446693374 2852142980⌋₊ * 2 ^ 132 ≤ Gl.p ^ 3 := by
  refine floor_of_bound _ _ _ (bchksBound_nonneg _ _ _) ?_
  have h := bchksBound_le (2 ^ 32) 446693374 2852142980 24 (5949007919755785640 / 2 ^ 64)
    (5949007919755785641 / 2 ^ 64) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine le_trans (mul_le_mul_of_nonneg_right h (by positivity)) ?_
  norm_num [Gl.p, Code.pGold]

end Cb.Gl.Bld.J
