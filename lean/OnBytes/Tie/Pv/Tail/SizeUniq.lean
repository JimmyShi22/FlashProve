-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Tail/SizeUniq.lean: the three inequalities `Size.Uniq` (Cb/Pv/Tail/Unique.lean) at
the sizes that are read off the verifier's record of a smallness test (`sizeOf`, SizeOf.lean), at
the characteristic of the challenge field.

Main names:
  `sizeOf_uniq`: for every record tl: (sizeOf tl).size.Uniq Cb.Gl.p. The shift and the radix of the
    packing are the verifier's constants, 2^17 and 2^20; nothing is asked of tl.
Limits: the statement is on two constants of the verifier and the prime alone.

-/
import Cb.Pv.Tail.Unique
import OnBytes.Tie.Pv.Tail.SizeOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Tie.Pv.Tail
open OnBytes OnBytes.Model Cb.Pv.Tail

/-- The three inequalities at the verifier's own sizes and the challenge field's characteristic. -/
theorem sizeOf_uniq (tl : HTailF2) : (sizeOf tl).size.Uniq Cb.Gl.p :=
  uniq_gl (s := (sizeOf tl).size) rfl rfl

end OnBytes.Tie.Pv.Tail

#print axioms OnBytes.Tie.Pv.Tail.sizeOf_uniq
