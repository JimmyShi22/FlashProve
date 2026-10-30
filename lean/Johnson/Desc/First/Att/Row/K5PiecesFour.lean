-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Row/K5PiecesFour.lean: HOW MANY PIECES THE SOFTMAX-TABLE CALL OF AN ATTENTION
SUB-PROOF's SHAPE
HAS OF EACH OF ITS TWO SEGMENT KINDS, OFF WHAT LIES ON THE SHAPE's FOUR CALLS. Laws; nothing is
evaluated.
  `fam_count`: of a family of pieces (`famAt`, Johnson/Road/Lane5AttLaid.lean) all have the
    family's segment kind, and none another.
  **`npOf_of_four`**: off `FourCalls`' clause p1 (the same file): the call number 1 has
    2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) pieces of fm, and as many of fd (`ACall.npOf`,
    OnBytes/Model/AttentionShape.lean).
Limits. General in the configuration: no value is treated. Nothing on soundness. On hiding nothing.
WHAT IT GIVES: a count of pieces, which `own_in_scope` (K5OwnInScope.lean) calls. Of K5's row's
eight binders (`k5_row_own`, K5RowOwn.lean) this file pays none: h₁ and h₂ fall in K5OwnScope.lean.
WHAT IT DOES NOT: h₄ (the walk at each plan) · hm · hZ, hG: shown at no public files by Lean's
kernel.

-/
import Johnson.Road.Lane5AttLaid

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Row
open OnBytes OnBytes.Road.L5
open OnBytes.Attention (ACall Cfg Shape Seg Piece)

variable {cf : Cfg}

/-- How many pieces of a family have the segment kind t. -/
theorem fam_count (s t : Seg) (HA c base n : ℕ) :
    ((famAt s HA c base n).filter fun p => p.seg == t).length =
      if (s == t) = true then n else 0 := by
  unfold famAt
  rw [List.filter_map]
  have e : ((fun p : Piece => p.seg == t) ∘
      fun b => ({ pcOf s HA c b with off := base + b * 2 ^ c } : Piece)) = fun _ => s == t := rfl
  rw [e, List.length_map]
  cases (s == t) <;> simp

/-- **The softmax-table call's numbers of pieces.** -/
theorem npOf_of_four {S : Shape} (F : FourCalls cf S) :
    (callAt S 1).npOf .fm = 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) ∧
      (callAt S 1).npOf .fd = 2 ^ cf.ll * (cf.H / 2 ^ cf.lgk) := by
  constructor
  · unfold ACall.npOf
    rw [← Array.length_toList, Array.toList_filter, F.p1, List.filter_append, List.length_append,
      fam_count, fam_count]
    rfl
  · unfold ACall.npOf
    rw [← Array.length_toList, Array.toList_filter, F.p1, List.filter_append, List.length_append,
      fam_count, fam_count]
    exact Nat.zero_add _

end H2K5.Row

#print axioms H2K5.Row.fam_count
#print axioms H2K5.Row.npOf_of_four
