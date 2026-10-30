-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K12/Law/OneRadB.lean: the test `oneRadB` (CondAtMade.lean) says yes where `OneRad`
(OneRadOfPlan.lean) holds.

Main names: `eq_of_sgEq`: the comparison of two stages' nine numbers is equality.
`oneRadB_of_oneRad`.
This file stands above Johnson/Bridge/ through its imports, and so above
Cb/Bridge/CodeListRSProved.lean and the files under ThirdParty/: files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Limits: a joint between a statement and a test with code. Nothing on soundness. Nothing on hiding.

-/
import Johnson.Desc.K12.Law.CondAtMade
import Johnson.Desc.K12.Law.OneRadOfPlan

set_option autoImplicit false
namespace H2K.Pub
open OnBytes OnBytes.Params OnBytes.Slice
open Johnson.Top.H (stageOf radiusOf)

theorem eq_of_sgEq {s s' : Sg} (h : sgEq s s' = true) : s = s' := by
  cases s
  cases s'
  simp only [sgEq, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨rfl, rfl⟩, rfl⟩, rfl⟩, rfl⟩ := h
  rfl

theorem oneRadB_of_oneRad {σ : Setting} {st : List StageSize} (h : OneRad σ st) :
    oneRadB σ st = true := by
  unfold oneRadB
  refine List.all_eq_true.2 fun y hy => List.all_eq_true.2 fun y' hy' => ?_
  cases e : sgEq (stageOf y.g y.t) (stageOf y'.g y'.t) with
  | false => rfl
  | true => simp [h y hy y' hy' (eq_of_sgEq e)]

end H2K.Pub

#print axioms H2K.Pub.oneRadB_of_oneRad
