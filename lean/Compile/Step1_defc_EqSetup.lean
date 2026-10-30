-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Step1_defc_EqSetup.lean: the renumbering of tokens (`up`, `down`:
Compile/Step1_life2_Virt.lean; words of this library: lean/GLOSSARY.md) at N₀ = δ = 0 is the
identity (`up_zz`, `down_zz`, `virtL_zero`).

Notation: `N₀`, `δ`: natural numbers; "the δ strings after the first N₀" (the head of
Compile/Step1_life2_Virt.lean); `up N₀ δ v`: `if v < N₀ then v else v + δ`; `down N₀ δ t`:
`if t < N₀ then t else t - δ` (Compile/Step1_life2_Virt.lean).

Limits: it does not prove a statement on the setup. Compile/Batch/EqSetup.lean uses this file.
-/
import Compile.Step1_defc_L
import Compile.Step1_defc_Prob
import Compile.Step1_life2_Chall
import Iop.ShapeKit

noncomputable section

open Rom Iop Prob

namespace Compile.DefC
open Compile.Life2 (up down)

namespace EqSetup

theorem up_zz (v : ℕ) : up 0 0 v = v := by unfold up; simp
theorem down_zz (a : ℕ) : down 0 0 a = a := by unfold down; simp

/-- the renumbering of tokens at N₀ = δ = 0 is the identity -/
theorem virtL_zero {S : OSpec} {sp : Split S} {α : Type} (Q : LStep S sp α) : virtL 0 0 Q = Q := by
  have hu : up 0 0 = id := funext up_zz
  have hd : ∀ (pts : Ctx S), (fun a o => pts (down 0 0 a) o) = pts := fun pts => by
    funext a o; rw [down_zz]
  induction Q with
  | pure a => rfl
  | sample n k ih => simp only [virtL, ih]
  | plain o q k ih => simp only [virtL, ih]
  | fresh ℓ k ih => simp only [virtL, ih, Nat.sub_zero]
  | marked o t us A hA k ih => simp only [virtL, ih, Nat.sub_zero, hu, List.map_id, id]
  | reveal ts pts k ih => simp only [virtL, ih, hu, hd, List.map_id]

end EqSetup

end Compile.DefC
