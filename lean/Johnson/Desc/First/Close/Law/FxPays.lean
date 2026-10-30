-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/FxPays.lean: THE TWO PREMISES OF K10's LAW ON THE FOLD's FIXED
COEFFICIENT, PAID AT EVERY CALLER OF A GROUP WITH KEPT ROWS. Statements and proofs.

K10's law asks of fx, the coefficient that a round's short message leaves out and its factor: one
step of the library's running claim reads one step of the program's (hst: `StepOK`,
OnBytes/Tie/Pv/Fold/FoldClaim.lean), and the factor times the left-out monomial's sum over {0, 1} is
1 (hfx).
  `caller_step`, `caller_pick`: both hold at fx := (the linear coefficient, 1), at every
    `RowsK.foldCaller`: its rounds have two scalars (n = 2 by the make of `RowsK.Sh`). By
    `stepOK_firstN`, and by evaluation.
Limits. Nothing on soundness.

-/
import Johnson.Top.H.CallerKept
import Johnson.Top.H.BatFoldTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close

open OnBytes OnBytes.Slice OnBytes.Tie.Pv.Fold Iop IOR KObj
open VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.BatFoldAt Cb Cb.Pv Johnson.Top.H

variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep]
  {B : Type} [Fintype B] (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J)
  (Z : Evader GE (R.G.Row B)) {Kc St₀ Wp : Type}
  {E₀ : ExtSpec} (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- hst at the linear coefficient with the factor 1. -/
theorem caller_step :
    StepOK (Yc (R.foldCaller keep Sb sl Z ((1 : Fin 3), (1 : GE)) A₀ bC bZ w₀ w₁)).val
      (Yc (R.foldCaller keep Sb sl Z ((1 : Fin 3), (1 : GE)) A₀ bC bZ w₀ w₁)).n
      ((1 : Fin 3), (1 : GE))
      (rd2 (R.foldCaller keep Sb sl Z ((1 : Fin 3), (1 : GE)) A₀ bC bZ w₀ w₁)) :=
  stepOK_firstN _

/-- hfx there. -/
theorem caller_pick :
    ((1 : Fin 3), (1 : GE)).2 *
      (HVar.plain GE (Yc (R.foldCaller keep Sb sl Z ((1 : Fin 3), (1 : GE)) A₀ bC bZ w₀ w₁)).n).mon
        ((1 : Fin 3), (1 : GE)).1 = 1 := by
  show (1 : GE) * (HVar.plain GE 2).mon (1 : Fin 3) = 1
  rw [one_mul]
  rfl

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.caller_step
#print axioms VerifiableInference.Desc.First.Close.caller_pick
