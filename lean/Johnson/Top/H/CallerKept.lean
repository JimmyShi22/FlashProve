-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H/CallerKept.lean: who calls "the round before a proximity test, then its first fold"
(`BatFoldCaller`, Johnson/Top/H/BatFold.lean) on a group of sent oracle messages with kept main
rows, and the kind's conditions at that caller.

The group's data are `RowsK` (Johnson/Top/H/GroupRowsKept.lean). The record of the round before
the fold is that of the group without kept rows (`Rows.sizeB`, Johnson/Top/H/CallerOf.lean): it
reads the group alone. Definitions, statements and proofs.
Main names:
  `RowsK.foldCaller`: the caller: the shape `RowsK.Sh`, the stage's distance, lists by the Johnson
    bound, counts bC and bZ.
  `RowsK.foldCaller_ok`: `BatFoldOKAt`, clause by clause: the coefficients evade zero (asked); the
    lists (`RowsK.list`); the joint radius implies each member's own (asked); the shape's laws
    (`RowsK.sh_ok`); the fold's conditions (`RowsK.hypK`).
  `RowsK.foldCaller_own`, `RowsK.foldCaller_ride`: so the block of the kind at the list of this one
    caller has the property that a typed list asks, in both forms of the kind.
Limits: no data are written here, so the conditions are proved of no value. `CountsAt`, `Grp.Fits`
and `Evader.OK` are asked. Which members are marked as kept for later (keep) and which rows have a
kept slot are two letters: nothing ties them here. The limits of the files named hold here.

-/
import Johnson.Top.H.GroupRowsKept
import Johnson.Top.H.CallerOf
import Johnson.Top.H.BatFold

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes.Slice Cb Iop IOR VerifiableInference.OnPublicFiles

namespace RowsK
variable {S : Sig GE} (R : RowsK S) (keep : S.O → Prop) [DecidablePred keep] {B : Type} [Fintype B]
  (Sb : B → Type) (sl : ∀ b, Slf GE (Sb b) R.G.C.J) (Z : Evader GE (R.G.Row B))
  (fx : Fin ((R.Sh.fold Sb sl Z).n + 1) × GE) {Kc St₀ Wp : Type} {E₀ : ExtSpec}
  (A₀ : Rels Kc St₀ E₀ ((S.sub (R.sizeB keep Sb sl Z).kp).Msg × Wp)) (bC bZ : ℕ)
  (w₀ : S.Wit × Wp) (w₁ : LdBrW R.G (R.sizeB keep Sb sl Z).kp Wp)

/-- Who calls the round before the fold with the fold. -/
noncomputable def foldCaller : BatFoldCaller GE where
  s := R.sizeB keep Sb sl Z
  Sh := R.Sh
  fx := fx
  Kc := Kc
  St₀ := St₀
  Wp := Wp
  E₀ := E₀
  A₀ := A₀
  d := R.s.d
  Lst := fun _ => lstJ R.s R.e
  mC := fun _ => bC
  mS := fun _ => bZ
  mW := fun _ => bZ
  w₀ := w₀
  w₁ := w₁

/-- The kind's conditions at the caller. -/
theorem foldCaller_ok (hZ : Z.OK) (hF : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ) :
    BatFoldOKAt (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁) where
  z := hZ
  list := R.list hg hj
  fits := hF
  shape := R.sh_ok hg
  fold := R.hypK Sb sl Z hg hj hc

/-- The block at the list of this one caller, where the fold sends its fresh mask. -/
theorem foldCaller_own (hZ : Z.OK) (hF : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ) :
    ((kBatFoldOwn [R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁]).block
      (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).Good :=
  kBatFoldOwn_good _
    (fun c h => by
      rw [List.mem_singleton.1 h]
      exact R.foldCaller_ok keep Sb sl Z fx A₀ bC bZ w₀ w₁ hZ hF hg hj hc)
    _ (List.mem_singleton.2 rfl)

/-- The same where the fold's mask was sent earlier. -/
theorem foldCaller_ride (hZ : Z.OK) (hF : R.G.Fits) (hg : R.Good) (hj : InJ R.s R.e)
    (hc : CountsAt R.s R.e bC bZ) :
    ((kBatFoldRide [R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁]).block
      (R.foldCaller keep Sb sl Z fx A₀ bC bZ w₀ w₁)).Good :=
  kBatFoldRide_good _
    (fun c h => by
      rw [List.mem_singleton.1 h]
      exact R.foldCaller_ok keep Sb sl Z fx A₀ bC bZ w₀ w₁ hZ hF hg hj hc)
    _ (List.mem_singleton.2 rfl)

end RowsK

end Johnson.Top.H
