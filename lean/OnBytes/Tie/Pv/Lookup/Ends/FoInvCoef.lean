-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoInvCoef.lean.
The closing steps of a sub-proof's check keep every property of the state that has `Prim`.

HTailF2.coefficientsF writes the virtual rows' weights by a function on the whole state (coefAll,
OnBytes/Tie/Pv/Lookup/Ends/FoCoef.lean), which is a row of writes in single virtual rows:
`inv_coefAll`. So coefficientsF and
coefficients have `Inv I`, and Attention.Seam.finish and Head.selfTests have `InvL I`.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoInvAttention
import OnBytes.Tie.Pv.Lookup.Ends.FoInvHead
import OnBytes.Tie.Pv.Lookup.Ends.FoInvLayer
import OnBytes.Tie.Pv.Lookup.Ends.FoCoef

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.HTailF2 OnBytes.PscRun

variable {I : Fork → Prop} [Prim I]

theorem inv_writes {α : Type} (tr ro : α → ℕ) (f : Fork → α → HRow → HRow) :
    ∀ (l : List α) (F : Fork), I F → I (l.foldl (fun F a => onRow F (tr a) (ro a) (f F a)) F)
  | [], _, h => h
  | _ :: l, _, h => inv_writes tr ro f l _ (Prim.onRow _ _ _ _ h)

theorem inv_tables (tl : HTailF2) (F : Fork) (h : I F) : I (coefTables tl F) := by
  unfold coefTables
  refine forIn_inv I _ (fun n s hs => ?_) _ _ h
  dsimp only
  split
  · split
    · exact ⟨_, rfl, Prim.onRow _ _ _ _ hs⟩
    · exact ⟨_, rfl, hs⟩
  · exact ⟨_, rfl, hs⟩

theorem inv_pieces (tl : HTailF2) (g : Forest.Heard) (F : Fork) (h : I F) :
    I (coefPieces tl g F) := by
  rw [coefPieces_eq]
  exact inv_writes (fun a : ℕ × Piece => a.2.tree) (fun a => a.2.row) (pieceF tl g) _ F h

theorem inv_powers (tl : HTailF2) (theta : E) (F : Fork) (h : I F) : I (coefPowers tl theta F) :=
  Prim.onRow _ _ _ _ (Prim.onRow _ _ _ _ h)

theorem inv_bz (tl : HTailF2) (g : Forest.Heard) (F : Fork) (h : I F) : I (coefBZ tl g F) :=
  Prim.onRow _ _ _ _ (Prim.onRow _ _ _ _ (Prim.onRow _ _ _ _ h))

theorem inv_mats (tl : HTailF2) (theta : E) (F : Fork) (h : I F) : I (coefMats tl theta F) := by
  rw [coefMats_eq]
  exact inv_writes (fun mu => tl.gtTree.getD mu 0) (fun _ => 0) _ _ F h

theorem inv_coefAll (tl : HTailF2) (g : Forest.Heard) (F : Fork) (h : I F) : I (coefAll tl g F) :=
  inv_mats tl _ _ (inv_bz tl g _ (inv_powers tl _ _ (inv_pieces tl g _ (inv_tables tl F h))))

theorem inv_coefficientsF (tl : HTailF2) : Inv I tl.coefficientsF := by
  intro F c a G c' h hS
  obtain ⟨g, -, rfl, -⟩ := coefficientsF_ok tl F G c c' h
  exact inv_coefAll tl g F hS

theorem inv_coefficients (tl : HTailF2) : Inv I tl.coefficients := inv_coefficientsF tl

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible first
  | exact inv_coefficients _ | exact inv_coefficientsF _)

theorem invL_finish (tl : HTailF2) (nU : Array ℕ) : InvL I (Attention.Seam.finish tl nU) := by inv

theorem invL_selfTests (R : Head.Run) (tl : HTailF2) (wo : WsForkOut) :
    InvL I (Head.selfTests R tl wo) := by inv

macro_rules | `(tactic| inv_rule) => `(tactic| with_reducible first
  | exact invL_finish _ _ | exact invL_selfTests _ _ _)

end Fo
