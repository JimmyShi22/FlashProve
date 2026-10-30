-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadForms.lean

The values of the forms and public tables of Policy/Seg/Head.lean.

Statements with their proofs; four are statements of Policy/Seg/HeadSteps.lean.
`headPol_req`: ρ, ρC, NB and the checked tokens are the same at `Cm.reqOf x` and at
`Head.Req.of pol x`. `val_cEx`, `val_cHid`, `val_cHe`: at matrices A the three forms have the values
`Head.ex`, `Ledger.b256` of the bytes `Head.Dv`, and d1 + 2^16 ex, all at the cells `TS.tH A`.
`val_cHidC` to `val_cHidS`: `cHid` at the six ranges of bytes has the values `Head.hidC` to
`Head.hidS`. `rhoP_eq`, `rhoCP_eq` and the lemmas after them: the public tables are ρ and ρC at the
position of the vertex; the masked ones are 0 at a dead vertex.
Live and dead vertices, `va`, `vi`, `vOf`: Cm/SegHead.lean.

Limits: nothing on families, on the segment, on bounds of cells, or on protocols.
-/
import Policy.Seg.HeadSteps
import Cm.TargetSegHeadProofs

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-! ## The request -/

theorem headPol_req : Spec.headPol_req := fun _ _ => ⟨fun _ => rfl, fun _ => rfl, rfl, rfl⟩

/-! ## Forms -/

section Forms
variable (A : ℕ → ℕ → ℕ → Gl.E)

@[simp] theorem val_cEx (v i : ℕ) : (cEx v i).val A = Head.ex (TS.tH A) v i := by
  simp [cEx, Head.ex]

@[simp] theorem val_cHid (a n i : ℕ) :
    (cHid a n i).val A = Ledger.b256 (fun m => Head.Dv (TS.tH A) m i) a n := by
  simp [cHid]

@[simp] theorem val_cHe (v i : ℕ) :
    (cHe v i).val A = Head.d1 (TS.tH A) v i + 2 ^ 16 * Head.ex (TS.tH A) v i := by
  simp [cHe]

/-- This theorem and the next five: `cHid` at six ranges of bytes has the values `Head.hidC` to
`Head.hidS` at the cells `TS.tH A`. -/
theorem val_cHidC (i : ℕ) : (cHid 99 5 i).val A = Head.hidC (TS.tH A) i := val_cHid A 99 5 i
theorem val_cHidB (i : ℕ) : (cHid 104 1 i).val A = Head.hidB (TS.tH A) i := val_cHid A 104 1 i
theorem val_cHidU (i : ℕ) : (cHid 105 5 i).val A = Head.hidU (TS.tH A) i := val_cHid A 105 5 i
theorem val_cHidK (i : ℕ) : (cHid 110 5 i).val A = Head.hidK (TS.tH A) i := val_cHid A 110 5 i
theorem val_cHidZ (i : ℕ) : (cHid 115 2 i).val A = Head.hidZ (TS.tH A) i := val_cHid A 115 2 i
theorem val_cHidS (i : ℕ) : (cHid 117 3 i).val A = Head.hidS (TS.tH A) i := val_cHid A 117 3 i

end Forms

theorem headPol_cEx_val : Spec.headPol_cEx_val := val_cEx
theorem headPol_cHid_val : Spec.headPol_cHid_val := val_cHid
theorem headPol_cHe_val : Spec.headPol_cHe_val := val_cHe

/-! ## Public tables -/

section Tables
variable (pol : AcceptancePolicy) (x : XI)

/-- The table `rhoP` is ρ of `Head.Req.of pol x` at the position of the vertex. -/
theorem rhoP_eq (b : ℕ) : rhoP x b = (((Head.Req.of pol x).rho (vi b) : ℤ) : Gl.E) := rfl
/-- The table `rhoCP` is ρC of `Head.Req.of pol x` at the position of the vertex. -/
theorem rhoCP_eq (b : ℕ) : rhoCP x b = (((Head.Req.of pol x).rhoC (vi b) : ℤ) : Gl.E) := rfl

theorem rhoP_vOf (a : ℕ) {i : ℕ} (hi : i < 2 ^ 10) :
    rhoP x (vOf a i) = (((Head.Req.of pol x).rho i : ℤ) : Gl.E) := by
  rw [rhoP_eq pol, vi_vOf a hi]

theorem rhoCP_vOf (a : ℕ) {i : ℕ} (hi : i < 2 ^ 10) :
    rhoCP x (vOf a i) = (((Head.Req.of pol x).rhoC i : ℤ) : Gl.E) := by
  rw [rhoCP_eq pol, vi_vOf a hi]

theorem vi_pos {i : ℕ} (hi : i < 2 ^ 10) : vi i = i := Nat.mod_eq_of_lt hi

theorem rhoCP_pos {i : ℕ} (hi : i < 2 ^ 10) :
    rhoCP x i = (((Head.Req.of pol x).rhoC i : ℤ) : Gl.E) := by
  rw [rhoCP_eq pol, vi_pos hi]

theorem rhoCT_live {a i : ℕ} (ha : a < 202048) (hi : i < 2 ^ 10) :
    rhoCT x (vOf a i) = (((Head.Req.of pol x).rhoC i : ℤ) : Gl.E) := by
  unfold rhoCT
  rw [va_vOf (lt_trans ha (by norm_num)) hi, if_pos ha, rhoCP_vOf pol x a hi]

theorem rhoCT_dead {b : ℕ} (h : 202048 ≤ va 18 b) : rhoCT x b = 0 := if_neg (not_lt.2 h)

theorem rhoE1_live {a i : ℕ} (ha : a < 70976) (hi : i < 2 ^ 10) :
    rhoE1 x (vOf a i) = (((Head.Req.of pol x).rho i : ℤ) : Gl.E) := by
  unfold rhoE1
  rw [va_vOf (lt_trans ha (by norm_num)) hi, if_pos ha, rhoP_vOf pol x a hi]

theorem rhoE1_dead {b : ℕ} (h : 70976 ≤ va 17 b) : rhoE1 x b = 0 := if_neg (not_lt.2 h)

end Tables

end Policy
