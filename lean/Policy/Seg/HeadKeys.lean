-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Seg/HeadKeys.lean

The values of the nine families of keys of Policy/Seg/Head.lean, at live and at dead vertices: two
statements of Policy/Seg/HeadSteps.lean, with their proofs.

Five families (NF, NFH, HD1, HD2, CNF) are the plain head's own expressions: for them the two
statements are `TS.head_key_live` and `TS.head_key_dead` (Cm/TargetSegHeadProofs.lean).
`val_mgPolEx`: at the vertex of (a, i), a < 202,048, i < 2^10, the margin's expression has the value
`Head.mg`. `headPol_key_live`: at the vertex of (a, i), a < `Head.len f`, i < `Head.nT`, the
family's value is `segKey`: the relation's key, at HD0 divided by 2^23. `headPol_key_dead`: at a
vertex whose index is not below `Head.len f` the value is the image of an entry of the family's
table: 0 at HD0 and ROW, row 0 of `FE` at HE1; HE0 has no such vertex.
Live and dead vertices, `va`, `vOf`: Cm/SegHead.lean.

Limits: nothing on identities, on the segment as a whole, on bounds of cells, or on protocols.
-/
import Policy.Seg.HeadForms

set_option autoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace Policy
open Cb Inst.Model Finset Cm.Seg Cm.Seg.Ex

/-! ## The keys at live vertices -/

/-- At the vertex of (a, i), a < 202,048, i < 2^10, the margin's expression has the value `Head.mg`:
the plain margin and the ledger's term. -/
theorem val_mgPolEx (pol : AcceptancePolicy) (x : XI) (W : ℕ → ℕ → Gl.F) (A : ℕ → ℕ → ℕ → Gl.E) {a i : ℕ}
    (ha : a < 202048) (hi : i < 2 ^ 10) :
    Ex1.val TS.fmtRef x W A mgPolEx 28 (vOf a i) =
      Head.mg (TS.tH A) (TS.HW W) (Head.Req.of pol x) a i := by
  unfold mgPolEx
  rw [val1_add, TS.val_mgEx x W A ha hi, val1_sc, val1_aff, rhoCT_live pol x ha hi, vi_vOf a hi,
    val_add, val_smul, val_cHidC, val_cHidB]
  rfl

theorem headPol_key_live : Spec.headPol_key_live := by
  intro np pol f x W A a i ha hi
  have hi' : i < 2 ^ 10 := hi
  cases f
  · exact TS.head_key_live np .NF x W A a i ha hi
  · exact TS.head_key_live np .NFH x W A a i ha hi
  · replace ha : a < 202048 := ha
    unfold keyFamPol
    rw [fam_val]
    show Ex1.val TS.fmtRef x W A
        (((2 : Gl.E) ^ 23)⁻¹ • (mgPolEx - ((2 : Gl.E) ^ 8) • TS.k1Ex - TS.k2Ex)) 28 (vOf a i) =
      ((2 : Gl.E) ^ 23)⁻¹ *
        (Head.mg (TS.tH A) (TS.HW W) (Head.Req.of pol x) a i -
          2 ^ 8 * Head.K1 (TS.tH A) (Cm.reqOf x) a i - Head.K2 (TS.tH A) (Cm.reqOf x) a i)
    rw [val1_smul, val1_sub, val1_sub, val1_smul, val_mgPolEx pol x W A ha hi',
      TS.val_k1Ex x W A ha hi', TS.val_k2Ex x W A ha hi']
  · exact TS.head_key_live np .HD1 x W A a i ha hi
  · replace ha : a < 120 := ha
    have h2 : a < 2 ^ 7 := lt_trans ha (by norm_num)
    unfold keyFamPol
    rw [fam_val]
    show Ex1.val TS.fmtRef x W A
        (aff (TS.gd 7 120 fun n i => (((Ledger.mu n : ℤ) : Gl.E)) • TS.cDv n i)) 17 (vOf a i) =
      ((Ledger.mu a : ℤ) : Gl.E) * Head.Dv (TS.tH A) a i
    rw [val1_aff, TS.val_gd A _ h2 ha hi', val_smul, TS.val_cDv]
  · exact TS.head_key_live np .HD2 x W A a i ha hi
  · replace ha : a < 131072 := ha
    have h2 : a < 2 ^ 17 := lt_of_lt_of_eq ha (by norm_num)
    unfold keyFamPol
    rw [fam_val]
    show Ex1.val TS.fmtRef x W A
        (aff (TS.gd 17 131072 cHe) + (32896 : Gl.E) • Ex.pub rhoP) 27 (vOf a i) =
      Head.K1 (TS.tH A) (Head.Req.of pol x) a i + 2 ^ 16 * Head.ex (TS.tH A) a i
    rw [val1_add, val1_aff, val1_smul, val1_pub, TS.val_gd A _ h2 ha hi', val_cHe,
      rhoP_vOf pol x a hi']
    unfold Head.K1
    ring
  · replace ha : a < 70976 := ha
    have h2 : a < 2 ^ 17 := lt_trans ha (by norm_num)
    unfold keyFamPol
    rw [fam_val]
    show Ex1.val TS.fmtRef x W A
        (aff (fun b =>
            if va 17 b < 70976 then cHe (131072 + va 17 b) (vi b)
            else cK (((FE.row 0 : ℤ) : Gl.E))) +
          (32896 : Gl.E) • Ex.pub rhoE1) 27 (vOf a i) =
      Head.K1 (TS.tH A) (Head.Req.of pol x) (131072 + a) i +
        2 ^ 16 * Head.ex (TS.tH A) (131072 + a) i
    rw [val1_add, val1_aff, val1_smul, val1_pub, va_vOf h2 hi', vi_vOf a hi', if_pos ha, val_cHe,
      rhoE1_live pol x ha hi']
    unfold Head.K1
    ring
  · exact TS.head_key_live np .CNF x W A a i ha hi

/-! ## The keys at dead vertices -/

/-- 0 is the image of an entry of the table of HD0 (this theorem) and of ROW (the next). -/
theorem zero_mem_HD0 : ∃ u ∈ (keyTabPol .HD0).set, (0 : Gl.E) = algebraMap Gl.F Gl.E u := by
  refine ⟨0, ⟨0, by positivity, ?_⟩, (map_zero _).symm⟩
  simp [keyTabPol, tabOf, Head.tableOf, R16]

theorem zero_mem_ROW : ∃ u ∈ (keyTabPol .ROW).set, (0 : Gl.E) = algebraMap Gl.F Gl.E u := by
  refine ⟨0, ⟨0, by positivity, ?_⟩, (map_zero _).symm⟩
  simp [keyTabPol, tabOf, Head.tableOf, R8]

theorem headPol_key_dead : Spec.headPol_key_dead := by
  intro np f x W A b hb hd
  cases f
  · exact TS.head_key_dead np .NF x W A b hb hd
  · exact TS.head_key_dead np .NFH x W A b hb hd
  · replace hd : 202048 ≤ va 18 b := hd
    unfold keyFamPol
    rw [fam_val, show Ex1.val TS.fmtRef x W A (keyExPol np .HD0) (vxPol .HD0 + 10) b = 0 by
      unfold keyExPol mgPolEx TS.mgEx TS.k1Ex TS.k2Ex
      simp only [val1_smul, val1_sub, val1_add, val1_sc, val1_aff, val1_pub]
      rw [TS.rhoT_dead x hd, rhoCT_dead x hd, TS.val_gd_dead A _ hd, TS.val_gd_dead A _ hd]
      ring]
    exact zero_mem_HD0
  · exact TS.head_key_dead np .HD1 x W A b hb hd
  · replace hd : 120 ≤ va 7 b := hd
    unfold keyFamPol
    rw [fam_val, show Ex1.val TS.fmtRef x W A (keyExPol np .ROW) (vxPol .ROW + 10) b = 0 by
      unfold keyExPol
      rw [val1_aff, TS.val_gd_dead A _ hd]]
    exact zero_mem_ROW
  · exact TS.head_key_dead np .HD2 x W A b hb hd
  · replace hd : 131072 ≤ va 17 b := hd
    have h : va 17 b < 2 ^ 17 := Nat.mod_lt _ (by positivity)
    omega
  · replace hd : 70976 ≤ va 17 b := hd
    refine ⟨((FE.row 0 : ℤ) : Gl.F), ⟨0, by positivity, rfl⟩, ?_⟩
    unfold keyFamPol
    rw [fam_val]
    unfold keyExPol
    rw [val1_add, val1_aff, val1_smul, val1_pub, if_neg (not_lt.2 hd), val_cK, rhoE1_dead x hd,
      mul_zero, add_zero, map_intCast]
  · exact TS.head_key_dead np .CNF x W A b hb hd

end Policy
