-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Inst/Model/Head/NoWrapProgram.lean: the head segment: a ring homomorphism commutes with its arrays,
and NORM reads its input below d only.

  `map_rd` .. `map_sB3`    a ring homomorphism commutes with the arrays and what is formed of them
  `NORM_V_congr` .. `NORM_OK_congr`    NORM reads its input below d only
Notation:
  `y : Req` (Inst/Model/Head/Index.lean): what the head reads of a request and of the policy: `y.r`,
    `y.e`: the two numbers that bound the covered positions; `y.win i`: the token that is checked at
    position i; `y.pol`: the three numbers of the acceptance policy.
(Words of this library: lean/GLOSSARY.md.)
-/
import Inst.Model.Head.NoWrap
import Inst.Model.ProgramR

set_option autoImplicit false

namespace Inst.Model.Head

open Finset

/-! ## Ring homomorphisms -/

section Map
variable {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') (t : Cells K)
  (H : ℕ → ℕ → K) (y : Req)

theorem map_rd (m : ℕ) (c : ℕ → K) : f (rd m c) = rd m fun l => f (c l) := by
  simp [rd, map_sum, map_mul, map_pow, map_ofNat]

theorem map_xv (j i : ℕ) : f (xv t j i) = xv (t.map f) j i := map_rd f _ _
theorem map_nw (j i : ℕ) : f (nw t j i) = nw (t.map f) j i := map_rd f _ _
theorem map_rn (j i : ℕ) : f (rn t j i) = rn (t.map f) j i := by
  unfold rn
  rw [map_add, map_rd, map_ofNat]
  rfl
theorem map_d1 (v i : ℕ) : f (d1 t v i) = d1 (t.map f) v i := map_rd f _ _
theorem map_d2 (v i : ℕ) : f (d2 t v i) = d2 (t.map f) v i := rfl
theorem map_ex (v i : ℕ) : f (ex t v i) = ex (t.map f) v i := by
  unfold ex
  rw [map_add, map_rd, map_ofNat]
  rfl
theorem map_nrm (j i : ℕ) : f (nrm t j i) = nrm (t.map f) j i := map_rd f _ _
theorem map_Dv (n i : ℕ) : f (Dv t n i) = Dv (t.map f) n i := by
  unfold Dv
  rw [map_add, map_ofNat]
  rfl
theorem map_lg (i v : ℕ) : f (lg t H i v) = lg (t.map f) (fun j v => f (H j v)) i v := by
  simp only [lg, map_sum, map_mul, map_nrm]
theorem map_K1 (v i : ℕ) : f (K1 t y v i) = K1 (t.map f) y v i := by
  simp only [K1, map_add, map_mul, map_d1, map_ofNat, map_intCast]
theorem map_K2 (v i : ℕ) : f (K2 t y v i) = K2 (t.map f) y v i := by
  simp only [K2, map_add, map_mul, map_d2, map_ofNat, map_intCast]
theorem map_hidC (i : ℕ) : f (hidC t i) = hidC (t.map f) i := by
  simp only [hidC, Ledger.map_b256, map_Dv]
theorem map_hidB (i : ℕ) : f (hidB t i) = hidB (t.map f) i := by
  simp only [hidB, Ledger.map_b256, map_Dv]
theorem map_hidU (i : ℕ) : f (hidU t i) = hidU (t.map f) i := by
  simp only [hidU, Ledger.map_b256, map_Dv]
theorem map_hidK (i : ℕ) : f (hidK t i) = hidK (t.map f) i := by
  simp only [hidK, Ledger.map_b256, map_Dv]
theorem map_hidZ (i : ℕ) : f (hidZ t i) = hidZ (t.map f) i := by
  simp only [hidZ, Ledger.map_b256, map_Dv]
theorem map_hidS (i : ℕ) : f (hidS t i) = hidS (t.map f) i := by
  simp only [hidS, Ledger.map_b256, map_Dv]
theorem map_mg (v i : ℕ) : f (mg t H y v i) = mg (t.map f) (fun j v => f (H j v)) y v i := by
  simp only [mg, map_add, map_mul, map_sub, map_lg, map_intCast, map_hidC,
    map_hidB, map_pow, map_ofNat]
  split_ifs <;> simp
/-- a ring homomorphism commutes with (B4), (Z), (B2), (B3) -/
theorem map_dB4 (i : ℕ) : f (dB4 t y i) = dB4 (t.map f) y i := by
  simp only [dB4, map_mul, map_sub, map_add, map_intCast, map_natCast, map_hidC, map_hidK]
theorem map_dZ (i : ℕ) : f (dZ t y i) = dZ (t.map f) y i := by
  simp only [dZ, map_mul, map_sub, map_add, map_sum, map_intCast, map_hidS,
    map_ex, map_pow, map_ofNat]
theorem map_sB2 : f (sB2 t y) = sB2 (t.map f) y := by
  simp only [sB2, map_sub, map_sum, map_mul, map_add, map_intCast, map_natCast,
    map_hidC, map_hidB, map_hidU]
theorem map_sB3 : f (sB3 t y) = sB3 (t.map f) y := by
  simp only [sB3, map_sub, map_sum, map_mul, map_add, map_intCast, map_hidB, map_hidZ]
  split_ifs <;> simp

end Map

/-! ## NORM reads its input below d only -/

section Congr
variable (np : NormPar) (d : ℕ) {x x' : Vec} (hx : ∀ j < d, x j = x' j)
include hx

theorem NORM_V_congr : NORM.V d x = NORM.V d x' :=
  sum_congr rfl fun j hj => by rw [hx j (mem_range.1 hj)]
theorem NORM_R_congr : NORM.R np d x = NORM.R np d x' := by
  unfold NORM.R NORM.sig
  rw [NORM_V_congr d hx]
theorem NORM_yw_congr {j : ℕ} (hj : j < d) : NORM.yw np d x j = NORM.yw np d x' j := by
  unfold NORM.yw
  rw [NORM_R_congr np d hx, hx j hj]
theorem NORM_out_congr {j : ℕ} (hj : j < d) : NORM.out np d x j = NORM.out np d x' j := by
  unfold NORM.out
  rw [NORM_yw_congr np d hx hj]
theorem NORM_OK_congr : NORM.OK np d x ↔ NORM.OK np d x' := by
  unfold NORM.OK
  rw [NORM_V_congr d hx]
  exact and_congr Iff.rfl
    (forall_congr' fun j => forall_congr' fun hj => by rw [NORM_yw_congr np d hx hj])

end Congr

end Inst.Model.Head
