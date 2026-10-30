-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/Port1.lean: towards the tie between the kind's sample row and the library's
sample map of a shape with one answer (Johnson/Pack/PortZ.lean): a sum over a table's indices as a
sum over its real entries, and the numbers of the two sides.

Main names: sum_table; v_bitsZ, bits_main, bits_mask; theta_padW.

What is not claimed. The tie itself is not in this file. Nothing on soundness, on an honest prover
or on hiding.

-/
import Johnson.Desc.K1.Law.PadTie
import Johnson.Pack.SendSize

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model Desc.Plain
open OnBytes.Slice Johnson.Pack

/-- A table's entry at an index: the real entry of the index's row and place, and 0 beyond the real
rows and places. -/
def tabAt {R Lc : Nat} (k : Nat) (msg : Fin R × Fin Lc → GE) (idx : Nat) : GE :=
  if h : idx % 2 ^ k < R ∧ idx / 2 ^ k < Lc then msg (⟨_, h.1⟩, ⟨_, h.2⟩) else 0

theorem tabAt_loc {R Lc : Nat} (k : Nat) (hR : R ≤ 2 ^ k) (msg : Fin R × Fin Lc → GE)
    (x : Fin R × Fin Lc) : tabAt k msg (x.1.val + 2 ^ k * x.2.val) = msg x := by
  have h1 : x.1.val < 2 ^ k := Nat.lt_of_lt_of_le x.1.isLt hR
  have e1 : (x.1.val + 2 ^ k * x.2.val) % 2 ^ k = x.1.val := by
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
  have e2 : (x.1.val + 2 ^ k * x.2.val) / 2 ^ k = x.2.val := by
    rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt h1, Nat.zero_add]
  unfold tabAt
  rw [dif_pos ⟨by rw [e1]; exact x.1.isLt, by rw [e2]; exact x.2.isLt⟩]
  exact congrArg msg (Prod.ext (Fin.ext e1) (Fin.ext e2))

/-- **A sum over a table's indices is the sum over its real entries.** -/
theorem sum_table {R Lc : Nat} (k N : Nat) (hR : R ≤ 2 ^ k) (hN : 2 ^ k * Lc ≤ N) (g : Nat → GE)
    (msg : Fin R × Fin Lc → GE) :
    ∑ idx ∈ Finset.range N, g idx * tabAt k msg idx =
      ∑ x : Fin R × Fin Lc, g (x.1.val + 2 ^ k * x.2.val) * msg x := by
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range N)
    fun idx => idx % 2 ^ k < R ∧ idx / 2 ^ k < Lc]
  have hz : ∑ idx ∈ (Finset.range N).filter (fun idx => ¬ (idx % 2 ^ k < R ∧ idx / 2 ^ k < Lc)),
      g idx * tabAt k msg idx = 0 := by
    refine Finset.sum_eq_zero fun idx h => ?_
    unfold tabAt
    rw [dif_neg (Finset.mem_filter.1 h).2, mul_zero]
  rw [hz, add_zero]
  symm
  refine Finset.sum_nbij (fun x => x.1.val + 2 ^ k * x.2.val) ?_ ?_ ?_ ?_
  · intro x _
    have h1 : x.1.val < 2 ^ k := Nat.lt_of_lt_of_le x.1.isLt hR
    have e1 : (x.1.val + 2 ^ k * x.2.val) % 2 ^ k = x.1.val := by
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h1]
    have e2 : (x.1.val + 2 ^ k * x.2.val) / 2 ^ k = x.2.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos k), Nat.div_eq_of_lt h1, Nat.zero_add]
    simp only [Finset.mem_filter, Finset.mem_range, e1, e2]
    refine ⟨?_, x.1.isLt, x.2.isLt⟩
    have h2 : 2 ^ k * (x.2.val + 1) ≤ 2 ^ k * Lc := Nat.mul_le_mul_left _ x.2.isLt
    rw [Nat.mul_succ] at h2
    omega
  · intro x _ y _ h
    have hx : x.1.val < 2 ^ k := Nat.lt_of_lt_of_le x.1.isLt hR
    have hy : y.1.val < 2 ^ k := Nat.lt_of_lt_of_le y.1.isLt hR
    obtain ⟨a, b⟩ := idx_inj k hx hy h
    exact Prod.ext (Fin.ext a) (Fin.ext b)
  · intro idx h
    simp only [Finset.coe_filter, Finset.mem_range, Set.mem_setOf_eq] at h
    exact ⟨(⟨_, h.2.1⟩, ⟨_, h.2.2⟩), by simp, Nat.mod_add_div idx (2 ^ k)⟩
  · intro x _
    rw [tabAt_loc k hR]

/-! ## The numbers of the two sides -/

theorem bits_main (cs : Codes) (s : OracleShape) (h : 0 < s.mainRows) :
    (Msg.of cs s).bits .main = B1 cs s := by
  have h' : s.mainRows ≠ 0 := Nat.pos_iff_ne_zero.1 h
  simp [Msg.bits, Msg.mainBits, Msg.of, h', B1, k1, pMain, clog, ceilLog2, Code.logEll]

theorem bits_mask (cs : Codes) (s : OracleShape) (h : 0 < s.maskRows) :
    (Msg.of cs s).bits .mask = B2 cs s := by
  have h' : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 h
  simp [Msg.bits, Msg.maskBits, Msg.of, h', B2, k2, pMask, clog, ceilLog2, Code.logEll]

/-- The cube has as many coordinates on both sides. -/
theorem v_bitsZ (cs : Codes) (s : OracleShape) : (Msg.of cs s).v = bitsZ cs s := by
  unfold Msg.v bitsZ
  by_cases h1 : 0 < s.mainRows <;> by_cases h2 : 0 < s.maskRows
  · have a := bits_main cs s h1
    have b := bits_mask cs s h2
    have c1 : s.mainRows ≠ 0 := Nat.pos_iff_ne_zero.1 h1
    have c2 : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 h2
    simp only [Msg.bits] at a b
    rw [a, b]
    simp [Msg.of, c1, c2, h1, h2]
  · have a := bits_main cs s h1
    have c1 : s.mainRows ≠ 0 := Nat.pos_iff_ne_zero.1 h1
    have c2 : s.maskRows = 0 := by omega
    simp only [Msg.bits] at a
    rw [a]
    simp [Msg.of, Msg.maskBits, c2, h1]
  · have b := bits_mask cs s h2
    have c1 : s.mainRows = 0 := by omega
    have c2 : s.maskRows ≠ 0 := Nat.pos_iff_ne_zero.1 h2
    simp only [Msg.bits] at b
    rw [b]
    simp [Msg.of, Msg.mainBits, c1, h2]
  · have c1 : s.mainRows = 0 := by omega
    have c2 : s.maskRows = 0 := by omega
    simp [Msg.of, Msg.mainBits, Msg.maskBits, c1, c2]

/-- The program's basis elements read as the library's 1, x, x². -/
theorem theta_padW (t : Fin 3) : readE (thetaE t.val) = Cb.Gl.padW t := by
  rw [readE_theta]
  fin_cases t <;> rfl

end VerifiableInference.Desc.K1
