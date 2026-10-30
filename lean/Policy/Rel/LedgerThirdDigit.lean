-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Policy/Rel/LedgerThirdDigit.lean

Two forms of the third digit of a margin of Policy/Rel/LedgerHead.lean.

* `LedgerHead.inLut_R23_iff`: in a commutative ring in which c is the inverse of 2^23, a lies in
  2^23 · [0, 2^16) if and only if c a lies in [0, 2^16). `inLut_R23_inv`: so modulo every odd prime.

Limits: this file says nothing on the relations.
-/
import Cm.RelProofs
import Cm.Rel2Proofs
import Policy.Rel.LedgerRel

set_option autoImplicit false

/- The next line removes the default table of scales (the instance `Scl.ref`) in this file.
Whatever reads a table here says which table. -/
attribute [-instance] Inst.Model.Scl.ref

namespace Policy.LedgerHead

open Inst.Model Inst.Model.Head

theorem row_R23 {K : Type} [CommRing K] (u : ℕ) :
    ((Cm.Plain.TP.R23.row u : ℤ) : K) = 2 ^ 23 * (u : K) := by
  show ((2 ^ 23 * (u : ℤ) : ℤ) : K) = 2 ^ 23 * (u : K)
  rw [Int.cast_mul, Int.cast_pow, Int.cast_ofNat, Int.cast_natCast]

theorem row_R16 {K : Type} [CommRing K] (u : ℕ) : ((R16.row u : ℤ) : K) = (u : K) :=
  Int.cast_natCast u

/-- In a commutative ring in which c is the inverse of 2^23: a is an entry of 2^23 · [0, 2^16) if
and only if c a is one of [0, 2^16). -/
theorem inLut_R23_iff {K : Type} [CommRing K] {c : K} (hc : c * 2 ^ 23 = 1) (a : K) :
    Head.InLut Cm.Plain.TP.R23 a ↔ Head.InLut R16 (c * a) := by
  constructor
  · rintro ⟨u, hu, e⟩
    refine ⟨u, hu, ?_⟩
    rw [e, row_R23, row_R16, ← mul_assoc, hc, one_mul]
  · rintro ⟨u, hu, e⟩
    refine ⟨u, hu, ?_⟩
    rw [row_R16] at e
    rw [row_R23, ← e, ← mul_assoc, mul_comm (2 ^ 23 : K), hc, one_mul]

/-- Modulo an odd prime p: a is an entry of 2^23 · [0, 2^16) if and only if the inverse of 2^23
times a is one of [0, 2^16). -/
theorem inLut_R23_inv {p : ℕ} [Fact p.Prime] (hp : 2 < p) (a : ZMod p) :
    Head.InLut Cm.Plain.TP.R23 a ↔ Head.InLut R16 ((2 ^ 23 : ZMod p)⁻¹ * a) := by
  have h2 : (2 : ZMod p) ≠ 0 := fun h0 => by
    have h1 : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    have hd := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 p).1 h1)
    omega
  exact inLut_R23_iff (inv_mul_cancel₀ (pow_ne_zero 23 h2)) a

end Policy.LedgerHead
