-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngForms.lean: the lookup argument's claims on its multiplicity bits B, as affine forms.

The lookup argument (Blocks/LookupRel.lean, Blocks/LookupBlock.lean) treats B as a function of the
implicit part (only relations mention B) and ends in relations "a value is ~B at a point" and "the
extension of the degree defects vanishes at a point". When B is a vector that the prover has sent,
whose entries forms can read one by one, these relations are linear claims.

 * `LkPar.bOf`: B, read off the entries: B[i, θ, π] is the entry number (i|θ|π) = i 2^(σ+lp) + θ
   2^lp + π.
 * `LkPar.bForm`: the form whose value is ~B(pt) (`val_bForm`).
 * `LkPar.degForm`: the form whose value is the extension of the degree defects at pt
   (`val_degForm`).

The file is generic in the parameters of the lookup argument and in how the entries are stored: ent
x is any form that reads entry number x.

Terms: lean/GLOSSARY.md.
-/
import Blocks.LookupRel

set_option autoImplicit false

namespace Blocks

open Finset

namespace LkPar

variable {E : Type} [Field E] (P : LkPar E) {N : Type} [Fintype N]

/-- the number of the entry (i|θ|π) -/
def bIdx (i θ π : ℕ) : ℕ := i * 2 ^ (P.σ + P.lp) + θ * 2 ^ P.lp + π

omit [Field E] in
theorem bIdx_decode (x : ℕ) : P.bIdx (P.iOf x) (P.thOf x) (P.piOf x) = x := by
  unfold bIdx iOf thOf piOf
  have h1 := Nat.div_add_mod' x (2 ^ P.lp)
  have h2 := Nat.div_add_mod' (x / 2 ^ P.lp) (2 ^ P.σ)
  have h3 : x / 2 ^ P.lp / 2 ^ P.σ = x / 2 ^ (P.σ + P.lp) := by
    rw [Nat.div_div_eq_div_mul, ← pow_add, Nat.add_comm]
  rw [h3] at h2
  have h4 : x / 2 ^ (P.σ + P.lp) * 2 ^ (P.σ + P.lp) =
      x / 2 ^ (P.σ + P.lp) * 2 ^ P.σ * 2 ^ P.lp := by
    rw [pow_add, mul_assoc]
  rw [h4, ← add_mul, h2, h1]

/-- B, read off the entries by the forms ent. -/
def bOf (ent : ℕ → Form N E) (y : N → E) (i θ π : ℕ) : E := Form.val y (ent (P.bIdx i θ π))

/-- The form of ~B(pt). -/
def bForm (ent : ℕ → Form N E) (pt : ℕ → E) : Form N E :=
  extF P.gT (fun x => if P.thOf x < P.NT then ent x else 0) pt

theorem val_bForm (ent : ℕ → Form N E) (y : N → E) (pt : ℕ → E) :
    Form.val y (P.bForm ent pt) = ext P.gT (P.vB (P.bOf ent y)) pt := by
  unfold bForm
  rw [val_extF]
  refine ext_congr (fun x _ => ?_) pt
  unfold vB bOf
  rw [P.bIdx_decode x]
  split_ifs
  · rfl
  · exact map_zero _

/-- The form of the degree check: the extension, at pt, of `LkPar.dDeg` (Blocks/LookupRel.lean):
∑_i mult_θ(i) - (nblk - ϕ_θ), and 0 for an unused θ. Here nblk is 2^D, ϕ_θ is `P.φ θ`, and mult_θ(i)
is ∑_π 2^π B[i, θ, π], with the form `ent (P.bIdx i θ π)` for the bit B[i, θ, π]. -/
def degForm (ent : ℕ → Form N E) (pt : ℕ → E) : Form N E :=
  extF P.σ (fun θ =>
      if θ < P.NT then
        (∑ i ∈ range (2 ^ P.r), ∑ π ∈ range (2 ^ P.lp), (2 : E) ^ π • ent (P.bIdx i θ π)) -
          Form.const ((2 ^ P.D - P.φ θ : ℕ) : E)
      else 0) pt

theorem val_degForm (ent : ℕ → Form N E) (y : N → E) (pt : ℕ → E) :
    Form.val y (P.degForm ent pt) = ext P.σ (P.dDeg (P.bOf ent y)) pt := by
  unfold degForm
  rw [val_extF]
  refine ext_congr (fun θ _ => ?_) pt
  unfold dDeg bOf
  split_ifs
  · rw [map_sub, Form.val_const, map_sum]
    congr 1
    refine sum_congr rfl fun i _ => ?_
    rw [map_sum]
    exact sum_congr rfl fun π _ => by rw [map_smul, smul_eq_mul]
  · exact map_zero _

end LkPar

end Blocks
