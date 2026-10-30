-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FastDenseLaw.lean: `denseAtFast = denseAt` (`denseAtFast_eq`): the
expansion of a claim's row that is meant to be faster (FastDense.lean) returns the same words as
`denseAt` (Run.lean), for all arguments, without hypothesis. It imports FastDense.lean alone, so
no Mathlib.

  `denseIndex_add`   the key lemma, for any list of dense variables: where the entry's index is a
                 multiple of 2 ^ (d + 1), setting bit d adds `denseIndex ds i (2 ^ d)` to the index
                 within the slice
  `spreadFast_eq`   `spreadFast` equals `Tensor.spreadTo` where w is 2 to the number of pairs, off
                 is a multiple of w, and idx is `denseIndex` at off
  `addToFast_eq`, `formAddToFast_eq`, `writeOutFast_eq`, `denseFast_eq`   each definition of
                 FastDense.lean equals the one that it repeats, as functions
  `Spec.denseAtFast_eq`, `denseAtFast_eq`   the main equation as a named `Prop`, and its proof

By what. Bit by bit (`bit_add`): for e below d both sides are 0, for e = d they are 1, and for e
above d adding 2 ^ d does not change the quotient. `Tensor.addTo` starts `spreadTo` at off = 0, with
w equal to 2 to the number of pairs, and each step halves w and adds 0 or w / 2 to off.

Limits. Two definitions give the same words. Nothing on cost, or on what a verifier decides.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FastDense

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes (Tensor Form denseIndex)

/-! ## 1 The index within the slice -/

theorem bit_eq (x e : Nat) : x / 2 ^ e % 2 = (x.testBit e).toNat := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ e) with h | h <;> simp [h]

/-- Bit e of 2 ^ (d + 1) * m + 2 ^ d is the sum of the two summands' bits e: no carry. -/
theorem bit_add (d e m : Nat) :
    (2 ^ (d + 1) * m + 2 ^ d) / 2 ^ e % 2 = 2 ^ (d + 1) * m / 2 ^ e % 2 + 2 ^ d / 2 ^ e % 2 := by
  have hlt : 2 ^ d < 2 ^ (d + 1) := Nat.pow_lt_pow_right (by omega) (by omega)
  have h0 : (2 ^ (d + 1) * m).testBit e =
      if e < d + 1 then false else m.testBit (e - (d + 1)) := by
    have h := Nat.testBit_two_pow_mul_add m (Nat.two_pow_pos (d + 1)) e
    simpa using h
  rw [bit_eq, bit_eq, bit_eq, Nat.testBit_two_pow_mul_add m hlt e, h0]
  by_cases h : e < d + 1
  · simp [h]
  · have h2 : (2 ^ d).testBit e = false :=
      Nat.testBit_lt_two_pow (Nat.pow_lt_pow_right (by omega) (by omega))
    simp [h, h2]

theorem denseIndex_zero : ∀ (ds : List Nat) (i : Nat), denseIndex ds i 0 = 0
  | [], _ => rfl
  | d :: ds, i => by
    show 0 / 2 ^ d % 2 * 2 ^ i + denseIndex ds (i + 1) 0 = 0
    rw [denseIndex_zero ds (i + 1), Nat.zero_div, Nat.zero_mod, Nat.zero_mul]

/-- Where the entry's index is a multiple of 2 ^ (d + 1), setting bit d adds
`denseIndex ds i (2 ^ d)` to the index within the slice. ds is any list: a variable may be named
twice, out of order, or lie beyond the tensor's variables. -/
theorem denseIndex_add : ∀ (ds : List Nat) (i d m : Nat),
    denseIndex ds i (2 ^ (d + 1) * m + 2 ^ d) =
      denseIndex ds i (2 ^ (d + 1) * m) + denseIndex ds i (2 ^ d)
  | [], _, _, _ => rfl
  | e :: ds, i, d, m => by
    show (2 ^ (d + 1) * m + 2 ^ d) / 2 ^ e % 2 * 2 ^ i +
        denseIndex ds (i + 1) (2 ^ (d + 1) * m + 2 ^ d) =
      2 ^ (d + 1) * m / 2 ^ e % 2 * 2 ^ i + denseIndex ds (i + 1) (2 ^ (d + 1) * m) +
        (2 ^ d / 2 ^ e % 2 * 2 ^ i + denseIndex ds (i + 1) (2 ^ d))
    rw [bit_add, denseIndex_add ds (i + 1) d m, Nat.add_mul]
    omega

/-! ## 2 One tensor -/

/-- `spreadFast` equals `Tensor.spreadTo` where w is 2 to the number of pairs, off is a multiple of
w, and idx is `denseIndex` at off. -/
theorem spreadFast_eq (v : Tensor) : ∀ (ps : List (OnBytes.E × OnBytes.E)) (m : Nat) (s : OnBytes.E)
    (out : Array OnBytes.E),
    spreadFast v (ps.zip (stepsBelow v.denseVars ps.length)) (2 ^ ps.length) (2 ^ ps.length * m)
        (denseIndex v.denseVars 0 (2 ^ ps.length * m)) s out =
      v.spreadTo ps (2 ^ ps.length) (2 ^ ps.length * m) s out
  | [], _, _, _ => rfl
  | p :: ps, m, s, out => by
    have hw : 2 ^ (ps.length + 1) / 2 = 2 ^ ps.length := by
      rw [Nat.pow_succ, Nat.mul_div_cancel _ (by omega)]
    have e1 : 2 ^ (ps.length + 1) * m = 2 ^ ps.length * (2 * m) := by
      rw [Nat.pow_succ, Nat.mul_assoc]
    have e2 : 2 ^ (ps.length + 1) * m + 2 ^ ps.length = 2 ^ ps.length * (2 * m + 1) := by
      rw [e1, Nat.mul_add, Nat.mul_one]
    show spreadFast v ((p, denseIndex v.denseVars 0 (2 ^ ps.length)) ::
          ps.zip (stepsBelow v.denseVars ps.length)) (2 ^ (ps.length + 1))
          (2 ^ (ps.length + 1) * m) (denseIndex v.denseVars 0 (2 ^ (ps.length + 1) * m)) s out =
        v.spreadTo (p :: ps) (2 ^ (ps.length + 1)) (2 ^ (ps.length + 1) * m) s out
    unfold spreadFast Tensor.spreadTo
    simp only [hw]
    rw [← denseIndex_add, e2, e1]
    simp only [spreadFast_eq v ps]

theorem addToFast_eq : addToFast = Tensor.addTo := by
  funext v out
  unfold addToFast
  split
  · rfl
  · unfold Tensor.addTo
    split
    · rfl
    · have h := spreadFast_eq v v.pairs.reverse 0 v.scalar out
      rw [List.length_reverse, Nat.mul_zero, denseIndex_zero] at h
      exact h

/-! ## 3 A form, and a claim's row -/

theorem formAddToFast_eq : formAddToFast = Form.addTo := by
  funext f out
  unfold formAddToFast Form.addTo
  rw [addToFast_eq]

theorem writeOutFast_eq : writeOutFast = Form.writeOut := by
  funext f vars
  unfold writeOutFast Form.writeOut
  rw [formAddToFast_eq]

theorem denseFast_eq : denseFast = VerifiableInference.Desc.K12.dense := by
  funext f vars
  unfold denseFast VerifiableInference.Desc.K12.dense
  rw [writeOutFast_eq]

def Spec.denseAtFast_eq : Prop := denseAtFast = denseAt

theorem denseAtFast_eq : Spec.denseAtFast_eq := by
  funext row s
  unfold denseAtFast denseAt
  rw [denseFast_eq]

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.bit_eq
#print axioms ProofFile.Honest.K12.Light.bit_add
#print axioms ProofFile.Honest.K12.Light.denseIndex_zero
#print axioms ProofFile.Honest.K12.Light.denseIndex_add
#print axioms ProofFile.Honest.K12.Light.spreadFast_eq
#print axioms ProofFile.Honest.K12.Light.addToFast_eq
#print axioms ProofFile.Honest.K12.Light.formAddToFast_eq
#print axioms ProofFile.Honest.K12.Light.writeOutFast_eq
#print axioms ProofFile.Honest.K12.Light.denseFast_eq
#print axioms ProofFile.Honest.K12.Light.denseAtFast_eq
#print axioms ProofFile.Honest.K12.Light.Spec.denseAtFast_eq
