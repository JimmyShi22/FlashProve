-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkTens.lean: the entries of the program's two kinds of tensors, in the field.

The program's verifier makes its vectors of coefficients from two kinds of tensors
(OnBytes/Iop/Tensor.lean): the equality vector at a point, and the vector of the products of given
factors, which it uses for the rows of a code's generator matrix. This file reads their entries in
the field `GE`.

Main theorems.
 `readE_eq`       an entry of the equality vector at z is the factor in front times the weight `eqW`
                of the index's vertex at z.
 `readE_product`  an entry of a vector of products is the factor in front times the product of the
                factors at the digits 1 of the index.
 `formAt_ofTensor`, `vars_insertChoice`  two small laws on forms and inserted variables.

Not claimed. Nothing on a tensor with a written-out factor.
-/
import OnBytes.Slice.BlkForm
import OnBytes.Slice.BlkRead
import OnBytes.Slice.ProgMle

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## The equality vector -/

/-- The halves that an index picks of the pairs (1 - z t, z t) multiply to the weight of the index's
vertex at the point z. -/
theorem pairsVal_eq : ∀ (z : List E) (j : ℕ),
    pairsVal rdE (z.map fun x => (subE oneE x, x)) j = eqW z.length (readL z) j
  | [], j => (eqW_zero _ j).symm
  | x :: z, j => by
    rw [List.map_cons, pairsVal_cons, pairsVal_eq z (j / 2), List.length_cons, eqW_succ', rdE_val]
    refine congrArg₂ (· * ·) ?_ rfl
    cases j.testBit 0
    · show readE (subE oneE x) = 1 - readE x
      rw [readE_sub, readE_one]
    · rfl

/-- An entry of the equality vector at the point z. -/
theorem readE_eq (z : List E) (s : E) (j : ℕ) :
    readE ((Tensor.eq z s).entry j) = readE s * eqW z.length (readL z) j := by
  rw [← rdE_val, entry_plain rdE _ rfl, rdE_val]
  exact congrArg _ (pairsVal_eq z j)

/-! ## The vector of products -/

/-- The halves that an index picks of the pairs (1, f t) multiply to the product of the f t over the
index's digits 1. -/
theorem pairsVal_product : ∀ (f : List F) (j : ℕ),
    pairsVal rdE (f.map fun x => (oneE, OnBytes.ofF x)) j =
      algebraMap GF GE (toF (productIndex f j))
  | [], _ => by
    show (1 : GE) = algebraMap GF GE (toF 1)
    rw [toF_one, map_one]
  | x :: f, j => by
    rw [List.map_cons, pairsVal_cons, pairsVal_product f (j / 2), toF_productIndex_cons, map_mul,
      rdE_val, Nat.testBit_zero]
    refine congrArg₂ (· * ·) ?_ rfl
    by_cases h : j % 2 = 1
    · rw [decide_eq_true h, if_pos h]
      exact readE_ofF x
    · rw [decide_eq_false h, if_neg h, map_one]
      exact readE_one

/-- An entry of a vector of products. -/
theorem readE_product (f : List F) (scalar : E) (j : ℕ) :
    readE ((Tensor.product f scalar).entry j) =
      readE scalar * algebraMap GF GE (toF (productIndex f j)) := by
  rw [← rdE_val, entry_plain rdE _ rfl, rdE_val]
  exact congrArg _ (pairsVal_product f j)

/-! ## Forms and inserted variables -/

/-- A form that is one tensor. -/
theorem formAt_ofTensor (v : Tensor) (j : ℕ) : formAt (Form.ofTensor v) j = readE (v.entry j) := by
  have e : Form.ofTensor v = ({} : Form).add v := rfl
  unfold formAt
  rw [e, ← rdE_val, Form.entry_add, Form.entry_empty, zero_add, rdE_val]

/-- Inserted variables are counted. -/
theorem vars_insertChoice (v : Tensor) (pos count value : ℕ) (h : pos ≤ v.vars) :
    (v.insertChoice pos count value).vars = v.vars + count := by
  unfold Tensor.vars at h ⊢
  unfold Tensor.insertChoice
  simp only [List.length_append, List.length_take, List.length_drop, choicePairs_length]
  omega

end OnBytes.Slice

#print axioms OnBytes.Slice.pairsVal_eq
#print axioms OnBytes.Slice.readE_eq
#print axioms OnBytes.Slice.pairsVal_product
#print axioms OnBytes.Slice.readE_product
#print axioms OnBytes.Slice.formAt_ofTensor
#print axioms OnBytes.Slice.vars_insertChoice
