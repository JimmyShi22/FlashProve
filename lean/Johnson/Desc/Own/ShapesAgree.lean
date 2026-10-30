-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Own/ShapesAgree.lean: the description's own tests on shapes
(Johnson/Desc/Own/Shapes.lean) say just what the hand-written program's say, at all arguments.
  colsStand_agrees       OnBytes.Blk.columnsFit (OnBytes/Iop/Ground.lean)
  tensorInOrder_agrees   OnBytes.Tensor.ok (OnBytes/Iop/Tensor.lean)
  formFits_agrees        OnBytes.Form.fits (OnBytes/Iop/Tensor.lean)
A YARDSTICK BESIDE: no block imports this file. It says nothing on whether the tests ask enough.
No soundness is claimed.
-/
import Johnson.Desc.Own.Shapes
import OnBytes.Iop.Ground

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Own

theorem colsStand_agrees (key W : Nat) : ∀ (cols : List (Nat × Nat × List UInt64)) (xs : List Nat),
    OnBytes.Blk.columnsFit key W cols xs = colsStand key W cols xs
  | [], _ => by simp [OnBytes.Blk.columnsFit, colsStand]
  | _ :: _, [] => by simp [OnBytes.Blk.columnsFit, colsStand]
  | y :: ys, x :: xs => by
    have ih := colsStand_agrees key W ys xs
    unfold colsStand at ih ⊢
    simp only [OnBytes.Blk.columnsFit, List.zip_cons_cons, List.all_cons, ih]

theorem distinct_agrees : ∀ l : List Nat, OnBytes.distinctNats l = decide l.Nodup
  | [] => by simp [OnBytes.distinctNats]
  | a :: l => by
    simp only [OnBytes.distinctNats, distinct_agrees l, List.nodup_cons]
    by_cases h : a ∈ l <;> simp [h]

theorem tensorInOrder_agrees (v : OnBytes.Tensor) : v.ok = tensorInOrder v := by
  unfold OnBytes.Tensor.ok tensorInOrder
  rw [distinct_agrees]
  rfl

theorem formFits_agrees (f : OnBytes.Form) (vars : Nat) : f.fits vars = formFits f vars := by
  unfold OnBytes.Form.fits formFits
  simp only [tensorInOrder_agrees]
  rfl

end VerifiableInference.Desc.Own

#print axioms VerifiableInference.Desc.Own.colsStand_agrees
#print axioms VerifiableInference.Desc.Own.tensorInOrder_agrees
#print axioms VerifiableInference.Desc.Own.formFits_agrees
