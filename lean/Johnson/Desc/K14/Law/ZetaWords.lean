-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K14/Law/ZetaWords.lean: the sentences of the key file's table on plain vectors of
machine elements (Johnson/Desc/Key/KeyMeaning23.lean: sumE, evalEq, readU, FoldAt) read as sums in a
field, under a reading ρ.

  val_sumE · val_evalEq · val_readU   the program's sum, the multilinear extension and "what is read
  off u" read as ∑ and eqK
  val_of_colIs      ColIs (Johnson/Desc/K14/Law/FoldCore.lean) at the readings gives: Omega's entry
  reads as what is read off u
  foldEq_of_val     the table's (Fold), read, is FoldEq (Johnson/Desc/K14/Law/Base.lean) at the
  readings

What is not claimed. Equations between readings, not between the program's words. Nothing on
soundness.

-/
import Johnson.Desc.Key.KeyMeaning23
import Johnson.Desc.K14.Law.Tensors
import Johnson.Desc.K14.Law.FoldCore

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law.ZetaWords
open OnBytes
open OnBytes.Params (LinShape)
open VerifiableInference.Desc.Key (sumE sumE_succ evalEq readU)
open _root_.Desc.K14.Law (eqK FoldEq ColIs entry_eq)

variable {K : Type} [Field K] (ρ : OnBytes.Model.Reading K)

theorem val_sumE (n : Nat) (f : Nat → E) :
    ρ.val (sumE n f) = ∑ i ∈ Finset.range n, ρ.val (f i) := by
  induction n with
  | zero =>
    have e : sumE 0 f = zeroE := rfl
    rw [e, ρ.zero, Finset.range_zero, Finset.sum_empty]
  | succ n ih => rw [sumE_succ, ρ.add, ih, Finset.sum_range_succ]

theorem val_evalEq (pt : List E) (n : Nat) (f : Nat → E) :
    ρ.val (evalEq pt n f) = ∑ c ∈ Finset.range n, eqK (pt.map ρ.val) c * ρ.val (f c) := by
  unfold evalEq
  rw [val_sumE]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ρ.mul, entry_eq ρ, ρ.one, one_mul]

theorem val_readU (S : LinShape) (psi : List E) (u : Nat → E) (y : Nat) :
    ρ.val (readU S psi u y) = ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK ((psi.take S.kLo).map ρ.val) t * ρ.val (u (t + 2 ^ S.kLo * y)) := by
  unfold readU
  exact val_evalEq ρ _ _ _

/-- Where omega is col_psi_lo(u) at the readings, Omega's entry reads as what is read off u. -/
theorem val_of_colIs (S : LinShape) (psi : List E) (u om : Nat → E)
    (h : ColIs S ((psi.take S.kLo).map ρ.val) (fun j => ρ.val (om j)) (fun i => ρ.val (u i))) :
    ∀ y, y < S.matrixRows → ρ.val (om y) = ρ.val (readU S psi u y) := fun y hy => by
  rw [val_readU]
  exact h y hy

/-- The table's (Fold), read, is (fold)'s equation at the readings. -/
theorem foldEq_of_val (S : LinShape) (psi zeta : List E) (u om : Nat → E)
    (h : ρ.val (evalEq zeta S.matrixRows om) =
      ρ.val (sumE S.matrixRows fun y => mulE ((Tensor.eq zeta).entry y) (readU S psi u y))) :
    FoldEq S ((psi.take S.kLo).map ρ.val) (zeta.map ρ.val) (fun j => ρ.val (om j))
      (fun i => ρ.val (u i)) := by
  rw [val_evalEq, val_sumE] at h
  show (∑ j ∈ Finset.range S.matrixRows, eqK (zeta.map ρ.val) j * ρ.val (om j)) =
    ∑ j ∈ Finset.range S.matrixRows, ∑ t ∈ Finset.range (2 ^ S.kLo),
      eqK ((psi.take S.kLo).map ρ.val) t * eqK (zeta.map ρ.val) j * ρ.val (u (t + 2 ^ S.kLo * j))
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [ρ.mul, entry_eq ρ, ρ.one, one_mul, val_readU, Finset.mul_sum]
  refine Finset.sum_congr rfl fun t _ => ?_
  ring

end Desc.K14.Law.ZetaWords
