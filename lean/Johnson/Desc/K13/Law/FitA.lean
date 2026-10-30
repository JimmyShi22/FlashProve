-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K13/Law/FitA.lean: sums over lists of the verifier's elements, read in a field. Lemmas
with their proofs, for Johnson/Desc/K13/Law/FitProofs.lean.
Main names:
  `formVal_append`, `_scale`, `_flatMap`; `weights_append`, `_scale`, `_flatMap`; `foldl_add`.
  `zip_powers_sum`, `zip_self`: a list with the powers c, c x, c x^2 .. beside it.
  `rd_cons`; `eqEvalFrom_val`, `eqEval_val`: the verifier's equality polynomial is `Alg.eqPt`.
  `zip_sumFrom`: a form on the mask entries of a list, as the sum that `walk_hU` speaks of.
  `mle_comb`: the extension of a combination of weight vectors.
Used of `verify-on-bytes`, pure functions and lemmas on them: `Psc.powers`, `Psc.scaleForm`,
`eqEval`, `eqEvalFrom`, `Tensor.entry`, `Tensor.scale`; `Tensor.entry_scale`
(OnBytes/Iop/TensorLaws.lean), `powers_cons` (OnBytes/Tie/Pv/Psc/StepWalk.lean),
`eqEvalFrom_cons_fun` (OnBytes/Slice/ProgMle.lean), `sumFrom` (OnBytes/Model/HideLaws.lean).

What is not claimed. Nothing on a run, on soundness or on hiding.

-/
import Johnson.Desc.K13.Law.Fit
import OnBytes.Iop.TensorLaws
import OnBytes.Slice.ProgMle

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law
open OnBytes OnBytes.Model Cb Iop
open Johnson.L5.Layers (rd sRounds)
open OnBytes.Road.Hd (powers_cons powers_len)

variable {K : Type} [Field K] (ρ : Reading K)

/-- The value of two mask forms, one behind the other. -/
theorem formVal_append (mask : Slot → K) (a b : MaskForm) :
    formVal ρ mask (a ++ b) = formVal ρ mask a + formVal ρ mask b := by
  simp [formVal]

/-- The value of c times a mask form. -/
theorem formVal_scale (mask : Slot → K) (c : E) (m : MaskForm) :
    formVal ρ mask (Psc.scaleForm c m) = ρ.val c * formVal ρ mask m := by
  induction m with
  | nil => simp [formVal, Psc.scaleForm]
  | cons t m ih =>
    have e : Psc.scaleForm c (t :: m) = (t.1, mulE c t.2) :: Psc.scaleForm c m := rfl
    have e1 : ∀ (u : Slot × E) (l : MaskForm),
        formVal ρ mask (u :: l) = ρ.val u.2 * mask u.1 + formVal ρ mask l := fun _ _ => by
      simp [formVal]
    rw [e, e1, e1, ih, ρ.mul]
    ring

/-- The value of mask forms in a row. -/
theorem formVal_flatMap {α : Type} (mask : Slot → K) (F : α → MaskForm) (l : List α) :
    formVal ρ mask (l.flatMap F) = (l.map fun p => formVal ρ mask (F p)).sum := by
  induction l with
  | nil => simp [formVal]
  | cons a l ih => rw [List.flatMap_cons, formVal_append, ih, List.map_cons, List.sum_cons]

/-- The weights of two lists of tensors, one behind the other. -/
theorem weights_append (nR : ℕ) (a b : List Tensor) (i : Fin nR) :
    weights ρ nR (a ++ b) i = weights ρ nR a i + weights ρ nR b i := by
  simp [weights]

/-- The weights of a list of tensors, each times c. -/
theorem weights_scale (nR : ℕ) (g : List Tensor) (c : E) (i : Fin nR) :
    weights ρ nR (g.map fun t => t.scale c) i = ρ.val c * weights ρ nR g i := by
  induction g with
  | nil => simp [weights]
  | cons t g ih =>
    have e1 : ∀ (u : Tensor) (l : List Tensor),
        weights ρ nR (u :: l) i = ρ.val (u.entry i) + weights ρ nR l i := fun _ _ => by
      simp [weights]
    rw [List.map_cons, e1, e1, ih, Tensor.entry_scale]
    ring

/-- The weights of lists of tensors in a row. -/
theorem weights_flatMap {α : Type} (nR : ℕ) (F : α → List Tensor) (l : List α) (i : Fin nR) :
    weights ρ nR (l.flatMap F) i = (l.map fun p => weights ρ nR (F p) i).sum := by
  induction l with
  | nil => simp [weights]
  | cons a l ih => rw [List.flatMap_cons, weights_append, ih, List.map_cons, List.sum_cons]

/-- A loop that adds, read. -/
theorem foldl_add {α : Type} (F : α → E) : ∀ (l : List α) (a : E),
    ρ.val (l.foldl (fun t p => addE t (F p)) a) = ρ.val a + (l.map fun p => ρ.val (F p)).sum
  | [], a => by simp
  | p :: l, a => by
    rw [List.foldl_cons, foldl_add F l, ρ.add, List.map_cons, List.sum_cons, add_assoc]

/-- A sum over a list with the powers c, c x, c x^2 .. beside it, as a sum over the places. -/
theorem zip_powers_sum {α : Type} (x : E) (f : α → K) : ∀ (l : List α) (c : E),
    (((Psc.powers c x l.length).zip l).map fun p => ρ.val p.1 * f p.2).sum =
      ∑ q : Fin l.length, ρ.val c * ρ.val x ^ (q : ℕ) * f (l.get q)
  | [], c => by simp
  | a :: l, c => by
    have e : (Psc.powers c x (a :: l).length).zip (a :: l) =
        (c, a) :: (Psc.powers (mulE c x) x l.length).zip l := by
      rw [List.length_cons, powers_cons, List.zip_cons_cons]
    rw [e, List.map_cons, List.sum_cons, zip_powers_sum x f l (mulE c x)]
    refine Eq.trans ?_ (Fin.sum_univ_succ (n := l.length)
      (fun q : Fin (l.length + 1) => ρ.val c * ρ.val x ^ (q : ℕ) * f ((a :: l).get q))).symm
    show ρ.val c * f a + ∑ q : Fin l.length, ρ.val (mulE c x) * ρ.val x ^ (q : ℕ) * f (l.get q) =
      ρ.val c * ρ.val x ^ ((0 : Fin (l.length + 1)) : ℕ) * f a +
        ∑ q : Fin l.length, ρ.val c * ρ.val x ^ ((q.succ : Fin (l.length + 1)) : ℕ) * f (l.get q)
    rw [ρ.mul, Fin.val_zero, pow_zero, mul_one]
    refine congrArg _ (Finset.sum_congr rfl fun q _ => ?_)
    rw [Fin.val_succ, pow_succ]
    ring

/-- A list beside a list that is made of it and the powers. -/
theorem zip_self {α β γ : Type} (x : E) (G : E × α → β) (H : α × β → γ) : ∀ (l : List α) (c : E),
    (l.zip (((Psc.powers c x l.length).zip l).map G)).map H =
      ((Psc.powers c x l.length).zip l).map fun p => H (p.2, G p)
  | [], _ => by simp
  | a :: l, c => by
    have e : (Psc.powers c x (a :: l).length).zip (a :: l) =
        (c, a) :: (Psc.powers (mulE c x) x l.length).zip l := by
      rw [List.length_cons, powers_cons, List.zip_cons_cons]
    rw [e, List.map_cons, List.zip_cons_cons, List.map_cons, List.map_cons,
      zip_self x G H l (mulE c x)]

/-- The first coordinate of a list that is read as a point. -/
theorem rd_zero (n : ℕ) (a : E) (l : List E) : rd ρ (n + 1) (a :: l) 0 = ρ.val a := by
  simp [rd]

/-- Its later coordinates. -/
theorem rd_succ (n : ℕ) (a : E) (l : List E) (i : Fin n) :
    rd ρ (n + 1) (a :: l) i.succ = rd ρ n l i := by
  simp [rd]

/-- A list with a first member, read as a point. -/
theorem rd_cons (n : ℕ) (a : E) (l : List E) :
    rd ρ (n + 1) (a :: l) = Fin.cons (ρ.val a) (rd ρ n l) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [rd_zero, Fin.cons_zero]
  · rw [rd_succ, Fin.cons_succ]

/-- The verifier's equality polynomial of two points, read. -/
theorem eqEvalFrom_val : ∀ (k : ℕ) (a b : List E) (r : E), a.length = k → b.length = k →
    ρ.val (eqEvalFrom a b r) = ρ.val r * Alg.eqPt (rd ρ k a) (rd ρ k b)
  | 0, [], [], r, _, _ => by
    unfold Alg.eqPt
    rw [Fin.prod_univ_zero, mul_one]
    rfl
  | k + 1, a :: as, b :: bs, r, ha, hb => by
    rw [congrFun (OnBytes.Slice.eqEvalFrom_cons_fun a b as bs) r,
      eqEvalFrom_val k as bs _ (by simpa using ha) (by simpa using hb)]
    unfold Alg.eqPt
    rw [Fin.prod_univ_succ]
    simp only [rd_zero, rd_succ, ρ.mul, ρ.sub, ρ.add, ρ.one, Alg.eq1]
    ring
  | 0, _ :: _, _, _, ha, _ => by simp at ha
  | 0, [], _ :: _, _, _, hb => by simp at hb
  | _ + 1, [], _, _, ha, _ => by simp at ha
  | _ + 1, _ :: _, [], _, _, hb => by simp at hb

/-- The same from the running value 1. -/
theorem eqEval_val (k : ℕ) (a b : List E) (ha : a.length = k) (hb : b.length = k) :
    ρ.val (eqEval a b) = Alg.eqPt (rd ρ k a) (rd ρ k b) := by
  unfold eqEval
  rw [eqEvalFrom_val ρ k a b oneE ha hb, ρ.one, one_mul]

/-- A form on mask entries in a row of a list, as a sum from a place on. -/
theorem zip_sumFrom (mask : Slot → K) : ∀ (fresh : List Slot) (l : List E) (s : ℕ) (μ : ℕ → K),
    l.length ≤ fresh.length → (∀ j, j < fresh.length → μ (s + j) = mask (fresh.getD j default)) →
    formVal ρ mask (fresh.zip l) = sumFrom (fun j y => ρ.val y * μ j) s l
  | _, [], _, _, _, _ => by simp [formVal, sumFrom]
  | [], _ :: _, _, _, h, _ => by simp at h
  | a :: fr, y :: l, s, μ, h, hμ => by
    have e1 : formVal ρ mask ((a :: fr).zip (y :: l)) =
        ρ.val y * mask a + formVal ρ mask (fr.zip l) := by
      simp [formVal]
    have h0 : μ s = mask a := by
      have := hμ 0 (by simp)
      simpa using this
    rw [e1, zip_sumFrom mask fr l (s + 1) μ (by simpa using h) (fun j hj => by
      have := hμ (j + 1) (by simpa using hj)
      have e : s + 1 + j = s + (j + 1) := by omega
      rw [e, this]
      simp)]
    show _ = ρ.val y * μ s + sumFrom (fun j y => ρ.val y * μ j) (s + 1) l
    rw [h0]

/-- The extension of a combination of weight vectors. -/
theorem mle_comb {nR k n : ℕ} (w : Wit K nR k) (c : Fin n → K) (g : Fin n → Fin nR → K)
    (z : Fin k → K) :
    Alg.mle (colOf w fun i => ∑ q, c q * g q i) z = ∑ q, c q * Alg.mle (colOf w (g q)) z := by
  have e : colOf w (fun i => ∑ q, c q * g q i) = fun b => ∑ q, c q * colOf w (g q) b := by
    funext b
    unfold colOf
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => by ring
  rw [e]
  unfold Alg.mle
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun b _ => by ring

end VerifiableInference.Desc.K13.Law
