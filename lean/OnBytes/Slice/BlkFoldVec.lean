-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/BlkFoldVec.lean: the coefficient vectors that the program's fold hands on, in the
field.

The program's block FOLD (OnBytes/Iop/Fold.lean) ends with a claim on three folded rows
(`foldOutput`). Its three vectors of coefficients are made by the program's own functions: the form
on the main rows with its low variables fixed (`Form.fixLow`, OnBytes/Iop/Tensor.lean), the
written-out mask form folded and scaled (`foldMaskForm`), and the public weights of the hiding
polynomial (`foldMaskWeights`). This file reads each in the field and shows that together they are
the vector `midVec`, in which the theorem on a fold (OnBytes/Slice/FoldPeel.lean) states the claim
after a fold. The program's records are read as OnBytes/Slice/BlkRead.lean fixes it, and its
elements by `readE`, `readV` and `readL` (OnBytes/Slice/ProgField.lean).

Main definitions.
 `PlainForm f`   no tensor of the form f has a written-out factor.
 `entSum l j`    the sum of the single entries of the list l at the index j.
 `behindB`, `weightsL`   the program's products of later elements, and its list of weights.
Main theorems.
 `readV_foldLowB`, `readV_foldLowB_of`   the program's fold of an array: entry p is the sum of the
                 entries b + 2^k p under the weights of the point.
 `readV_foldMaskForm`    the form on the carried mask row.
 `foldMaskWeights_eq`, `readV_foldMaskWeights`   the program's weights are the library's, each
                 column at the place that OnBytes/Slice/SimFold.lean names.
 `readE_fixPairs`, `tensorAt_fixLow`, `sum_mergeEntries`, `entry_fix`   the parts of a form.
 `tensors_fixLow`   without a written-out factor, the program's pass over a form's tensors fixes
                 each tensor by itself.
 `formAt_fixLow_range`, `formAt_fixLow`   a form with its k low variables fixed at a point: for
                 entry p, each row gives its entry (row, p) times the row's weight; these are
                 added, and the total is multiplied by the factor.
 `plainForm_empty` to `plainForm_fixLow`, `vars_fixLow`   the calls that build and fix forms keep
                 them without a written-out factor; fixing takes k variables from every tensor.
 `vecS_foldOutput`, `vecS_foldOutput_ok`   the three vectors are `midVec`; the second takes the
                 sizes from the program's own test `foldRowOk`.

Not claimed. Nothing for a form with a written-out factor: `Tensor.foldedSlice` is not treated, and
`PlainForm` is a hypothesis of the statements on forms. That the forms which reach a fold are of
this kind is not shown here. Kept members of a group are not read. Nothing on the run of the block,
on its target or on its point. Nothing on soundness.
-/
import OnBytes.Iop.TensorLaws
import OnBytes.Slice.BlkRead
import OnBytes.Slice.FoldPeel
import OnBytes.Slice.ProgMle

set_option autoImplicit false

namespace OnBytes.Slice
open Cb

/-! ## The program's fold of an array -/

/-- One folded variable halves the length, rounded down. -/
theorem size_foldLowOnce (v : Array E) (g : E) : (foldLowOnce v g).size = v.size / 2 :=
  Array.size_ofFn

/-- One variable folded: entry i is (1 - g) v[2 i] + g v[2 i + 1]; a last entry without a partner is
dropped. -/
theorem readV_foldLowOnce (v : Array E) (g : E) (i : ℕ) :
    readV (foldLowOnce v g) i =
      if i < v.size / 2 then (1 - readE g) * readV v (2 * i) + readE g * readV v (2 * i + 1)
      else 0 := by
  by_cases hi : i < v.size / 2
  · rw [if_pos hi]
    have e : (foldLowOnce v g).getD i zeroE =
        maddE (v.getD (2 * i) zeroE) g
          (subE (v.getD (2 * i + 1) zeroE) (v.getD (2 * i) zeroE)) := by
      unfold foldLowOnce
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hi]
      rfl
    unfold readV
    rw [e, readE_maddE, readE_sub]
    ring
  · rw [if_neg hi]
    exact readV_of_le _ _ (by rw [size_foldLowOnce]; omega)

/-- Folding at no coordinate changes nothing. -/
theorem foldLowB_nil (v : Array E) : foldLow v [] = v := rfl

/-- Folding at a point folds at its first coordinate first. -/
theorem foldLowB_cons (v : Array E) (x : E) (xs : List E) :
    foldLow v (x :: xs) = foldLow (foldLowOnce v x) xs := rfl

/-- Each variable halves the length, rounded down. -/
theorem size_foldLowB (g : List E) : ∀ v : Array E, (foldLow v g).size = v.size / 2 ^ g.length := by
  induction g with
  | nil =>
    intro v
    rw [foldLowB_nil]
    exact (Nat.div_one _).symm
  | cons x xs ih =>
    intro v
    rw [foldLowB_cons, ih, size_foldLowOnce, Nat.div_div_eq_div_mul, List.length_cons, pow_succ']

/-- The program's fold of a table: entry p is the sum of the rows b under the weights of the
point, as far as whole blocks of 2^|g| entries go. -/
theorem readV_foldLowB (g : List E) : ∀ (v : Array E) (p : ℕ),
    readV (foldLow v g) p =
      if p < v.size / 2 ^ g.length then
        ∑ b ∈ Finset.range (2 ^ g.length),
          eqW g.length (readL g) b * readV v (b + 2 ^ g.length * p)
      else 0 := by
  induction g with
  | nil =>
    intro v p
    rw [foldLowB_nil]
    show readV v p = if p < v.size / 2 ^ 0 then
      ∑ b ∈ Finset.range (2 ^ 0), eqW 0 (readL []) b * readV v (b + 2 ^ 0 * p) else 0
    rw [pow_zero, Nat.div_one, Finset.sum_range_one, eqW_zero, one_mul, Nat.zero_add, Nat.one_mul]
    by_cases hp : p < v.size
    · rw [if_pos hp]
    · rw [if_neg hp]
      exact readV_of_le _ _ (by omega)
  | cons x xs ih =>
    intro v p
    have hdiv : v.size / 2 / 2 ^ xs.length = v.size / 2 ^ (xs.length + 1) := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [foldLowB_cons, ih, size_foldLowOnce, hdiv, List.length_cons]
    by_cases hp : p < v.size / 2 ^ (xs.length + 1)
    · rw [if_pos hp, if_pos hp, pow_succ', sum_range_two_mul]
      refine Finset.sum_congr rfl fun b hb => ?_
      have hb' := Finset.mem_range.1 hb
      have hin : b + 2 ^ xs.length * p < v.size / 2 := by
        have h1 : 2 ^ xs.length * (p + 1) ≤ v.size / 2 := by
          rw [← hdiv] at hp
          exact (Nat.le_div_iff_mul_le (Nat.two_pow_pos _)).1 hp |>.trans_eq' (Nat.mul_comm _ _)
        have h2 : 2 ^ xs.length * (p + 1) = 2 ^ xs.length * p + 2 ^ xs.length := by ring
        omega
      have e0 : 2 * b + 2 * 2 ^ xs.length * p = 2 * (b + 2 ^ xs.length * p) := by ring
      have e1 : 2 * b + 1 + 2 * 2 ^ xs.length * p = 2 * (b + 2 ^ xs.length * p) + 1 := by ring
      have t0 : (2 * b).testBit 0 = false := by simp [Nat.testBit_zero]
      have t1 : (2 * b + 1).testBit 0 = true := by simp [Nat.testBit_zero]
      have d0 : 2 * b / 2 = b := by omega
      have d1 : (2 * b + 1) / 2 = b := by omega
      rw [readV_foldLowOnce, if_pos hin, eqW_succ', eqW_succ', t0, t1, d0, d1, e0, e1]
      show eqW xs.length (readL xs) b * ((1 - readE x) * readV v (2 * (b + 2 ^ xs.length * p))
          + readE x * readV v (2 * (b + 2 ^ xs.length * p) + 1))
        = (1 - readE x) * eqW xs.length (readL xs) b * readV v (2 * (b + 2 ^ xs.length * p))
          + readE x * eqW xs.length (readL xs) b * readV v (2 * (b + 2 ^ xs.length * p) + 1)
      ring
    · rw [if_neg hp, if_neg hp]

/-- The same for a table of whole blocks, at every place. -/
theorem readV_foldLowB_of (g : List E) (v : Array E) (l : ℕ) (hv : v.size = l * 2 ^ g.length)
    (p : ℕ) :
    readV (foldLow v g) p =
      ∑ b ∈ Finset.range (2 ^ g.length),
        eqW g.length (readL g) b * readV v (b + 2 ^ g.length * p) := by
  rw [readV_foldLowB, hv, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  by_cases hp : p < l
  · rw [if_pos hp]
  · rw [if_neg hp]
    refine (Finset.sum_eq_zero fun b _ => ?_).symm
    have hle : l * 2 ^ g.length ≤ 2 ^ g.length * p := by
      rw [Nat.mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    rw [readV_of_le v _ (by rw [hv]; omega), mul_zero]

/-! ## The form on the carried mask row -/

/-- Every entry of an array times s. -/
theorem readV_map_mul (A : Array E) (s : E) (p : ℕ) :
    readV (A.map (mulE · s)) p = readV A p * readE s := by
  unfold readV
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases A[p]? with
  | none =>
    show readE zeroE = readE zeroE * readE s
    rw [readE_zero, zero_mul]
  | some a => exact readE_mul a s

/-- The members of a list from the place l on. -/
theorem drop_eq_map (g : List E) (k l : ℕ) (hg : g.length = k) :
    g.drop l = (List.range (k - l)).map fun i => g.getD (l + i) zeroE := by
  apply List.ext_getElem?
  intro i
  rw [List.getElem?_drop, List.getElem?_map]
  by_cases hi : i < k - l
  · rw [List.getElem?_range hi, List.getElem?_eq_getElem (by omega)]
    show _ = some (g.getD (l + i) zeroE)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simpa using hi)]
    rfl

/-- A product over the numbers from s on, below n. -/
theorem prod_from (F : ℕ → GE) (n s : ℕ) :
    ∏ i ∈ Finset.range (n - s), F (s + i) = ∏ t : Fin n, if s ≤ t.val then F t.val else 1 := by
  rw [← Finset.prod_range (fun i => if s ≤ i then F i else 1)]
  by_cases hs : s ≤ n
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hs
    have h1 : (∏ i ∈ Finset.range s, if s ≤ i then F i else 1) = 1 :=
      Finset.prod_eq_one fun i hi => if_neg (by have := Finset.mem_range.1 hi; omega)
    rw [Nat.add_sub_cancel_left, Finset.prod_range_add, h1, one_mul]
    exact Finset.prod_congr rfl fun i _ => (if_pos (Nat.le_add_right s i)).symm
  · rw [show n - s = 0 by omega, Finset.prod_range_zero]
    exact (Finset.prod_eq_one fun i hi =>
      if_neg (by have := Finset.mem_range.1 hi; omega)).symm

/-- The product of eps and the later elements. -/
theorem readE_late (h n : ℕ) (g : List E) (hg : g.length = h + n) (eps : E) :
    readE ((g.drop h).foldl mulE eps) = readE eps * ∏ t : Fin n, readL g (h + t.val) := by
  rw [drop_eq_map g (h + n) h hg, List.foldl_map, Nat.add_sub_cancel_left,
    readE_foldl_range (fun i => g.getD (h + i) zeroE) eps n, Finset.prod_range]
  rfl

/-- The form on the carried mask row, by definition. -/
theorem foldMaskForm_def (h : ℕ) (d : Array E) (eps : E) (g : List E) :
    foldMaskForm h d eps g =
      (foldLow d (g.take h)).map (mulE · ((g.drop h).foldl mulE eps)) := rfl

/-- The form on the carried mask row: the mask form, fixed at the first h coordinates, times
eps and the later coordinates. -/
theorem readV_foldMaskForm (h n : ℕ) (d : Array E) (eps : E) (g : List E)
    (hg : g.length = h + n) (l : ℕ) (hd : d.size = l * 2 ^ h) (p : ℕ) :
    readV (foldMaskForm h d eps g) p =
      (∑ β : Fin h → Bool, readV d (Sz.rowNo β + 2 ^ h * p)
        * Alg.eqk (readP h g) β)
        * (readE eps * ∏ t : Fin n, readL g (h + t.val)) := by
  have hlen : (g.take h).length = h := by
    rw [List.length_take, hg]
    omega
  rw [foldMaskForm_def, readV_map_mul, readE_late h n g hg,
    readV_foldLowB_of (g.take h) d l (by rw [hlen]; exact hd), hlen, sum_range_cube]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [eqW_congr h _ (readL g) _ fun t ht => readL_take h g t ht, eqW_rowNo, mul_comm]
  rfl

/-! ## The weights on the fresh mask row -/

/-- The program's product of the elements number l to k - 1 of an array. -/
def behindB (k : ℕ) (g : Array E) (l : ℕ) : E :=
  (List.range (k - l)).foldl (fun s i => mulE s (g.getD (l + i) zeroE)) oneE

/-- That product, for h + n elements, from the place h + s on. -/
theorem readE_behindB (h n : ℕ) (g : Array E) (s : ℕ) :
    readE (behindB (h + n) g (h + s)) =
      ∏ t : Fin n, if s ≤ t.val then readV g (h + t.val) else 1 := by
  unfold behindB
  rw [readE_foldl_range (fun i => g.getD (h + s + i) zeroE) oneE, readE_one, one_mul,
    show h + n - (h + s) = n - s by omega, ← prod_from (fun i => readV g (h + i)) n s]
  exact Finset.prod_congr rfl fun i _ => by rw [Nat.add_assoc]; rfl

/-- The members of the program's vector of weights, before it is filled to its length. -/
def weightsL (h n : ℕ) (g : Array E) : List E :=
  layL (behindB (h + n) g h)
    (fun i => mulE (g.getD i zeroE) (behindB (h + n) g h))
    (fun i => mulE (g.getD (h + i) zeroE) (behindB (h + n) g (h + 1 + i)))
    (fun i => mulE (mulE (g.getD (h + i) zeroE) (g.getD (h + i) zeroE))
      (behindB (h + n) g (h + 1 + i)))
    oneE h n

/-- The program's vector of weights is that list, filled with 0. -/
theorem foldMaskWeights_eq (h n len : ℕ) (g : Array E) :
    foldMaskWeights (h + n) h len g =
      (weightsL h n g ++ List.replicate (len - (weightsL h n g).length) zeroE).toArray := by
  have h2 : ((List.range n).flatMap fun i =>
        (if i == 0 then [] else
          [mulE (g.getD (h + i) zeroE) (behindB (h + n) g (h + 1 + i))]) ++
        [mulE (mulE (g.getD (h + i) zeroE) (g.getD (h + i) zeroE))
          (behindB (h + n) g (h + 1 + i))]) =
      midL (fun i => mulE (g.getD (h + i) zeroE) (behindB (h + n) g (h + 1 + i)))
        (fun i => mulE (mulE (g.getD (h + i) zeroE) (g.getD (h + i) zeroE))
          (behindB (h + n) g (h + 1 + i))) n :=
    List.flatMap_congr fun i _ => by
      by_cases h0 : i = 0
      · rw [if_pos h0, if_pos (by rw [h0]; rfl), List.nil_append]
      · rw [if_neg h0, if_neg (by simpa using h0), List.singleton_append]
  have h3 : (if h < h + n then [oneE] else ([] : List E)) = if 0 < n then [oneE] else [] := by
    simp only [Nat.lt_add_right_iff_pos]
  have hu : (behindB (h + n) g h ::
        (List.range h).map fun i => mulE (g.getD i zeroE) (behindB (h + n) g h)) ++
      ((List.range (h + n - h)).flatMap fun i =>
        (if i == 0 then [] else
          [mulE (g.getD (h + i) zeroE) (behindB (h + n) g (h + 1 + i))]) ++
        [mulE (mulE (g.getD (h + i) zeroE) (g.getD (h + i) zeroE))
          (behindB (h + n) g (h + 1 + i))]) ++
      (if h < h + n then [oneE] else []) = weightsL h n g := by
    rw [Nat.add_sub_cancel_left, h2, h3, List.append_assoc]
    rfl
  have key : ∀ U W : List E, U = W →
      (U ++ List.replicate (len - U.length) zeroE).toArray =
        (W ++ List.replicate (len - W.length) zeroE).toArray := fun _ _ e => by rw [e]
  exact key _ _ hu

/-- Each column's weight is at the column's place. -/
theorem readE_weightsL_at (h n : ℕ) (g : Array E) (c : PCol h n 1) :
    readE ((weightsL h n g).getD (hidePlace h n c) zeroE) =
      QwC h n 1 (fun t : Fin (h + n) => readV g t.val) c := by
  have hlate : readE (behindB (h + n) g h) = ∏ t : Fin n, readV g (h + t.val) := by
    have e := readE_behindB h n g 0
    rw [Nat.add_zero] at e
    rw [e]
    exact Finset.prod_congr rfl fun t _ => if_pos (Nat.zero_le _)
  rcases c with ⟨i, q⟩ | ⟨t, p⟩ | u
  · have hq : q.val = 0 := by have := q.isLt; omega
    show readE ((weightsL h n g).getD (1 + i.val) zeroE) =
      readV g i.val ^ (q.val + 1) * ∏ t : Fin n, readV g (h + t.val)
    unfold weightsL
    rw [layL_hd _ _ _ _ _ _ _ _ _ i.isLt, readE_mul, hlate, hq, Nat.zero_add, pow_one]
    rfl
  · have htail : readE (behindB (h + n) g (h + 1 + t.val)) =
        ∏ t' : Fin n, if t < t' then readV g (h + t'.val) else 1 := by
      have e := readE_behindB h n g (t.val + 1)
      rw [show h + (t.val + 1) = h + 1 + t.val by omega] at e
      exact e
    show readE ((weightsL h n g).getD
        (if t.val = 0 ∧ p.val = 0 then 0 else h + 2 * t.val + p.val) zeroE) =
      readV g (h + t.val) ^ (p.val + 1) * ∏ t' : Fin n, if t < t' then readV g (h + t'.val) else 1
    unfold weightsL
    by_cases h0 : t.val = 0 ∧ p.val = 0
    · rw [if_pos h0, layL_zero, hlate, h0.2, Nat.zero_add, pow_one,
        ← mon_split (fun t' : Fin n => readV g (h + t'.val)) t]
      exact Finset.prod_congr rfl fun t' _ =>
        (if_pos (show t ≤ t' from Fin.le_def.2 (by rw [h0.1]; exact Nat.zero_le _))).symm
    · rw [if_neg h0]
      by_cases hp : p.val = 0
      · rw [hp, Nat.add_zero (h + 2 * t.val), layL_lin _ _ _ _ _ _ _ _ _ (by omega) t.isLt,
          readE_mul, htail, Nat.zero_add, pow_one]
        rfl
      · have hp1 : p.val = 1 := by have := p.isLt; omega
        rw [hp1, layL_sq _ _ _ _ _ _ _ _ _ t.isLt, readE_mul, readE_mul, htail, pow_two]
        rfl
  · show readE ((weightsL h n g).getD (if n = 0 then 0 else h + 2 * n) zeroE) = 1
    unfold weightsL
    by_cases hn : n = 0
    · subst hn
      rw [if_pos rfl, layL_zero, hlate]
      rfl
    · rw [if_neg hn, layL_one _ _ _ _ _ _ _ _ (by omega)]
      exact readE_one

/-- The list of weights, read at any place. -/
theorem readL_weightsL (h n : ℕ) (g : Array E) (j : ℕ) :
    readL (weightsL h n g) j =
      ∑ c : PCol h n 1, if hidePlace h n c = j
        then QwC h n 1 (fun t : Fin (h + n) => readV g t.val) c else 0 := by
  unfold readL
  by_cases hex : ∃ c, hidePlace h n c = j
  · obtain ⟨c, hc⟩ := hex
    rw [← hc, readE_weightsL_at h n g c,
      Finset.sum_eq_single c (fun c' _ hne => if_neg fun e => hne (hidePlace_inj h n e))
        (fun hm => absurd (Finset.mem_univ c) hm), if_pos rfl]
  · have hfar : h + 2 * n + 1 ≤ j := by
      by_contra hlt
      exact hex (hidePlace_surj h n j (by omega))
    unfold weightsL
    rw [layL_far _ _ _ _ _ _ _ _ _ hfar, readE_zero]
    exact (Finset.sum_eq_zero fun c _ => if_neg fun e => hex ⟨c, e⟩).symm

/-- The weights on the fresh mask row are the library's, each column at its place. -/
theorem readV_foldMaskWeights (h n len : ℕ) (g : Array E) (j : ℕ) :
    readV (foldMaskWeights (h + n) h len g) j =
      ∑ c : PCol h n 1, if hidePlace h n c = j
        then QwC h n 1 (fun t : Fin (h + n) => readV g t.val) c else 0 := by
  rw [foldMaskWeights_eq h n len g, readV_toArray, readL_append, ← readL_weightsL h n g j]
  by_cases hj : j < (weightsL h n g).length
  · rw [if_pos hj]
  · rw [if_neg hj, readL_of_le (weightsL h n g) j (by omega)]
    exact readL_replicate_zero _ _

/-! ## Forms without a written-out factor -/

/-- No tensor of the form has a written-out factor. -/
def PlainForm (f : Form) : Prop := ∀ v ∈ f.tensors, v.denseVars = []

/-- No coordinate: the pairs are kept. An equation between functions of the scalar. -/
theorem fixPairs_nil_fun (ps : List (E × E)) : fixPairs ps [] = fun s => (s, ps) := by
  cases ps <;> rfl

/-- No coordinate: scalar and pairs are kept. -/
theorem fixPairs_nil (ps : List (E × E)) (s : E) : fixPairs ps [] s = (s, ps) :=
  congrFun (fixPairs_nil_fun ps) s

/-- No pair: the scalar is kept. An equation between functions of the scalar. -/
theorem fixPairs_none_fun (g : List E) : fixPairs [] g = fun s => (s, []) := by
  cases g <;> rfl

/-- One coordinate takes the first pair into the scalar. -/
theorem fixPairs_cons_fun (q : E × E) (qs : List (E × E)) (x : E) (xs : List E) :
    fixPairs (q :: qs) (x :: xs) =
      fun s => fixPairs qs xs (mulE s (addE q.1 (mulE x (subE q.2 q.1)))) := rfl

/-- The pairs that are left are as many as there were, less the coordinates of the point. -/
theorem length_fixPairs : ∀ (g : List E) (ps : List (E × E)) (s : E),
    (fixPairs ps g s).2.length = ps.length - g.length
  | [], ps, s => by rw [fixPairs_nil]; rfl
  | x :: xs, [], s => by
    rw [congrFun (fixPairs_none_fun (x :: xs)) s]
    exact (Nat.zero_sub _).symm
  | x :: xs, q :: qs, s => by
    rw [congrFun (fixPairs_cons_fun q qs x xs) s, length_fixPairs xs qs]
    simp

/-- Fixing the low variables of a product of pairs: the new scalar times the halves that are
left is the old scalar times the sum, under the weights of the point, over the low bits. -/
theorem readE_fixPairs : ∀ (g : List E) (ps : List (E × E)) (s : E) (p : ℕ),
    g.length ≤ ps.length →
    readE (fixPairs ps g s).1 * pairsVal rdE (fixPairs ps g s).2 p =
      readE s * ∑ b ∈ Finset.range (2 ^ g.length),
        eqW g.length (readL g) b * pairsVal rdE ps (b + 2 ^ g.length * p)
  | [], ps, s, p, _ => by
    rw [fixPairs_nil]
    show readE s * pairsVal rdE ps p = readE s * ∑ b ∈ Finset.range (2 ^ 0),
      eqW 0 (readL []) b * pairsVal rdE ps (b + 2 ^ 0 * p)
    rw [pow_zero, Finset.sum_range_one, eqW_zero, one_mul, Nat.zero_add, Nat.one_mul]
  | _ :: _, [], _, _, h => absurd h (by simp)
  | x :: xs, q :: qs, s, p, h => by
    have hl : xs.length ≤ qs.length := by simpa using h
    rw [congrFun (fixPairs_cons_fun q qs x xs) s, readE_fixPairs xs qs _ p hl, readE_mul, readE_add,
      readE_mul, readE_sub, List.length_cons, pow_succ', sum_range_two_mul, mul_assoc,
      Finset.mul_sum]
    refine congrArg (readE s * ·) (Finset.sum_congr rfl fun b _ => ?_)
    have e0 : 2 * b + 2 * 2 ^ xs.length * p = 2 * (b + 2 ^ xs.length * p) := by ring
    have e1 : 2 * b + 1 + 2 * 2 ^ xs.length * p = 2 * (b + 2 ^ xs.length * p) + 1 := by ring
    have t0 : (2 * b).testBit 0 = false := by simp [Nat.testBit_zero]
    have t1 : (2 * b + 1).testBit 0 = true := by simp [Nat.testBit_zero]
    have d0 : 2 * b / 2 = b := by omega
    have d1 : (2 * b + 1) / 2 = b := by omega
    have p0 : ∀ m, pairsVal rdE (q :: qs) (2 * m) = readE q.1 * pairsVal rdE qs m := fun m => by
      have hm : 2 * m / 2 = m := by omega
      have hz : (2 * m % 2 == 1) = false := by simp
      show rdE.val (if 2 * m % 2 == 1 then q.2 else q.1) * pairsVal rdE qs (2 * m / 2) = _
      rw [hm, hz, rdE_val]
      rfl
    have p1 : ∀ m, pairsVal rdE (q :: qs) (2 * m + 1) = readE q.2 * pairsVal rdE qs m := fun m => by
      have hm : (2 * m + 1) / 2 = m := by omega
      have hz : ((2 * m + 1) % 2 == 1) = true := by simp [Nat.add_mod]
      show rdE.val (if (2 * m + 1) % 2 == 1 then q.2 else q.1)
        * pairsVal rdE qs ((2 * m + 1) / 2) = _
      rw [hm, hz, rdE_val]
      rfl
    rw [eqW_succ', eqW_succ', t0, t1, d0, d1, e0, e1, p0, p1]
    show (readE q.1 + readE x * (readE q.2 - readE q.1)) * (eqW xs.length (readL xs) b
        * pairsVal rdE qs (b + 2 ^ xs.length * p))
      = (1 - readE x) * eqW xs.length (readL xs) b
          * (readE q.1 * pairsVal rdE qs (b + 2 ^ xs.length * p))
        + readE x * eqW xs.length (readL xs) b
          * (readE q.2 * pairsVal rdE qs (b + 2 ^ xs.length * p))
    ring

/-- An entry of a tensor without a written-out factor. -/
theorem readE_entry_plain (w : Tensor) (hw : w.denseVars = []) (j : ℕ) :
    readE (w.entry j) = readE w.scalar * pairsVal rdE w.pairs j := by
  have h := Tensor.entry_val rdE w j
  have h1 : w.denseVal rdE j = 1 := by
    unfold Tensor.denseVal
    rw [hw]
    rfl
  rw [h1, mul_one, rdE_val, rdE_val] at h
  exact h

/-- What fixing does to a tensor without a written-out factor. -/
theorem fixLow_plain (v : Tensor) (hd : v.denseVars = []) (g : List E) :
    v.fixLow g = { v with
      scalar := (fixPairs v.pairs g v.scalar).1
      pairs := (fixPairs v.pairs g v.scalar).2
      denseVars := [] } := by
  have hc : v.sliceIsCut g.length = false := by
    unfold Tensor.sliceIsCut
    rw [hd]
    rfl
  unfold Tensor.fixLow
  simp only [hc, Bool.false_eq_true, if_false, hd, List.map_nil]

/-- Scaling a tensor keeps its written-out variables. -/
theorem scale_denseVars (v : Tensor) (x : E) : (v.scale x).denseVars = v.denseVars := by
  unfold Tensor.scale
  rfl

/-- Scaling a tensor keeps its number of variables. -/
theorem scale_vars (v : Tensor) (x : E) : (v.scale x).vars = v.vars := by
  unfold Tensor.scale Tensor.vars
  rfl

/-- A tensor without a written-out factor, with its k low variables fixed: entry p is the sum of the
entries b + 2^k p under the weights of the point. -/
theorem tensorAt_fixLow (v : Tensor) (hd : v.denseVars = []) (g : List E)
    (hg : g.length ≤ v.vars) (p : ℕ) :
    readE ((v.fixLow g).entry p) = ∑ b ∈ Finset.range (2 ^ g.length),
      eqW g.length (readL g) b * readE (v.entry (b + 2 ^ g.length * p)) := by
  rw [fixLow_plain v hd g, readE_entry_plain _ rfl]
  show readE (fixPairs v.pairs g v.scalar).1 * pairsVal rdE (fixPairs v.pairs g v.scalar).2 p = _
  rw [readE_fixPairs g v.pairs v.scalar p hg, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [readE_entry_plain v hd]
  ring

/-- One step of the program's pass over the tensors of a form, at a tensor without a written-out
factor: the tensor is fixed by itself, and the table of folded slices is unchanged. -/
theorem fixLowShared_plain (g : List E) (s : List Tensor × Form.FoldedSlices) (v : Tensor)
    (hd : v.denseVars = []) : Form.fixLowShared g s v = (v.fixLow g :: s.1, s.2) := by
  have hc : v.sliceIsCut g.length = false := by
    unfold Tensor.sliceIsCut
    rw [hd]
    rfl
  unfold Form.fixLowShared
  simp only [hc, Bool.false_eq_true, if_false]

/-- The whole pass, for tensors without a written-out factor. -/
theorem foldl_fixLowShared (g : List E) (times : E) : ∀ (l : List Tensor)
    (s : List Tensor × Form.FoldedSlices), (∀ v ∈ l, v.denseVars = []) →
    (l.foldl (fun s v => Form.fixLowShared g s (v.scale times)) s).1 =
      (l.map fun v => (v.scale times).fixLow g).reverse ++ s.1
  | [], s, _ => rfl
  | v :: l, s, h => by
    rw [List.foldl_cons, fixLowShared_plain g s (v.scale times)
        ((scale_denseVars v times).trans (h v List.mem_cons_self)),
      foldl_fixLowShared g times l _ fun w hw => h w (List.mem_cons_of_mem _ hw),
      List.map_cons, List.reverse_cons, List.append_assoc]
    rfl

/-- The tensors of a form with its low variables fixed: each is fixed by itself, if none has a
written-out factor. -/
theorem tensors_fixLow (f : Form) (hp : ∀ v ∈ f.tensors, v.denseVars = []) (g : List E)
    (times : E) :
    (f.fixLow g times).tensors = f.tensors.map fun v => (v.scale times).fixLow g := by
  show (f.tensors.foldl (fun s v => Form.fixLowShared g s (v.scale times)) ([], {})).1.reverse = _
  rw [foldl_fixLowShared g times f.tensors _ hp, List.append_nil, List.reverse_reverse]

/-- The single entries of a form with its low variables fixed, by definition. -/
theorem entries_fixLow (f : Form) (g : List E) (times : E) :
    (f.fixLow g times).entries = mergeEntries (f.entries.map fun e =>
      (e.1 / 2 ^ g.length, mulE (eqWeight g e.1 e.2) times)) := rfl

/-- The sum of the single entries at an index. -/
def entSum (l : List (ℕ × E)) (j : ℕ) : GE := (l.map fun e => if e.1 = j then readE e.2 else 0).sum

/-- The sum of the single entries, one entry at a time. -/
theorem entSum_cons (a : ℕ × E) (l : List (ℕ × E)) (j : ℕ) :
    entSum (a :: l) j = (if a.1 = j then readE a.2 else 0) + entSum l j := rfl

/-- One pass that joins neighbours with one index keeps the sum at every index. -/
theorem entSum_join (j : ℕ) : ∀ (l acc : List (ℕ × E)),
    entSum (l.foldl (fun acc a =>
      match acc with
      | b :: r => if a.1 == b.1 then (b.1, addE b.2 a.2) :: r else a :: acc
      | [] => [a]) acc) j = entSum acc j + entSum l j
  | [], acc => by simp [entSum]
  | a :: l, [] => by
    rw [List.foldl_cons, entSum_join j l, entSum_cons a l]
    simp [entSum]
  | a :: l, b :: r => by
    rw [List.foldl_cons, entSum_join j l, entSum_cons a l]
    by_cases hab : a.1 = b.1
    · have hb : (a.1 == b.1) = true := by simp [hab]
      simp only [hb, if_true]
      rw [entSum_cons, entSum_cons]
      by_cases hj : b.1 = j
      · simp only [hj, hab, if_true, readE_add]
        ring
      · simp only [hj, hab, if_false]
        ring
    · have hb : (a.1 == b.1) = false := by simp [hab]
      simp only [hb, Bool.false_eq_true, if_false]
      rw [entSum_cons]
      ring

/-- Merging keeps the sum of the single entries at every index. -/
theorem sum_mergeEntries (l : List (ℕ × E)) (j : ℕ) : entSum (mergeEntries l) j = entSum l j := by
  unfold mergeEntries
  have hrev : ∀ m : List (ℕ × E), entSum m.reverse j = entSum m j := fun m => by
    unfold entSum
    rw [List.map_reverse, List.sum_reverse]
  rw [hrev]
  refine (entSum_join j _ []).trans ?_
  have hperm : entSum (l.mergeSort fun a b => a.1 ≤ b.1) j = entSum l j :=
    ((List.mergeSort_perm l _).map _).sum_eq
  rw [hperm]
  simp [entSum]

/-- A single entry that moves to the index of its higher bits. -/
theorem entry_fix (g : List E) (e : ℕ × E) (times : E) (p : ℕ) :
    (if e.1 / 2 ^ g.length = p then readE (mulE (eqWeight g e.1 e.2) times) else 0) =
      (∑ b ∈ Finset.range (2 ^ g.length), eqW g.length (readL g) b
        * (if e.1 = b + 2 ^ g.length * p then readE e.2 else 0)) * readE times := by
  have hpos : 0 < 2 ^ g.length := Nat.two_pow_pos _
  by_cases h : e.1 / 2 ^ g.length = p
  · have hsplit : e.1 = e.1 % 2 ^ g.length + 2 ^ g.length * p := by
      rw [← h]
      exact (Nat.mod_add_div _ _).symm
    rw [if_pos h, Finset.sum_eq_single (e.1 % 2 ^ g.length)]
    · rw [if_pos hsplit, eqW_mod, readE_mul, readE_eqWeight]
      ring
    · intro b hb hne
      rw [if_neg, mul_zero]
      intro hc
      apply hne
      rw [hc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (Finset.mem_range.1 hb)]
    · intro hn
      exact absurd (Finset.mem_range.2 (Nat.mod_lt _ hpos)) hn
  · rw [if_neg h, Finset.sum_eq_zero, zero_mul]
    intro b hb
    rw [if_neg, mul_zero]
    intro hc
    apply h
    rw [hc, Nat.add_mul_div_left _ _ hpos, Nat.div_eq_of_lt (Finset.mem_range.1 hb), Nat.zero_add]

/-- The weights may be taken inside: a weighted sum of list sums is a list sum of weighted sums. -/
theorem sum_mul_list {α : Type} (s : Finset ℕ) (W : ℕ → GE) (h : α → ℕ → GE) : ∀ L : List α,
    ∑ b ∈ s, W b * (L.map fun a => h a b).sum = (L.map fun a => ∑ b ∈ s, W b * h a b).sum
  | [] => by simp
  | a :: L => by
    simp only [List.map_cons, List.sum_cons, mul_add, Finset.sum_add_distrib, sum_mul_list s W h L]

/-- A form with its low variables fixed, as a sum over the numbers below 2^k. -/
theorem formAt_fixLow_range (f : Form) (hp : PlainForm f) (g : List E)
    (hv : ∀ v ∈ f.tensors, g.length ≤ v.vars) (times : E) (p : ℕ) :
    formAt (f.fixLow g times) p =
      (∑ b ∈ Finset.range (2 ^ g.length),
        eqW g.length (readL g) b * formAt f (b + 2 ^ g.length * p)) * readE times := by
  have hL : formAt (f.fixLow g times) p =
      ((f.fixLow g times).tensors.map fun v => readE (v.entry p)).sum
        + entSum (f.fixLow g times).entries p := Form.entry_val rdE _ p
  have hR : ∀ j, formAt f j = (f.tensors.map fun v => readE (v.entry j)).sum + entSum f.entries j :=
    fun j => Form.entry_val rdE f j
  have hT : ((f.fixLow g times).tensors.map fun v => readE (v.entry p)).sum =
      (f.tensors.map fun v => ∑ b ∈ Finset.range (2 ^ g.length),
        eqW g.length (readL g) b * readE (v.entry (b + 2 ^ g.length * p))).sum * readE times := by
    rw [tensors_fixLow f hp g times, List.map_map, ← List.sum_map_mul_right]
    refine congrArg List.sum (List.map_congr_left fun v hvm => ?_)
    show readE (((v.scale times).fixLow g).entry p) = _
    rw [tensorAt_fixLow (v.scale times) ((scale_denseVars v times).trans (hp v hvm)) g
      ((hv v hvm).trans_eq (scale_vars v times).symm) p, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    have hs := Tensor.entry_scale rdE v times (b + 2 ^ g.length * p)
    rw [rdE_val, rdE_val, rdE_val] at hs
    rw [hs, mul_assoc]
  have hE : entSum (f.fixLow g times).entries p =
      (f.entries.map fun e => ∑ b ∈ Finset.range (2 ^ g.length), eqW g.length (readL g) b
        * (if e.1 = b + 2 ^ g.length * p then readE e.2 else 0)).sum * readE times := by
    rw [entries_fixLow, sum_mergeEntries, ← List.sum_map_mul_right]
    unfold entSum
    rw [List.map_map]
    exact congrArg List.sum (List.map_congr_left fun e _ => entry_fix g e times p)
  rw [hL, hT, hE, ← add_mul]
  congr 1
  rw [← sum_mul_list, ← sum_mul_list, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [hR, mul_add]
  rfl

/-- A form with its low variables fixed, in the terms of the library's fold: for entry p, each row β
gives the entry (β, p) times the weight of β at the point; these are added, and the total is
multiplied by the factor. -/
theorem formAt_fixLow (f : Form) (hp : PlainForm f) (k : ℕ) (g : List E) (hg : g.length = k)
    (hv : ∀ v ∈ f.tensors, k ≤ v.vars) (times : E) (p : ℕ) :
    formAt (f.fixLow g times) p =
      (∑ β : Fin k → Bool, formAt f (Sz.rowNo β + 2 ^ k * p)
        * Alg.eqk (readP k g) β) * readE times := by
  subst hg
  rw [formAt_fixLow_range f hp g hv times p, sum_range_cube]
  congr 1
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [eqW_rowNo, mul_comm]
  rfl

/-! ## What keeps a form without a written-out factor -/

/-- The empty form has no written-out factor. -/
theorem plainForm_empty : PlainForm {} := fun _ h => absurd h (List.not_mem_nil)

/-- A tensor without a written-out factor may be added. -/
theorem plainForm_add {f : Form} (hf : PlainForm f) {v : Tensor} (hv : v.denseVars = []) :
    PlainForm (f.add v) := fun w hw => by
  rcases List.mem_cons.1 hw with rfl | h
  · exact hv
  · exact hf w h

/-- A single entry adds no tensor. -/
theorem plainForm_addEntry {f : Form} (hf : PlainForm f) (i : ℕ) (c : E) :
    PlainForm (f.addEntry i c) := hf

/-- Scaling gives no tensor a written-out factor. -/
theorem plainForm_scale {f : Form} (hf : PlainForm f) (x : E) : PlainForm (f.scale x) :=
  fun w hw => by
    obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
    exact (scale_denseVars v x).trans (hf v hv)

/-- The sum of two forms without a written-out factor has none. -/
theorem plainForm_plus {f o : Form} (hf : PlainForm f) (ho : PlainForm o) :
    PlainForm (f.plus o) := fun w hw => by
  rcases List.mem_append.1 hw with h | h
  · exact ho w h
  · exact hf w h

/-- A multiple of a form without a written-out factor may be added. -/
theorem plainForm_addForm {f o : Form} (hf : PlainForm f) (ho : PlainForm o) (x : E) :
    PlainForm (f.addForm o x) := plainForm_plus hf (plainForm_scale ho x)

/-- Inserted variables that pick bits give a tensor no written-out factor. -/
theorem insertChoice_denseVars (v : Tensor) (hv : v.denseVars = []) (pos count value : ℕ) :
    (v.insertChoice pos count value).denseVars = [] := by
  show v.denseVars.map (fun d => if pos ≤ d then d + count else d) = []
  rw [hv]
  rfl

/-- Inserted variables that pick bits give a form no written-out factor. -/
theorem plainForm_insertChoice {f : Form} (hf : PlainForm f) (pos count value : ℕ) :
    PlainForm (f.insertChoice pos count value) := fun w hw => by
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  exact insertChoice_denseVars v (hf v hv) pos count value

/-- Fixing low variables keeps a form without a written-out factor. -/
theorem plainForm_fixLow {f : Form} (hf : PlainForm f) (g : List E) (times : E) :
    PlainForm (f.fixLow g times) := fun w hw => by
  rw [tensors_fixLow f hf g times] at hw
  obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hw
  rw [fixLow_plain (v.scale times) ((scale_denseVars v times).trans (hf v hv)) g]

/-- Each tensor loses as many variables as the point has coordinates. -/
theorem vars_fixLow {f : Form} (hf : PlainForm f) (g : List E) (times : E) (m : ℕ)
    (hv : ∀ v ∈ f.tensors, v.vars = g.length + m) : ∀ w ∈ (f.fixLow g times).tensors, w.vars = m :=
  fun w hw => by
    rw [tensors_fixLow f hf g times] at hw
    obtain ⟨v, hvm, rfl⟩ := List.mem_map.1 hw
    rw [fixLow_plain (v.scale times) ((scale_denseVars v times).trans (hf v hvm)) g]
    show (fixPairs (v.scale times).pairs g (v.scale times).scalar).2.length = m
    have h1 : (v.scale times).pairs.length = g.length + m := (scale_vars v times).trans (hv v hvm)
    rw [length_fixPairs, h1]
    omega

/-! ## The three vectors that the program's fold hands on -/

/-- The form on the main row, by definition. -/
theorem foldOutput_c (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : ℕ) (eps : E)
    (gamma : List E) (claim : E) :
    (foldOutput S F row fresh eps gamma claim).c = row.c.fixLow gamma eps := rfl

/-- The two written-out vectors, by definition. -/
theorem foldOutput_d (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : ℕ) (eps : E)
    (gamma : List E) (claim : E) :
    (foldOutput S F row fresh eps gamma claim).d =
      #[foldMaskForm F.layout.h row.d eps gamma,
        foldMaskWeights F.layout.k F.layout.h (S.codes.mask.getD F.maskCode default).ell
          gamma.toArray] := rfl

/-- The coefficients after the program's fold, read in the field, are those of the library's fold
(`midVec`): the form on the main row, the form on the carried mask row, and the weights on the fresh
mask row. Asked: the row's form has no written-out factor, and the sizes fit the stage. -/
theorem vecS_foldOutput (s : Sg) (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : ℕ)
    (eps : E) (gamma : List E) (claim : E) (hk : F.layout.k = s.h + s.g) (hh : F.layout.h = s.h)
    (hg : gamma.length = s.h + s.g) (hp : PlainForm row.c)
    (hv : ∀ v ∈ row.c.tensors, s.h + s.g ≤ v.vars) (hd : row.d.size = s.Z.l * 2 ^ s.h) :
    vecS s (foldOutput S F row fresh eps gamma claim) =
      midVec s s.Z.l (vecG s row) (readE eps) (readP (s.h + s.g) gamma) := by
  funext j
  rcases j with j | j | j
  · show formAt (foldOutput S F row fresh eps gamma claim).c j.val = _
    rw [foldOutput_c]
    exact formAt_fixLow row.c hp (s.h + s.g) gamma hg hv eps j.val
  · show readV ((foldOutput S F row fresh eps gamma claim).d.getD 0 #[]) j.val = _
    rw [foldOutput_d]
    show readV (foldMaskForm F.layout.h row.d eps gamma) j.val = _
    rw [hh]
    exact readV_foldMaskForm s.h s.g row.d eps gamma hg s.Z.l hd j.val
  · show readV ((foldOutput S F row fresh eps gamma claim).d.getD 1 #[]) j.val = _
    rw [foldOutput_d]
    show readV (foldMaskWeights F.layout.k F.layout.h
      (S.codes.mask.getD F.maskCode default).ell gamma.toArray) j.val = _
    have hz : (fun t : Fin (s.h + s.g) => readV gamma.toArray t.val) =
        fun t : Fin (s.h + s.g) => readL gamma t.val :=
      funext fun t => readV_toArray gamma t.val
    rw [hk, hh, readV_foldMaskWeights s.h s.g _ gamma.toArray j.val, hz]
    show _ = hideW s.h s.g s.Z.l (readP (s.h + s.g) gamma) j.val
    unfold hideW
    rw [if_pos j.isLt]
    rfl

/-- What the program's test of a row's sizes says of the form and of the written-out mask form. -/
theorem of_foldRowOk (S : Statement) (F : FoldShape) (row : GroupRow)
    (h : foldRowOk S F row = true) :
    (∀ v ∈ row.c.tensors,
      v.vars = F.layout.k + ceilLog2 (S.codes.base.getD F.code default).ell) ∧
      row.d.size = (S.codes.mask.getD F.maskCode default).ell * 2 ^ F.layout.h := by
  unfold foldRowOk Form.fits at h
  simp only [Bool.and_eq_true, List.all_eq_true, beq_iff_eq] at h
  exact ⟨fun v hv => (h.1.1.1 v hv).1, h.1.2⟩

/-- The same from the program's own test of the row's sizes. -/
theorem vecS_foldOutput_ok (s : Sg) (S : Statement) (F : FoldShape) (row : GroupRow) (fresh : ℕ)
    (eps : E) (gamma : List E) (claim : E) (hk : F.layout.k = s.h + s.g) (hh : F.layout.h = s.h)
    (hg : gamma.length = s.h + s.g) (hp : PlainForm row.c) (hok : foldRowOk S F row = true)
    (hZ : (S.codes.mask.getD F.maskCode default).ell = s.Z.l) :
    vecS s (foldOutput S F row fresh eps gamma claim) =
      midVec s s.Z.l (vecG s row) (readE eps) (readP (s.h + s.g) gamma) := by
  obtain ⟨h1, h2⟩ := of_foldRowOk S F row hok
  refine vecS_foldOutput s S F row fresh eps gamma claim hk hh hg hp (fun v hv => ?_) ?_
  · rw [h1 v hv, hk]
    exact Nat.le_add_right _ _
  · rw [h2, hZ, hh]

end OnBytes.Slice

#print axioms OnBytes.Slice.vecS_foldOutput_ok
#print axioms OnBytes.Slice.readV_foldLowB
#print axioms OnBytes.Slice.readV_foldMaskForm
#print axioms OnBytes.Slice.readV_foldMaskWeights
#print axioms OnBytes.Slice.readE_fixPairs
#print axioms OnBytes.Slice.tensorAt_fixLow
#print axioms OnBytes.Slice.sum_mergeEntries
#print axioms OnBytes.Slice.formAt_fixLow
#print axioms OnBytes.Slice.plainForm_fixLow
#print axioms OnBytes.Slice.vars_fixLow
#print axioms OnBytes.Slice.vecS_foldOutput
#print axioms OnBytes.Slice.size_foldLowOnce
#print axioms OnBytes.Slice.readV_foldLowOnce
#print axioms OnBytes.Slice.foldLowB_nil
#print axioms OnBytes.Slice.foldLowB_cons
#print axioms OnBytes.Slice.size_foldLowB
#print axioms OnBytes.Slice.readV_foldLowB_of
#print axioms OnBytes.Slice.readV_map_mul
#print axioms OnBytes.Slice.drop_eq_map
#print axioms OnBytes.Slice.prod_from
#print axioms OnBytes.Slice.readE_late
#print axioms OnBytes.Slice.foldMaskForm_def
#print axioms OnBytes.Slice.readE_behindB
#print axioms OnBytes.Slice.foldMaskWeights_eq
#print axioms OnBytes.Slice.readE_weightsL_at
#print axioms OnBytes.Slice.readL_weightsL
#print axioms OnBytes.Slice.fixPairs_nil_fun
#print axioms OnBytes.Slice.fixPairs_nil
#print axioms OnBytes.Slice.fixPairs_none_fun
#print axioms OnBytes.Slice.fixPairs_cons_fun
#print axioms OnBytes.Slice.length_fixPairs
#print axioms OnBytes.Slice.readE_entry_plain
#print axioms OnBytes.Slice.fixLow_plain
#print axioms OnBytes.Slice.scale_denseVars
#print axioms OnBytes.Slice.scale_vars
#print axioms OnBytes.Slice.fixLowShared_plain
#print axioms OnBytes.Slice.foldl_fixLowShared
#print axioms OnBytes.Slice.tensors_fixLow
#print axioms OnBytes.Slice.entries_fixLow
#print axioms OnBytes.Slice.entSum_cons
#print axioms OnBytes.Slice.entSum_join
#print axioms OnBytes.Slice.entry_fix
#print axioms OnBytes.Slice.sum_mul_list
#print axioms OnBytes.Slice.formAt_fixLow_range
#print axioms OnBytes.Slice.plainForm_empty
#print axioms OnBytes.Slice.plainForm_add
#print axioms OnBytes.Slice.plainForm_addEntry
#print axioms OnBytes.Slice.plainForm_scale
#print axioms OnBytes.Slice.plainForm_plus
#print axioms OnBytes.Slice.plainForm_addForm
#print axioms OnBytes.Slice.insertChoice_denseVars
#print axioms OnBytes.Slice.plainForm_insertChoice
#print axioms OnBytes.Slice.foldOutput_c
#print axioms OnBytes.Slice.foldOutput_d
#print axioms OnBytes.Slice.of_foldRowOk
