-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SimBasic.lean: what the format's vectors and codes compute, in the field.

Fmt/M1Types.lean and Fmt/M1Codes.lean hold the arithmetic that the written verifier of the proximity
test uses: vectors of triples of words, tables of weights of a point on the cube, folds, sums of
rows, and the symbols and generator rows of a code. This file reads each result in the fields
`GF` and `GE` and gives it as a closed form: the right side has only the inputs as they are read
in the field, finite sums and products, powers, and the library's weight `Alg.eqk`.

How inputs are read. `vec v i` (OnBytes/Slice/Stage.lean) is entry i of an array and `lst z t` is
entry t of a list; both are 0 beyond the end, as in the format's own arithmetic. So most statements
hold at every index and need no hypothesis on sizes. `eqW n z i` is `Alg.eqk` at the point with the
n coordinates z 0 to z (n - 1) and at the vertex of the n lowest binary digits of i, the lowest
digit first.

Main definitions: `lst`, `eqW`, `noRow`.
Main theorems. Weights: `vec_pv`, `vec_eqTab`, `toE_eqAt`. Vectors: `toE_dot`, `vec_addV`,
`vec_scaleV`, `vec_axpy`, `vec_powsE`. Folds: `vec_foldLow`, `toE_foldV`. Indices and vertices:
`eqW_rowNo`, `sum_range_cube`. Sums of rows: `vec_sumRows_c`, `vec_sumRows_d`,
`toE_sumRows_t`. Codes: `toF_genT`, `toF_genM`, `toF_symF`, `toE_symE`, `toE_encE`. Each array's
size has a statement of its own (`size_pv` and so on).

Not claimed. Nothing on a protocol. Nothing on the other field of the format.
-/
import OnBytes.Slice.FieldInv
import OnBytes.Slice.Cells
import OnBytes.Slice.Stage

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1

/-! ## How arrays, lists and vertices are read -/

/-- Entry t of a list of triples, read in the extension field; 0 beyond the end. -/
def lst (z : List E) (t : ℕ) : GE := toE (z.getD t Fmt.Fld.zeroE)

/-- The weight of a vertex of the cube at a point. The point has the n coordinates z 0 to z (n - 1);
the vertex has the n lowest binary digits of i, the lowest first. -/
def eqW (n : ℕ) (z : ℕ → GE) (i : ℕ) : GE :=
  Alg.eqk (fun t : Fin n => z t.val) (fun t : Fin n => i.testBit t.val)

/-- The weight, written out as a product. -/
theorem eqW_def (n : ℕ) (z : ℕ → GE) (i : ℕ) :
    eqW n z i = ∏ t : Fin n, if i.testBit t.val then z t.val else 1 - z t.val := rfl

/-- The faster product of the format is read as the product of the field. -/
theorem toE_mulEF (a b : E) : toE (Fmt.Fld.two.mulEF a b) = toE a * toE b :=
  (congrArg toE (Fmt.mulEF_eq .two a b)).trans (toE_mulE a b)

/-- The empty list is read as 0 at every index. -/
theorem lst_nil (i : ℕ) : lst [] i = 0 := toE_zeroE

/-- Entry 0 of a list is its head. -/
theorem lst_cons_zero (a : E) (l : List E) : lst (a :: l) 0 = toE a := rfl

/-- Entry i + 1 of a list is entry i of its tail. -/
theorem lst_cons_succ (a : E) (l : List E) (i : ℕ) : lst (a :: l) (i + 1) = lst l i := rfl

/-- A list made into an array is read as the list. -/
theorem vec_toArray (l : List E) (i : ℕ) : vec l.toArray i = lst l i := by
  unfold vec lst ent
  rw [Array.getD_eq_getD_getElem?, List.getElem?_toArray, List.getD_eq_getElem?_getD]

/-- An array is read as its list. -/
theorem vec_eq_lst (v : Array E) (i : ℕ) : vec v i = lst v.toList i :=
  vec_toArray v.toList i

/-- A list is read as 0 from its length on. -/
theorem lst_of_le (l : List E) (i : ℕ) (h : l.length ≤ i) : lst l i = 0 := by
  unfold lst
  rw [List.getD_eq_default _ _ h]
  exact toE_zeroE

/-- An array is read as 0 from its size on. -/
theorem vec_of_le (v : Array E) (i : ℕ) (h : v.size ≤ i) : vec v i = 0 := by
  rw [vec_eq_lst]
  exact lst_of_le _ _ (by rw [Array.length_toList]; exact h)

/-- Two lists, one after the other. -/
theorem lst_append : ∀ (A B : List E) (i : ℕ),
    lst (A ++ B) i = if i < A.length then lst A i else lst B (i - A.length)
  | [], _, _ => rfl
  | _ :: _, _, 0 => rfl
  | a :: A, B, i + 1 => by
      have hsub : i + 1 - (a :: A).length = i - A.length := Nat.succ_sub_succ _ _
      rw [hsub]
      exact (lst_append A B i).trans (if_congr Nat.succ_lt_succ_iff.symm rfl rfl)

/-- The first h entries of a list are read as the list's own. -/
theorem lst_take (h : ℕ) (l : List E) (t : ℕ) (ht : t < h) : lst (l.take h) t = lst l t := by
  unfold lst
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]

/-- A list of which every entry is multiplied by c. -/
theorem lst_map_mul (c : E) : ∀ (T : List E) (i : ℕ),
    lst (T.map (Fmt.Fld.two.mulEF c)) i = toE c * lst T i
  | [], i => by
      rw [List.map_nil, lst_nil, mul_zero]
  | a :: _, 0 => toE_mulEF c a
  | _ :: T, i + 1 => lst_map_mul c T i

/-- A list of zeros is read as 0 at every index. -/
theorem lst_replicate_zero : ∀ n i : ℕ, lst (List.replicate n Fmt.Fld.zeroE) i = 0
  | 0, i => lst_nil i
  | _ + 1, 0 => toE_zeroE
  | n + 1, i + 1 => lst_replicate_zero n i


/-! ## Laws of the weight -/

/-- On the cube without coordinates the weight is 1. -/
theorem eqW_zero (z : ℕ → GE) (i : ℕ) : eqW 0 z i = 1 := by
  rw [eqW_def]
  exact Finset.prod_empty

/-- One more variable on top. -/
theorem eqW_succ (n : ℕ) (z : ℕ → GE) (i : ℕ) :
    eqW (n + 1) z i = eqW n z i * (if i.testBit n then z n else 1 - z n) := by
  rw [eqW_def, eqW_def, Fin.prod_univ_castSucc]
  rfl

/-- One more variable at the bottom. -/
theorem eqW_succ' (n : ℕ) (z : ℕ → GE) (i : ℕ) :
    eqW (n + 1) z i =
      (if i.testBit 0 then z 0 else 1 - z 0) * eqW n (fun t => z (t + 1)) (i / 2) := by
  rw [eqW_def, eqW_def, Fin.prod_univ_succ]
  refine congrArg _ (Finset.prod_congr rfl fun t _ => ?_)
  rw [Fin.val_succ, Nat.testBit_succ]

/-- The weight reads the point's first n coordinates alone. -/
theorem eqW_congr (n : ℕ) (z z' : ℕ → GE) (i : ℕ) (h : ∀ t, t < n → z t = z' t) :
    eqW n z i = eqW n z' i := by
  rw [eqW_def, eqW_def]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [h t.val t.isLt]

/-- The weight reads the n lowest digits of the index alone. -/
theorem eqW_mod (n : ℕ) (z : ℕ → GE) (i : ℕ) : eqW n z (i % 2 ^ n) = eqW n z i := by
  rw [eqW_def, eqW_def]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [Nat.testBit_mod_two_pow, decide_eq_true t.isLt, Bool.true_and]


/-! ## Tables of weights -/

/-- One step doubles the table's length. -/
theorem length_eqStep (f : Fmt.Fld) (T : List E) (z : E) :
    (eqStep f T z).length = 2 * T.length := by
  unfold eqStep
  rw [List.length_append, List.length_map, List.length_map, Nat.two_mul]

/-- One step for each coordinate of z: the table's length times 2^(the length of z). -/
theorem length_eqFold (f : Fmt.Fld) : ∀ (z : List E) (T : List E),
    (z.foldl (eqStep f) T).length = T.length * 2 ^ z.length
  | [], T => by
      rw [List.foldl_nil, List.length_nil, pow_zero, Nat.mul_one]
  | x :: z, T => by
      rw [List.foldl_cons, length_eqFold f z, length_eqStep, List.length_cons, pow_succ]
      ring

/-- One step of the table: the old table under 1 - w, then under w. -/
theorem lst_eqStep (T : List E) (w : E) (i : ℕ) :
    lst (eqStep .two T w) i =
      if i < T.length then (1 - toE w) * lst T i else toE w * lst T (i - T.length) := by
  unfold eqStep
  rw [lst_append, List.length_map, lst_map_mul, lst_map_mul, toE_subE, toE_oneE]

/-- The table that `pv` builds, as a list. -/
theorem lst_eqFold (s : E) (z : List E) : ∀ i : ℕ,
    lst (z.foldl (eqStep .two) [s]) i =
      if i < 2 ^ z.length then toE s * eqW z.length (lst z) i else 0 := by
  induction z using List.reverseRecOn with
  | nil =>
    intro i
    rw [List.foldl_nil, List.length_nil, pow_zero]
    by_cases hi : i < 1
    · have h0 : i = 0 := by omega
      rw [if_pos hi, h0, eqW_zero, mul_one]
      rfl
    · rw [if_neg hi]
      exact lst_of_le _ _ (by rw [List.length_singleton]; omega)
  | append_singleton z w ih =>
    intro i
    have hlen : (z.foldl (eqStep .two) [s]).length = 2 ^ z.length := by
      rw [length_eqFold, List.length_singleton, Nat.one_mul]
    have hold : ∀ j, eqW z.length (lst (z ++ [w])) j = eqW z.length (lst z) j := fun j =>
      eqW_congr _ _ _ _ fun t ht => by rw [lst_append, if_pos ht]
    have htop : lst (z ++ [w]) z.length = toE w := by
      rw [lst_append, if_neg (Nat.lt_irrefl _), Nat.sub_self]
      rfl
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil, lst_eqStep, hlen,
      List.length_append, List.length_singleton, eqW_succ, hold, htop, pow_succ]
    by_cases h1 : i < 2 ^ z.length
    · have h2 : i < 2 ^ z.length * 2 := by omega
      rw [if_pos h1, if_pos h2, ih, if_pos h1, Nat.testBit_lt_two_pow h1]
      simp only [Bool.false_eq_true, if_false]
      ring
    · rw [if_neg h1, ih]
      by_cases h2 : i < 2 ^ z.length * 2
      · have h3 : i - 2 ^ z.length < 2 ^ z.length := by omega
        have hbit : i.testBit z.length = true := by
          rw [Nat.testBit_eq_decide_div_mod_eq]
          have hd : i / 2 ^ z.length = 1 :=
            Nat.div_eq_of_lt_le (by omega) (by omega)
          rw [hd]
          rfl
        have hlow : eqW z.length (lst z) (i - 2 ^ z.length) = eqW z.length (lst z) i := by
          rw [← eqW_mod _ _ i, ← eqW_mod _ _ (i - 2 ^ z.length)]
          congr 1
          rw [Nat.mod_eq_sub_mod (Nat.le_of_not_lt h1)]
        rw [if_pos h3, if_pos h2, hbit, hlow, if_pos rfl]
        ring
      · have h3 : ¬ i - 2 ^ z.length < 2 ^ z.length := by omega
        rw [if_neg h3, if_neg h2, mul_zero]

/-- The table `pv s z` has one entry for each vertex. -/
theorem size_pv (f : Fmt.Fld) (s : E) (z : List E) : (pv f s z).size = 2 ^ z.length := by
  unfold pv
  rw [List.size_toArray, length_eqFold, List.length_singleton, Nat.one_mul]

/-- Entry i of `pv s z` is s times the weight of the vertex i at the point z. -/
theorem vec_pv (s : E) (z : List E) (i : ℕ) :
    vec (pv .two s z) i = if i < 2 ^ z.length then toE s * eqW z.length (lst z) i else 0 := by
  unfold pv
  rw [vec_toArray]
  exact lst_eqFold s z i

/-- The table `eqTab z` has one entry for each vertex. -/
theorem size_eqTab (f : Fmt.Fld) (z : List E) : (eqTab f z).size = 2 ^ z.length :=
  size_pv f Fmt.Fld.oneE z

/-- Entry i of `eqTab z` is the weight of the vertex i at the point z. -/
theorem vec_eqTab (z : List E) (i : ℕ) :
    vec (eqTab .two z) i = if i < 2 ^ z.length then eqW z.length (lst z) i else 0 := by
  have h := vec_pv Fmt.Fld.oneE z i
  rw [toE_oneE, one_mul] at h
  exact h

/-- The loop of `eqAt`, from any state. -/
theorem toE_eqAtLoop : ∀ (z : List E) (a : E) (j : ℕ),
    toE (z.foldl (fun (s : E × Nat) x => (Fmt.Fld.two.mulE s.1
      (if s.2 % 2 = 1 then x else Fmt.Fld.two.subE Fmt.Fld.oneE x), s.2 / 2)) (a, j)).1 =
      toE a * eqW z.length (lst z) j
  | [], a, j => by
      rw [List.foldl_nil, List.length_nil, eqW_zero, mul_one]
  | x :: z, a, j => by
      have hz : (fun t => lst (x :: z) (t + 1)) = lst z := rfl
      rw [List.foldl_cons, toE_eqAtLoop z, toE_mulE, List.length_cons, eqW_succ', hz,
        lst_cons_zero, Nat.testBit_zero, mul_assoc]
      by_cases hj : j % 2 = 1
      · rw [if_pos hj, decide_eq_true hj, if_pos rfl]
      · rw [if_neg hj, decide_eq_false hj, toE_subE, toE_oneE]
        rfl

/-- `eqAt z j` is the weight of the vertex of the lowest digits of j, for every j. -/
theorem toE_eqAt (z : List E) (j : ℕ) : toE (eqAt .two z j) = eqW z.length (lst z) j := by
  unfold eqAt
  rw [toE_eqAtLoop, toE_oneE, one_mul]


/-! ## Vectors -/

/-- The loop of the inner product, started from any sum acc. -/
theorem toE_dotL : ∀ (u v : List E) (acc : E),
    toE (dotL .two u v acc) =
      toE acc + ∑ i ∈ Finset.range (min u.length v.length), lst u i * lst v i
  | [], v, acc => by
      rw [List.length_nil, Nat.zero_min, Finset.sum_range_zero, add_zero]
      rfl
  | a :: u, [], acc => by
      rw [List.length_nil, Nat.min_zero, Finset.sum_range_zero, add_zero]
      rfl
  | a :: u, b :: v, acc => by
      have step : dotL .two (a :: u) (b :: v) acc =
          dotL .two u v (Fmt.Fld.two.addE acc (Fmt.Fld.two.mulEF a b)) := rfl
      rw [step, toE_dotL u v, toE_addE, toE_mulEF, List.length_cons, List.length_cons,
        Nat.succ_min_succ, Finset.sum_range_succ']
      simp only [lst_cons_succ, lst_cons_zero]
      ring

/-- The inner product runs as far as both vectors reach. -/
theorem toE_dot (u v : Array E) :
    toE (dot .two u v) = ∑ i ∈ Finset.range (min u.size v.size), vec u i * vec v i := by
  unfold dot
  rw [toE_dotL, toE_zeroE, zero_add, Array.length_toList, Array.length_toList]
  exact Finset.sum_congr rfl fun i _ => by rw [vec_eq_lst, vec_eq_lst]

/-- The inner product as a sum over any range that holds the shorter vector. -/
theorem toE_dot_of_le (u v : Array E) (n : ℕ) (h : min u.size v.size ≤ n) :
    toE (dot .two u v) = ∑ i ∈ Finset.range n, vec u i * vec v i := by
  rw [toE_dot]
  refine Finset.sum_subset (Finset.range_mono h) fun i _ hi => ?_
  have hle : min u.size v.size ≤ i := Nat.le_of_not_lt fun hlt => hi (Finset.mem_range.2 hlt)
  rcases min_le_iff.1 hle with hu | hv
  · rw [vec_of_le u i hu, zero_mul]
  · rw [vec_of_le v i hv, mul_zero]

/-- A list filled up to n entries; a longer list keeps its length. -/
theorem length_padL (n : ℕ) (u : List E) : (padL n u).length = max u.length n := by
  unfold padL
  rw [List.length_append, List.length_replicate]
  omega

/-- Filling up with 0 does not change what is read. -/
theorem lst_padL (n : ℕ) (u : List E) (i : ℕ) : lst (padL n u) i = lst u i := by
  unfold padL
  rw [lst_append, lst_replicate_zero]
  by_cases h : i < u.length
  · rw [if_pos h]
  · rw [if_neg h, lst_of_le u i (Nat.le_of_not_lt h)]

/-- The sum of two lists of one length, entry by entry. -/
theorem lst_zipAdd : ∀ (A B : List E) (i : ℕ), A.length = B.length →
    lst (List.zipWith Fmt.Fld.two.addE A B) i = lst A i + lst B i
  | [], [], i, _ => by
      rw [List.zipWith_nil_left, lst_nil, add_zero]
  | a :: _, b :: _, 0, _ => toE_addE a b
  | _ :: A, _ :: B, i + 1, h => lst_zipAdd A B i (Nat.succ.inj h)

/-- The sum of two vectors is as long as the longer one. -/
theorem size_addV (f : Fmt.Fld) (u v : Array E) : (addV f u v).size = max u.size v.size := by
  unfold addV addL
  rw [List.size_toArray, List.length_zipWith, length_padL, length_padL, Array.length_toList,
    Array.length_toList]
  omega

/-- The sum of two vectors, entry by entry; the shorter one counts as filled with 0. -/
theorem vec_addV (u v : Array E) (i : ℕ) : vec (addV .two u v) i = vec u i + vec v i := by
  unfold addV addL
  rw [vec_toArray, lst_zipAdd _ _ _ (by rw [length_padL, length_padL, Nat.max_comm]), lst_padL,
    lst_padL, vec_eq_lst, vec_eq_lst]

/-- Multiplying by s keeps the size. -/
theorem size_scaleV (f : Fmt.Fld) (s : E) (v : Array E) : (scaleV f s v).size = v.size := by
  unfold scaleV
  rw [List.size_toArray, List.length_map, Array.length_toList]

/-- A vector of which every entry is multiplied by s. -/
theorem vec_scaleV (s : E) (v : Array E) (i : ℕ) :
    vec (scaleV .two s v) i = toE s * vec v i := by
  unfold scaleV
  rw [vec_toArray, lst_map_mul, vec_eq_lst]

/-- The vector u + s v is as long as the longer of u and v. -/
theorem size_axpy (f : Fmt.Fld) (u : Array E) (s : E) (v : Array E) :
    (axpy f u s v).size = max u.size v.size := by
  unfold axpy
  rw [size_addV, size_scaleV]

/-- The vector u + s v. -/
theorem vec_axpy (u : Array E) (s : E) (v : Array E) (i : ℕ) :
    vec (axpy .two u s v) i = vec u i + toE s * vec v i := by
  unfold axpy
  rw [vec_addV, vec_scaleV]

/-- The loop of the powers puts what it has gathered in front. -/
theorem powsL_acc (f : Fmt.Fld) (x : E) : ∀ (n : ℕ) (c : E) (acc : List E),
    powsL f x n c acc = acc.reverse ++ powsL f x n c []
  | 0, _, acc => (List.append_nil _).symm
  | n + 1, c, acc => by
      have s1 : powsL f x (n + 1) c acc = powsL f x n (f.mulEF c x) (c :: acc) := rfl
      have s2 : powsL f x (n + 1) c [] = powsL f x n (f.mulEF c x) [c] := rfl
      rw [s1, s2, powsL_acc f x n _ (c :: acc), powsL_acc f x n _ [c], List.reverse_cons,
        List.reverse_singleton, List.append_assoc]

/-- The loop of the powers, one step: the first member is c, the rest starts from c x. -/
theorem powsL_succ (f : Fmt.Fld) (x : E) (n : ℕ) (c : E) :
    powsL f x (n + 1) c [] = c :: powsL f x n (f.mulEF c x) [] :=
  powsL_acc f x n (f.mulEF c x) [c]

/-- The loop of the powers gives n members. -/
theorem length_powsL (f : Fmt.Fld) (x : E) : ∀ (n : ℕ) (c : E), (powsL f x n c []).length = n
  | 0, _ => rfl
  | n + 1, c => by
      rw [powsL_succ, List.length_cons, length_powsL f x n]

/-- Member i of the loop of the powers, started from c, is c x^i, for i below n. -/
theorem lst_powsL (x : E) : ∀ (n : ℕ) (c : E) (i : ℕ),
    lst (powsL .two x n c []) i = if i < n then toE c * toE x ^ i else 0
  | 0, _, i => by
      rw [if_neg (Nat.not_lt_zero i)]
      exact lst_nil i
  | n + 1, c, 0 => by
      rw [powsL_succ, lst_cons_zero, if_pos (Nat.succ_pos n), pow_zero, mul_one]
  | n + 1, c, i + 1 => by
      rw [powsL_succ, lst_cons_succ, lst_powsL x n, toE_mulEF, pow_succ']
      by_cases h : i < n
      · rw [if_pos h, if_pos (Nat.succ_lt_succ h), mul_assoc]
      · rw [if_neg h, if_neg fun hh => h (Nat.lt_of_succ_lt_succ hh)]

/-- The vector `powsE x n` has n entries. -/
theorem size_powsE (f : Fmt.Fld) (x : E) (n : ℕ) : (powsE f x n).size = n := by
  unfold powsE
  rw [List.size_toArray, length_powsL]

/-- Entry i of `powsE x n` is x^i, for i below n. -/
theorem vec_powsE (x : E) (n i : ℕ) :
    vec (powsE .two x n) i = if i < n then toE x ^ i else 0 := by
  unfold powsE
  rw [vec_toArray, lst_powsL, toE_oneE, one_mul]


/-! ## Folds -/

/-- The loop of one fold puts what it has gathered in front. -/
theorem fold1A_acc (f : Fmt.Fld) (g : E) : ∀ (T acc : List E),
    fold1A f g T acc = acc.reverse ++ fold1A f g T []
  | [], acc => (List.append_nil _).symm
  | [a], acc => by
      have s1 : fold1A f g [a] acc =
          (f.addE a (f.mulEF g (f.subE Fmt.Fld.zeroE a)) :: acc).reverse := rfl
      have s2 : fold1A f g [a] [] = [f.addE a (f.mulEF g (f.subE Fmt.Fld.zeroE a))] := rfl
      rw [s1, s2, List.reverse_cons]
  | a :: b :: T, acc => by
      have s1 : fold1A f g (a :: b :: T) acc =
          fold1A f g T (f.addE a (f.mulEF g (f.subE b a)) :: acc) := rfl
      have s2 : fold1A f g (a :: b :: T) [] =
          fold1A f g T [f.addE a (f.mulEF g (f.subE b a))] := rfl
      rw [s1, s2, fold1A_acc f g T (_ :: acc), fold1A_acc f g T [_], List.reverse_cons,
        List.reverse_singleton, List.append_assoc]

/-- One fold on the first two entries a and b gives a + g (b - a); the rest is folded alike. -/
theorem fold1L_cons_cons (f : Fmt.Fld) (g a b : E) (T : List E) :
    fold1L f g (a :: b :: T) = f.addE a (f.mulEF g (f.subE b a)) :: fold1L f g T :=
  fold1A_acc f g T [f.addE a (f.mulEF g (f.subE b a))]

/-- One fold halves the length, rounded up. -/
theorem length_fold1L (f : Fmt.Fld) (g : E) : ∀ T : List E,
    (fold1L f g T).length = (T.length + 1) / 2
  | [] => rfl
  | [a] => by
      have h : fold1L f g [a] = [f.addE a (f.mulEF g (f.subE Fmt.Fld.zeroE a))] := rfl
      have h1 : (fold1L f g [a]).length = 1 := congrArg List.length h
      have h2 : [a].length = 1 := rfl
      omega
  | a :: b :: T => by
      rw [fold1L_cons_cons, List.length_cons, length_fold1L f g T, List.length_cons,
        List.length_cons]
      omega

/-- One fold: entry i of the new list from the entries 2 i and 2 i + 1 of the old one. -/
theorem lst_fold1L (g : E) : ∀ (T : List E) (i : ℕ),
    lst (fold1L .two g T) i = (1 - toE g) * lst T (2 * i) + toE g * lst T (2 * i + 1)
  | [], i => by
      have h : fold1L .two g [] = [] := rfl
      rw [h, lst_nil, lst_nil, lst_nil, mul_zero, mul_zero, add_zero]
  | [a], 0 => by
      have h : fold1L .two g [a] =
          [Fmt.Fld.two.addE a (Fmt.Fld.two.mulEF g (Fmt.Fld.two.subE Fmt.Fld.zeroE a))] := rfl
      have h1 : lst [a] (2 * 0 + 1) = 0 := lst_nil 0
      have h0 : lst [a] (2 * 0) = toE a := rfl
      rw [h, lst_cons_zero, toE_addE, toE_mulEF, toE_subE, toE_zeroE, h0, h1]
      ring
  | [a], i + 1 => by
      have h0 : lst [a] (2 * (i + 1)) = 0 := lst_of_le _ _ (by rw [List.length_singleton]; omega)
      have h1 : lst [a] (2 * (i + 1) + 1) = 0 :=
        lst_of_le _ _ (by rw [List.length_singleton]; omega)
      have h2 : lst (fold1L .two g [a]) (i + 1) = 0 :=
        lst_of_le _ _ (by rw [length_fold1L, List.length_singleton]; omega)
      rw [h0, h1, h2, mul_zero, mul_zero, add_zero]
  | a :: b :: T, 0 => by
      have h0 : lst (a :: b :: T) (2 * 0) = toE a := rfl
      have h1 : lst (a :: b :: T) (2 * 0 + 1) = toE b := rfl
      rw [fold1L_cons_cons, lst_cons_zero, toE_addE, toE_mulEF, toE_subE, h0, h1]
      ring
  | a :: b :: T, i + 1 => by
      have h0 : lst (a :: b :: T) (2 * (i + 1)) = lst T (2 * i) := rfl
      have h1 : lst (a :: b :: T) (2 * (i + 1) + 1) = lst T (2 * i + 1) := rfl
      rw [fold1L_cons_cons, lst_cons_succ, lst_fold1L g T i, h0, h1]

/-- A sum over an even range, taken in pairs. -/
theorem sum_range_two_mul (F : ℕ → GE) : ∀ m : ℕ,
    ∑ i ∈ Finset.range (2 * m), F i = ∑ i ∈ Finset.range m, (F (2 * i) + F (2 * i + 1))
  | 0 => rfl
  | m + 1 => by
      have h : 2 * (m + 1) = 2 * m + 1 + 1 := by ring
      rw [h, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
        sum_range_two_mul F m, add_assoc]

/-- One fold for each member of g: the length divided by 2^(the length of g), rounded up. -/
theorem length_foldL (f : Fmt.Fld) : ∀ (g T : List E),
    (g.foldl (fun T x => fold1L f x T) T).length = (T.length + 2 ^ g.length - 1) / 2 ^ g.length
  | [], T => by
      rw [List.foldl_nil, List.length_nil, pow_zero, Nat.add_sub_cancel, Nat.div_one]
  | x :: g, T => by
      have hpos : 0 < 2 ^ g.length := Nat.two_pow_pos _
      have half :
          (T.length + 1) / 2 + 2 ^ g.length - 1 = (T.length + 2 * 2 ^ g.length - 1) / 2 := by
        omega
      rw [List.foldl_cons, length_foldL f g, length_fold1L, List.length_cons, half,
        Nat.div_div_eq_div_mul, pow_succ']

/-- All folds, on lists. -/
theorem lst_foldL : ∀ (g T : List E) (p : ℕ),
    lst (g.foldl (fun T x => fold1L .two x T) T) p =
      ∑ b ∈ Finset.range (2 ^ g.length), eqW g.length (lst g) b * lst T (b + 2 ^ g.length * p)
  | [], T, p => by
      rw [List.foldl_nil, List.length_nil, pow_zero, Finset.sum_range_one, eqW_zero, one_mul,
        Nat.zero_add, Nat.one_mul]
  | x :: g, T, p => by
      have hz : (fun t => lst (x :: g) (t + 1)) = lst g := rfl
      rw [List.foldl_cons, lst_foldL g, List.length_cons, pow_succ', sum_range_two_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      have e0 : (2 * b).testBit 0 = false := by
        rw [Nat.testBit_zero]
        exact decide_eq_false (by omega)
      have e1 : (2 * b + 1).testBit 0 = true := by
        rw [Nat.testBit_zero]
        exact decide_eq_true (by omega)
      have d0 : 2 * b / 2 = b := by omega
      have d1 : (2 * b + 1) / 2 = b := by omega
      have i0 : 2 * (b + 2 ^ g.length * p) = 2 * b + 2 * 2 ^ g.length * p := by ring
      have i1 : 2 * (b + 2 ^ g.length * p) + 1 = 2 * b + 1 + 2 * 2 ^ g.length * p := by ring
      rw [lst_fold1L, eqW_succ', eqW_succ', hz, e0, e1, d0, d1, i1, i0, lst_cons_zero, if_pos rfl,
        if_neg Bool.false_ne_true]
      ring

/-- Each variable halves the length, rounded up. -/
theorem size_foldLow (f : Fmt.Fld) (g : List E) (T : Array E) :
    (foldLow f g T).size = (T.size + 2 ^ g.length - 1) / 2 ^ g.length := by
  unfold foldLow
  rw [List.size_toArray, length_foldL, Array.length_toList]

/-- Entry p of a folded table: the rows b of the table under the weights of the point g. -/
theorem vec_foldLow (g : List E) (T : Array E) (p : ℕ) :
    vec (foldLow .two g T) p =
      ∑ b ∈ Finset.range (2 ^ g.length), eqW g.length (lst g) b * vec T (b + 2 ^ g.length * p) := by
  unfold foldLow
  rw [vec_toArray, lst_foldL]
  exact Finset.sum_congr rfl fun b _ => by rw [vec_eq_lst]

/-- A vector folded to one element. -/
theorem toE_foldV (g : List E) (v : Array E) :
    toE (foldV .two g v) =
      ∑ b ∈ Finset.range (2 ^ g.length), eqW g.length (lst g) b * vec v b := by
  have h := vec_foldLow g v 0
  simp only [Nat.mul_zero, Nat.add_zero] at h
  exact h


/-! ## Indices and vertices -/

/-- The weight at the number of a vertex is the library's weight at the vertex. -/
theorem eqW_rowNo (k : ℕ) (z : ℕ → GE) (β : Fin k → Bool) :
    eqW k z (Sz.rowNo β) = Alg.eqk (fun t : Fin k => z t.val) β := by
  unfold eqW
  exact congrArg _ (funext fun t => testBit_rowNo β t)

/-- A sum over the indices below 2^k is the sum over the vertices of the cube. -/
theorem sum_range_cube (k : ℕ) (F : ℕ → GE) :
    ∑ b ∈ Finset.range (2 ^ k), F b = ∑ β : Fin k → Bool, F (Sz.rowNo β) :=
  (sum_rowNo k F).symm

/-- The weight at a list's point, with the point as a function on `Fin n`. -/
theorem eqW_lst (n : ℕ) (g : List E) (i : ℕ) :
    eqW n (lst g) i = Alg.eqk (ptL n g) (fun t : Fin n => i.testBit t.val) := rfl


/-! ## Sums of rows -/

/-- The row without entries and with the target 0. It is what is read beyond a list's end. -/
def noRow : GRow := ⟨#[], #[], Fmt.Fld.zeroE⟩

/-- One step of the loop of `sumRows`: the state is the sum of the rows before this one and the
power of x for this one. -/
def rowStep (f : Fmt.Fld) (x : E) (s : GRow × E) (R : GRow) : GRow × E :=
  (⟨axpy f s.1.c s.2 R.c, axpy f s.1.d s.2 R.d, f.addE s.1.t (f.mulE s.2 R.t)⟩, f.mulE s.2 x)

/-- `sumRows` is the loop of `rowStep`, started from the empty row and the power 1. -/
theorem sumRows_eq (f : Fmt.Fld) (x : E) (rows : List GRow) :
    sumRows f x rows = (rows.foldl (rowStep f x) (noRow, Fmt.Fld.oneE)).1 := rfl

/-- The loop of `sumRows` from any state, read through any map φ of rows that is additive in the
way that the three parts of a row are. -/
theorem rowLoop (x : E) (φ : GRow → GE)
    (hφ : ∀ (s : GRow × E) (R : GRow), φ (rowStep .two x s R).1 = φ s.1 + toE s.2 * φ R) :
    ∀ (rows : List GRow) (s : GRow × E),
      φ (rows.foldl (rowStep .two x) s).1 =
        φ s.1 + ∑ k ∈ Finset.range rows.length, toE s.2 * toE x ^ k * φ (rows.getD k noRow)
  | [], s => by
      rw [List.foldl_nil, List.length_nil, Finset.sum_range_zero, add_zero]
  | R :: rows, s => by
      have hc : toE (rowStep .two x s R).2 = toE s.2 * toE x := toE_mulE _ _
      rw [List.foldl_cons, rowLoop x φ hφ rows, hφ, hc, List.length_cons,
        Finset.sum_range_succ', add_assoc]
      congr 1
      rw [add_comm]
      congr 1
      · exact Finset.sum_congr rfl fun k _ => by
          rw [List.getD_cons_succ, pow_succ']
          ring
      · rw [List.getD_cons_zero, pow_zero, mul_one]

/-- The sum of the rows, row number k under x^k: the coefficients on the main table. -/
theorem vec_sumRows_c (x : E) (rows : List GRow) (i : ℕ) :
    vec (sumRows .two x rows).c i =
      ∑ k ∈ Finset.range rows.length, toE x ^ k * vec (rows.getD k noRow).c i := by
  have h := rowLoop x (fun R => vec R.c i) (fun s R => vec_axpy s.1.c s.2 R.c i) rows
    (noRow, Fmt.Fld.oneE)
  have h0 : vec noRow.c i = 0 := vec_of_le _ _ (Nat.zero_le i)
  rw [sumRows_eq]
  simp only [toE_oneE, one_mul, h0, zero_add] at h
  exact h

/-- The sum of the rows, row number k under x^k: the coefficients on the mask table. -/
theorem vec_sumRows_d (x : E) (rows : List GRow) (i : ℕ) :
    vec (sumRows .two x rows).d i =
      ∑ k ∈ Finset.range rows.length, toE x ^ k * vec (rows.getD k noRow).d i := by
  have h := rowLoop x (fun R => vec R.d i) (fun s R => vec_axpy s.1.d s.2 R.d i) rows
    (noRow, Fmt.Fld.oneE)
  have h0 : vec noRow.d i = 0 := vec_of_le _ _ (Nat.zero_le i)
  rw [sumRows_eq]
  simp only [toE_oneE, one_mul, h0, zero_add] at h
  exact h

/-- The sum of the rows, row number k under x^k: the target. -/
theorem toE_sumRows_t (x : E) (rows : List GRow) :
    toE (sumRows .two x rows).t =
      ∑ k ∈ Finset.range rows.length, toE x ^ k * toE (rows.getD k noRow).t := by
  have h := rowLoop x (fun R => toE R.t)
    (fun s R => (toE_addE _ _).trans (congrArg _ (toE_mulE _ _))) rows (noRow, Fmt.Fld.oneE)
  have h0 : toE noRow.t = 0 := toE_zeroE
  rw [sumRows_eq]
  simp only [toE_oneE, one_mul, h0, zero_add] at h
  exact h

/-- The sizes in the loop of `sumRows`, from any state. -/
theorem rowLoop_size (f : Fmt.Fld) (x : E) (σ : GRow → ℕ)
    (hσ : ∀ (s : GRow × E) (R : GRow), σ (rowStep f x s R).1 = max (σ s.1) (σ R)) :
    ∀ (rows : List GRow) (s : GRow × E),
      σ (rows.foldl (rowStep f x) s).1 = rows.foldl (fun n R => max n (σ R)) (σ s.1)
  | [], _ => rfl
  | R :: rows, s => by
      rw [List.foldl_cons, List.foldl_cons, rowLoop_size f x σ hσ rows, hσ]

/-- The sum's part on the main table is as long as the longest row's. -/
theorem size_sumRows_c (f : Fmt.Fld) (x : E) (rows : List GRow) :
    (sumRows f x rows).c.size = rows.foldl (fun n R => max n R.c.size) 0 :=
  rowLoop_size f x (fun R => R.c.size) (fun s R => size_axpy f s.1.c s.2 R.c) rows
    (noRow, Fmt.Fld.oneE)

/-- The sum's part on the mask table is as long as the longest row's. -/
theorem size_sumRows_d (f : Fmt.Fld) (x : E) (rows : List GRow) :
    (sumRows f x rows).d.size = rows.foldl (fun n R => max n R.d.size) 0 :=
  rowLoop_size f x (fun R => R.d.size) (fun s R => size_axpy f s.1.d s.2 R.d) rows
    (noRow, Fmt.Fld.oneE)


/-! ## Codes -/

/-- The list `powers z n s` has n members. -/
theorem length_powers (z : UInt64) : ∀ (n : ℕ) (s : UInt64), (powers z n s).length = n
  | 0, _ => rfl
  | n + 1, s => congrArg (· + 1) (length_powers z n (Fmt.Fld.two.mul s z))

/-- Member j of `powers z n s` is s z^j, for j below n. -/
theorem toF_powers (z : UInt64) : ∀ (n : ℕ) (s : UInt64) (j : ℕ),
    toF ((powers z n s).getD j 0) = if j < n then toF s * toF z ^ j else 0
  | 0, _, j => by
      rw [if_neg (Nat.not_lt_zero j)]
      exact toF_zero
  | n + 1, s, 0 => by
      rw [if_pos (Nat.succ_pos n), pow_zero, mul_one]
      rfl
  | n + 1, s, j + 1 => by
      have step : (powers z (n + 1) s).getD (j + 1) 0 =
          (powers z n (Fmt.Fld.two.mul s z)).getD j 0 := rfl
      rw [step, toF_powers z n, toF_mul, pow_succ']
      by_cases h : j < n
      · rw [if_pos h, if_pos (Nat.succ_lt_succ h), mul_assoc]
      · rw [if_neg h, if_neg fun hh => h (Nat.lt_of_succ_lt_succ hh)]

/-- The generator's row on the tail has as many members as the tail. -/
theorem length_genT (C : Code) (x : ℕ) : (genT C x).length = C.r := length_powers _ _ _

/-- The generator's row on the message has as many members as the message. -/
theorem length_genM (C : Code) (x : ℕ) : (genM C x).length = C.l := length_powers _ _ _

/-- The generator's row on the tail: the powers of the point from exponent 0 on. -/
theorem toF_genT (C : Code) (x j : ℕ) :
    toF ((genT C x).getD j 0) = if j < C.r then toF (point C.a x) ^ j else 0 := by
  unfold genT
  rw [toF_powers, toF_one, one_mul]

/-- The generator's row on the message: the powers of the point from exponent r on. -/
theorem toF_genM (C : Code) (x j : ℕ) :
    toF ((genM C x).getD j 0) = if j < C.l then toF (point C.a x) ^ (C.r + j) else 0 := by
  unfold genM
  rw [toF_powers, toF_pow, pow_add]

/-- A list of words, each taken as an element of the extension field. -/
theorem lst_map_ofF : ∀ (l : List UInt64) (j : ℕ),
    lst (l.map Fmt.Fld.ofF) j = algebraMap GF GE (toF (l.getD j 0))
  | [], j => by
      have h : toF (([] : List UInt64).getD j 0) = 0 := toF_zero
      rw [List.map_nil, lst_nil, h, map_zero]
  | a :: _, 0 => toE_ofF a
  | _ :: l, j + 1 => lst_map_ofF l j

/-- The generator's row on the tail, as a vector over the extension field. -/
theorem vec_genTE (C : Code) (x j : ℕ) :
    vec (genTE C x) j = if j < C.r then algebraMap GF GE (toF (point C.a x) ^ j) else 0 := by
  unfold genTE
  rw [vec_toArray, lst_map_ofF, toF_genT]
  split
  · rfl
  · exact map_zero _

/-- The generator's row on the message, as a vector over the extension field. -/
theorem vec_genME (C : Code) (x j : ℕ) :
    vec (genME C x) j =
      if j < C.l then algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) else 0 := by
  unfold genME
  rw [vec_toArray, lst_map_ofF, toF_genM]
  split
  · rfl
  · exact map_zero _

/-- The library's generator matrix on the tail is the format's row. -/
theorem genOf_castAdd (C : Code) (x : Fin (2 ^ C.a)) (q : Fin C.r) :
    genOf C x (Fin.castAdd C.l q) = vec (genTE C x.val) q.val := by
  rw [vec_genTE, if_pos q.isLt]
  rfl

/-- The library's generator matrix on the message is the format's row. -/
theorem genOf_natAdd (C : Code) (x : Fin (2 ^ C.a)) (j : Fin C.l) :
    genOf C x (Fin.natAdd C.r j) = vec (genME C x.val) j.val := by
  rw [vec_genME, if_pos j.isLt]
  rfl

/-- A list cut or filled to n members has n members. -/
theorem length_fitL {α : Type} (d : α) (n : ℕ) (l : List α) : (fitL d n l).length = n := by
  unfold fitL
  rw [List.length_append, List.length_take, List.length_replicate]
  omega

/-- A list cut or filled to n members: below n it is read as the list itself. -/
theorem getD_fitL {α : Type} (d : α) (n : ℕ) (l : List α) (k : ℕ) (hk : k < n) :
    (fitL d n l).getD k d = l.getD k d := by
  unfold fitL
  by_cases h : k < l.length
  · have h1 : k < (l.take n).length := by
      rw [List.length_take]
      omega
    rw [List.getD_append _ _ _ _ h1, List.getD_eq_getElem _ _ h1, List.getD_eq_getElem _ _ h,
      List.getElem_take]
  · have h1 : (l.take n).length ≤ k := by
      rw [List.length_take]
      omega
    rw [List.getD_append_right _ _ _ _ h1, List.getD_eq_default l d (Nat.le_of_not_lt h)]
    by_cases h2 : k - (l.take n).length < n - l.length
    · rw [List.getD_replicate _ h2]
    · rw [List.getD_eq_default _ _ (by rw [List.length_replicate]; omega)]

/-- The value of a polynomial over the base field, given by its list of coefficients. -/
theorem toF_hornerF (z : UInt64) : ∀ cs : List UInt64,
    toF (hornerF z cs) = ∑ k ∈ Finset.range cs.length, toF z ^ k * toF (cs.getD k 0)
  | [] => toF_zero
  | c :: cs => by
      have step : hornerF z (c :: cs) = Fmt.Fld.two.add c (Fmt.Fld.two.mul z (hornerF z cs)) := rfl
      rw [step, toF_add, toF_mul, toF_hornerF z cs, List.length_cons, Finset.sum_range_succ',
        Finset.mul_sum, List.getD_cons_zero, pow_zero, one_mul, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by
        rw [List.getD_cons_succ, pow_succ', mul_assoc]

/-- The same with coefficients in the extension field. -/
theorem toE_hornerE (z : UInt64) : ∀ cs : List E,
    toE (hornerE z cs) = ∑ k ∈ Finset.range cs.length, algebraMap GF GE (toF z ^ k) * lst cs k
  | [] => toE_zeroE
  | c :: cs => by
      have step : hornerE z (c :: cs) =
          Fmt.Fld.two.addE c (Fmt.Fld.two.scaleE z (hornerE z cs)) := rfl
      rw [step, toE_addE, toE_scaleE, toE_hornerE z cs, List.length_cons,
        Finset.sum_range_succ', Algebra.smul_def, Finset.mul_sum, lst_cons_zero, pow_zero, map_one,
        one_mul, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by
        rw [lst_cons_succ, pow_succ', map_mul, mul_assoc]

/-- A symbol over the base field: the polynomial with the tail's and then the message's entries as
coefficients, at the point. Lists that are too short count as filled with 0; too long, as cut. -/
theorem toF_symF (C : Code) (x : ℕ) (m rho : List UInt64) :
    toF (symF C x m rho) =
      (∑ q ∈ Finset.range C.r, toF (point C.a x) ^ q * toF (rho.getD q 0)) +
        ∑ j ∈ Finset.range C.l, toF (point C.a x) ^ (C.r + j) * toF (m.getD j 0) := by
  unfold symF
  rw [toF_hornerF, List.length_append, length_fitL, length_fitL, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < C.r := Finset.mem_range.1 hq
    rw [List.getD_append _ _ _ _ (by rw [length_fitL]; exact hq'), getD_fitL _ _ _ _ hq']
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < C.l := Finset.mem_range.1 hj
    rw [List.getD_append_right _ _ _ _ (by rw [length_fitL]; exact Nat.le_add_right _ _),
      length_fitL, Nat.add_sub_cancel_left, getD_fitL _ _ _ _ hj']

/-- A symbol over the extension field. -/
theorem toE_symE (C : Code) (x : ℕ) (m rho : List E) :
    toE (symE C x m rho) =
      (∑ q ∈ Finset.range C.r, algebraMap GF GE (toF (point C.a x) ^ q) * lst rho q) +
        ∑ j ∈ Finset.range C.l, algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) * lst m j := by
  unfold symE
  rw [toE_hornerE, List.length_append, length_fitL, length_fitL, Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun q hq => ?_
    have hq' : q < C.r := Finset.mem_range.1 hq
    rw [lst_append, length_fitL, if_pos hq']
    unfold lst
    rw [getD_fitL _ _ _ _ hq']
  · refine Finset.sum_congr rfl fun j hj => ?_
    have hj' : j < C.l := Finset.mem_range.1 hj
    rw [lst_append, length_fitL, if_neg (Nat.not_lt.2 (Nat.le_add_right _ _)),
      Nat.add_sub_cancel_left]
    unfold lst
    rw [getD_fitL _ _ _ _ hj']

/-- A symbol over the extension field is the library's encoder at the code's own positions. -/
theorem toE_symE_enc (C : Code) (x : Fin (2 ^ C.a)) (m rho : List E) :
    toE (symE C x.val m rho) =
      (ldOf C C.a).enc (fun j => lst m j.val) (fun q => lst rho q.val) x () := by
  rw [toE_symE, Finset.sum_range, Finset.sum_range]
  rfl

/-- The same on arrays. -/
theorem toE_encE (C : Code) (m rho : Array E) (x : Fin (2 ^ C.a)) :
    toE (encE C m rho x.val) =
      (ldOf C C.a).enc (fun j => vec m j.val) (fun q => vec rho q.val) x () := by
  have h := toE_symE_enc C x m.toList rho.toList
  simp only [← vec_eq_lst] at h
  exact h

end OnBytes.Slice

#print axioms OnBytes.Slice.eqW_def
#print axioms OnBytes.Slice.toE_mulEF
#print axioms OnBytes.Slice.lst_nil
#print axioms OnBytes.Slice.lst_cons_zero
#print axioms OnBytes.Slice.lst_cons_succ
#print axioms OnBytes.Slice.vec_toArray
#print axioms OnBytes.Slice.vec_eq_lst
#print axioms OnBytes.Slice.lst_of_le
#print axioms OnBytes.Slice.vec_of_le
#print axioms OnBytes.Slice.lst_append
#print axioms OnBytes.Slice.lst_take
#print axioms OnBytes.Slice.lst_map_mul
#print axioms OnBytes.Slice.lst_replicate_zero
#print axioms OnBytes.Slice.eqW_zero
#print axioms OnBytes.Slice.eqW_succ
#print axioms OnBytes.Slice.eqW_succ'
#print axioms OnBytes.Slice.eqW_congr
#print axioms OnBytes.Slice.eqW_mod
#print axioms OnBytes.Slice.length_eqStep
#print axioms OnBytes.Slice.length_eqFold
#print axioms OnBytes.Slice.lst_eqStep
#print axioms OnBytes.Slice.lst_eqFold
#print axioms OnBytes.Slice.size_pv
#print axioms OnBytes.Slice.vec_pv
#print axioms OnBytes.Slice.size_eqTab
#print axioms OnBytes.Slice.vec_eqTab
#print axioms OnBytes.Slice.toE_eqAtLoop
#print axioms OnBytes.Slice.toE_eqAt
#print axioms OnBytes.Slice.toE_dotL
#print axioms OnBytes.Slice.toE_dot
#print axioms OnBytes.Slice.toE_dot_of_le
#print axioms OnBytes.Slice.length_padL
#print axioms OnBytes.Slice.lst_padL
#print axioms OnBytes.Slice.lst_zipAdd
#print axioms OnBytes.Slice.size_addV
#print axioms OnBytes.Slice.vec_addV
#print axioms OnBytes.Slice.size_scaleV
#print axioms OnBytes.Slice.vec_scaleV
#print axioms OnBytes.Slice.size_axpy
#print axioms OnBytes.Slice.vec_axpy
#print axioms OnBytes.Slice.powsL_acc
#print axioms OnBytes.Slice.powsL_succ
#print axioms OnBytes.Slice.length_powsL
#print axioms OnBytes.Slice.lst_powsL
#print axioms OnBytes.Slice.size_powsE
#print axioms OnBytes.Slice.vec_powsE
#print axioms OnBytes.Slice.fold1A_acc
#print axioms OnBytes.Slice.fold1L_cons_cons
#print axioms OnBytes.Slice.length_fold1L
#print axioms OnBytes.Slice.lst_fold1L
#print axioms OnBytes.Slice.sum_range_two_mul
#print axioms OnBytes.Slice.length_foldL
#print axioms OnBytes.Slice.lst_foldL
#print axioms OnBytes.Slice.size_foldLow
#print axioms OnBytes.Slice.vec_foldLow
#print axioms OnBytes.Slice.toE_foldV
#print axioms OnBytes.Slice.eqW_rowNo
#print axioms OnBytes.Slice.sum_range_cube
#print axioms OnBytes.Slice.eqW_lst
#print axioms OnBytes.Slice.sumRows_eq
#print axioms OnBytes.Slice.rowLoop
#print axioms OnBytes.Slice.vec_sumRows_c
#print axioms OnBytes.Slice.vec_sumRows_d
#print axioms OnBytes.Slice.toE_sumRows_t
#print axioms OnBytes.Slice.rowLoop_size
#print axioms OnBytes.Slice.size_sumRows_c
#print axioms OnBytes.Slice.size_sumRows_d
#print axioms OnBytes.Slice.length_powers
#print axioms OnBytes.Slice.toF_powers
#print axioms OnBytes.Slice.length_genT
#print axioms OnBytes.Slice.length_genM
#print axioms OnBytes.Slice.toF_genT
#print axioms OnBytes.Slice.toF_genM
#print axioms OnBytes.Slice.lst_map_ofF
#print axioms OnBytes.Slice.vec_genTE
#print axioms OnBytes.Slice.vec_genME
#print axioms OnBytes.Slice.genOf_castAdd
#print axioms OnBytes.Slice.genOf_natAdd
#print axioms OnBytes.Slice.length_fitL
#print axioms OnBytes.Slice.getD_fitL
#print axioms OnBytes.Slice.toF_hornerF
#print axioms OnBytes.Slice.toE_hornerE
#print axioms OnBytes.Slice.toF_symF
#print axioms OnBytes.Slice.toE_symE
#print axioms OnBytes.Slice.toE_symE_enc
#print axioms OnBytes.Slice.toE_encE
