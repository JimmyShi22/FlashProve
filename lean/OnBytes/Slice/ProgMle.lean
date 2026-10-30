-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ProgMle.lean: the program's weights of a point on the cube, read in the field.

OnBytes/Field/Mle.lean holds the program's routines on multilinear polynomials. This file reads
those that give the weights of a point, and the value of a polynomial in one variable, in the field
`GE` (the cubic extension field, `Cb.Gl.E` of Cb/Gl/GlField.lean). Elements of the program are read
by `readE`, `readV` and `readL` (OnBytes/Slice/ProgField.lean). The closed forms are those of
OnBytes/Slice/SimBasic.lean: `eqW n z i` is the library's weight `Alg.eqk` (Alg/Mle.lean) at the
point with the coordinates z 0 to z (n - 1) and at the vertex of the n lowest binary digits of i.

Main theorems: `readE_eqWeight`, `readE_eqIndex`, `size_eqTable`, `readV_eqTable`,
`readE_eqEval`, `readE_polyEval`.

Not claimed. Nothing on the other routines of OnBytes/Field/Mle.lean (folds of a vector, products of
factors as multilinear polynomials).
-/
import OnBytes.Field.Mle
import OnBytes.Slice.ProgCodes

set_option autoImplicit false

namespace OnBytes.Slice

/-! ## Lists of elements -/

/-- Two lists, one after the other. -/
theorem readL_append (A B : List E) (i : ℕ) :
    readL (A ++ B) i = if i < A.length then readL A i else readL B (i - A.length) := by
  rw [readL_eq_lst, List.map_append, lst_append, List.length_map, ← readL_eq_lst, ← readL_eq_lst]

/-- The first n entries of a list are read as the list's own. -/
theorem readL_take (n : ℕ) (l : List E) (t : ℕ) (ht : t < n) : readL (l.take n) t = readL l t := by
  unfold readL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt ht]

/-- A list without its first n entries. -/
theorem readL_drop (n : ℕ) (l : List E) (t : ℕ) : readL (l.drop n) t = readL l (n + t) := by
  unfold readL
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_drop]

/-- A list of zeros is read as 0 everywhere. -/
theorem readL_replicate_zero : ∀ n i : ℕ, readL (List.replicate n zeroE) i = 0
  | 0, i => readL_nil i
  | _ + 1, 0 => readE_zero
  | n + 1, i + 1 => readL_replicate_zero n i

/-- A running product over the numbers below m. -/
theorem readE_foldl_range (a : ℕ → E) (r : E) : ∀ m : ℕ,
    readE ((List.range m).foldl (fun s i => mulE s (a i)) r) =
      readE r * ∏ i ∈ Finset.range m, readE (a i)
  | 0 => by
      rw [List.range_zero, List.foldl_nil, Finset.prod_range_zero, mul_one]
  | m + 1 => by
      rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, readE_mul,
        readE_foldl_range a r m, Finset.prod_range_succ, mul_assoc]

/-- A list of which every entry is multiplied by x from the right. -/
theorem readL_map_mulR (x : E) : ∀ (T : List E) (i : ℕ),
    readL (T.map fun w => mulE w x) i = readL T i * readE x
  | [], i => by
      rw [List.map_nil, readL_nil, zero_mul]
  | a :: T, 0 => by
      rw [List.map_cons, readL_cons_zero, readL_cons_zero]
      exact readE_mul a x
  | a :: T, i + 1 => by
      rw [List.map_cons, readL_cons_succ, readL_cons_succ]
      exact readL_map_mulR x T i

/-- The difference of two lists of one length, entry by entry. -/
theorem readL_zipSub : ∀ (A B : List E) (i : ℕ), A.length = B.length →
    readL (List.zipWith subE A B) i = readL A i - readL B i
  | [], [], i, _ => by
      rw [List.zipWith_nil_left, readL_nil, sub_zero]
  | a :: A, b :: B, 0, _ => by
      rw [List.zipWith_cons_cons, readL_cons_zero, readL_cons_zero, readL_cons_zero]
      exact readE_sub a b
  | a :: A, b :: B, i + 1, h => by
      rw [List.zipWith_cons_cons, readL_cons_succ, readL_cons_succ, readL_cons_succ]
      exact readL_zipSub A B i (Nat.succ.inj h)

/-! ## The weight of one vertex -/

/-- One step of the loop of the weight, as an equation between functions of the index and the
running value. -/
theorem eqWeight_cons_fun (x : E) (xs : List E) :
    eqWeight (x :: xs) = fun j r =>
      eqWeight xs (j / 2) (mulE r (if j % 2 == 1 then x else subE oneE x)) := rfl

/-- The loop of the weight, from any running value. -/
theorem readE_eqWeight : ∀ (z : List E) (j : ℕ) (r : E),
    readE (eqWeight z j r) = readE r * eqW z.length (readL z) j
  | [], j, r => by
      rw [List.length_nil, eqW_zero, mul_one]
      rfl
  | x :: z, j, r => by
      have hz : (fun t => readL (x :: z) (t + 1)) = readL z := rfl
      rw [congrFun (congrFun (eqWeight_cons_fun x z) j) r, readE_eqWeight z, readE_mul,
        List.length_cons, eqW_succ', hz, readL_cons_zero, Nat.testBit_zero, mul_assoc]
      by_cases hj : j % 2 = 1
      · rw [if_pos (beq_iff_eq.2 hj), decide_eq_true hj, if_pos rfl]
      · rw [if_neg (fun hb => hj (beq_iff_eq.1 hb)), decide_eq_false hj, readE_sub, readE_one]
        rfl

/-- The weight that the point z gives to the vertex of the lowest digits of j, for every j. -/
theorem readE_eqIndex (z : List E) (j : ℕ) :
    readE (eqIndex z j) = eqW z.length (readL z) j := by
  unfold eqIndex
  rw [readE_eqWeight, readE_one, one_mul]

/-! ## The table of all weights -/

/-- One step of the program's table, on lists: the old table minus its product with x, then that
product. -/
def tabStep (T : List E) (x : E) : List E :=
  List.zipWith subE T (T.map fun w => mulE w x) ++ T.map fun w => mulE w x

/-- A step of the table's loop doubles its length. -/
theorem length_tabStep (T : List E) (x : E) : (tabStep T x).length = 2 * T.length := by
  unfold tabStep
  rw [List.length_append, List.length_zipWith, List.length_map, Nat.min_self, Nat.two_mul]

/-- One step of the program's table: the old table under 1 - x, then under x. -/
theorem readL_tabStep (T : List E) (x : E) (i : ℕ) :
    readL (tabStep T x) i =
      if i < T.length then (1 - readE x) * readL T i else readE x * readL T (i - T.length) := by
  unfold tabStep
  rw [readL_append, List.length_zipWith, List.length_map, Nat.min_self,
    readL_zipSub _ _ _ (List.length_map _).symm, readL_map_mulR, readL_map_mulR]
  by_cases h : i < T.length
  · rw [if_pos h, if_pos h]
    ring
  · rw [if_neg h, if_neg h, mul_comm]

/-- The program's table and the format's table at the triples are read alike. -/
theorem readL_tabFold (s : E) (z : List E) :
    (z.foldl tabStep [s]).length =
        ((z.map E.triple).foldl (Fmt.M1.eqStep .two) [s.triple]).length ∧
      ∀ i, readL (z.foldl tabStep [s]) i =
        lst ((z.map E.triple).foldl (Fmt.M1.eqStep .two) [s.triple]) i := by
  induction z using List.reverseRecOn with
  | nil =>
    rw [List.map_nil, List.foldl_nil, List.foldl_nil]
    exact ⟨rfl, fun i => readL_eq_lst [s] i⟩
  | append_singleton z w ih =>
    obtain ⟨hl, he⟩ := ih
    rw [List.map_append, List.map_cons, List.map_nil, List.foldl_append, List.foldl_append,
      List.foldl_cons, List.foldl_cons, List.foldl_nil, List.foldl_nil]
    refine ⟨by rw [length_tabStep, length_eqStep, hl], fun i => ?_⟩
    rw [readL_tabStep, lst_eqStep, hl, he, he, readE_def]

/-- The program's loop on arrays is the loop on lists. -/
theorem toList_tabFold : ∀ (z : List E) (a : Array E),
    (z.foldl (fun (out : Array E) x =>
      (Array.zipWith subE out (out.map fun w => mulE w x)) ++ out.map fun w => mulE w x) a).toList =
      z.foldl tabStep a.toList
  | [], _ => rfl
  | x :: z, a => by
      rw [List.foldl_cons, List.foldl_cons, toList_tabFold z]
      unfold tabStep
      rw [Array.toList_append, Array.toList_zipWith, Array.toList_map]

/-- The table of weights has one entry for each vertex. -/
theorem size_eqTable (z : List E) : (eqTable z).size = 2 ^ z.length := by
  have h : (eqTable z).toList = z.foldl tabStep [oneE] := toList_tabFold z #[oneE]
  rw [← Array.length_toList, h, (readL_tabFold oneE z).1, length_eqFold, List.length_singleton,
    Nat.one_mul, List.length_map]

/-- Entry i of the program's table is the weight of the vertex i at the point z; 0 beyond the
table's end. -/
theorem readV_eqTable (z : List E) (i : ℕ) :
    readV (eqTable z) i = if i < 2 ^ z.length then eqW z.length (readL z) i else 0 := by
  have h : (eqTable z).toList = z.foldl tabStep [oneE] := toList_tabFold z #[oneE]
  have hp : lst (z.map E.triple) = readL z := funext fun t => (readL_eq_lst z t).symm
  rw [readV_eq_readL, h, (readL_tabFold oneE z).2, lst_eqFold, List.length_map, hp, ← readE_def,
    readE_one, one_mul]

/-! ## The equality polynomial of two points -/

/-- One step of the loop of the equality polynomial, as an equation between functions of the
running value. -/
theorem eqEvalFrom_cons_fun (a b : E) (as bs : List E) :
    eqEvalFrom (a :: as) (b :: bs) = fun r =>
      eqEvalFrom as bs
        (mulE r (subE (subE (addE (addE (mulE a b) (mulE a b)) oneE) a) b)) := rfl

/-- The loop of the equality polynomial, from any running value. -/
theorem readE_eqEvalFrom : ∀ (a b : List E) (r : E),
    readE (eqEvalFrom a b r) =
      readE r * ∏ t ∈ Finset.range (min a.length b.length), Alg.eq1 (readL a t) (readL b t)
  | [], b, r => by
      rw [List.length_nil, Nat.zero_min, Finset.prod_range_zero, mul_one]
      rfl
  | a :: as, [], r => by
      rw [List.length_nil, Nat.min_zero, Finset.prod_range_zero, mul_one]
      rfl
  | a :: as, b :: bs, r => by
      rw [congrFun (eqEvalFrom_cons_fun a b as bs) r, readE_eqEvalFrom as bs, readE_mul, readE_sub,
        readE_sub, readE_add, readE_add, readE_mul, readE_one, List.length_cons, List.length_cons,
        Nat.succ_min_succ, Finset.prod_range_succ']
      simp only [readL_cons_succ, readL_cons_zero, Alg.eq1]
      ring

/-- The equality polynomial of two points: the product of a b + (1 - a) (1 - b) over the
coordinates, as far as the shorter point goes. -/
theorem readE_eqEval (a b : List E) :
    readE (eqEval a b) =
      ∏ t ∈ Finset.range (min a.length b.length), Alg.eq1 (readL a t) (readL b t) := by
  unfold eqEval
  rw [readE_eqEvalFrom, readE_one, one_mul]

/-! ## A polynomial in one variable -/

/-- The loop of Horner's rule over the coefficients, the highest first. -/
theorem readE_polyLoop (x : E) : ∀ (c : List E) (r : E),
    readE (c.foldl (fun r a => maddE a r x) r) =
      readE r * readE x ^ c.length + ∑ k ∈ Finset.range c.length, readL c.reverse k * readE x ^ k
  | [], r => by
      rw [List.foldl_nil, List.length_nil, pow_zero, mul_one, Finset.sum_range_zero, add_zero]
  | a :: c, r => by
      have hlast : readL (a :: c).reverse c.length = readE a := by
        rw [List.reverse_cons, readL_append, List.length_reverse, if_neg (Nat.lt_irrefl _),
          Nat.sub_self]
        rfl
      have hlow : ∀ k ∈ Finset.range c.length, readL (a :: c).reverse k * readE x ^ k =
          readL c.reverse k * readE x ^ k := fun k hk => by
        rw [List.reverse_cons, readL_append, List.length_reverse, if_pos (Finset.mem_range.1 hk)]
      rw [List.foldl_cons, readE_polyLoop x c, readE_maddE, List.length_cons,
        Finset.sum_range_succ, hlast, Finset.sum_congr rfl hlow]
      ring

/-- The value at x of the polynomial with the coefficients c, the constant one first. -/
theorem readE_polyEval (c : List E) (x : E) :
    readE (polyEval c x) = ∑ k ∈ Finset.range c.length, readL c k * readE x ^ k := by
  unfold polyEval
  rw [readE_polyLoop, readE_zero, zero_mul, zero_add, List.length_reverse, List.reverse_reverse]

end OnBytes.Slice

#print axioms OnBytes.Slice.readL_append
#print axioms OnBytes.Slice.readL_take
#print axioms OnBytes.Slice.readL_drop
#print axioms OnBytes.Slice.readL_replicate_zero
#print axioms OnBytes.Slice.readE_foldl_range
#print axioms OnBytes.Slice.readL_map_mulR
#print axioms OnBytes.Slice.readL_zipSub
#print axioms OnBytes.Slice.eqWeight_cons_fun
#print axioms OnBytes.Slice.readE_eqWeight
#print axioms OnBytes.Slice.readE_eqIndex
#print axioms OnBytes.Slice.length_tabStep
#print axioms OnBytes.Slice.readL_tabStep
#print axioms OnBytes.Slice.readL_tabFold
#print axioms OnBytes.Slice.toList_tabFold
#print axioms OnBytes.Slice.size_eqTable
#print axioms OnBytes.Slice.readV_eqTable
#print axioms OnBytes.Slice.eqEvalFrom_cons_fun
#print axioms OnBytes.Slice.readE_eqEvalFrom
#print axioms OnBytes.Slice.readE_eqEval
#print axioms OnBytes.Slice.readE_polyLoop
#print axioms OnBytes.Slice.readE_polyEval
