-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/ProgCodes.lean: the program's points, generator rows and symbols, read in the field.

The program has its own routines for a code (OnBytes/Iop/Ground.lean): `codePoint`,
`generatorMessage`, `generatorTail` and `symbolAt`, and its own inner product
(OnBytes/Iop/Fold.lean: `inner`). They are written for speed: a point is made with 32 squarings, a
power of the point is a product of repeated squares, and a symbol goes by Horner's rule on single
words. This file reads their results in the fields `GF` and `GE` and gives them in the closed forms
that OnBytes/Slice/SimBasic.lean and SimBase.lean give for the format's own routines: the point is
the format's point, a generator row holds the powers of the point, and a symbol is the library's
encoder.

Elements of the program are read by `readE`, `readV` and `readL` (OnBytes/Slice/ProgField.lean).
`readL_eq_lst` and `readV_eq_vec` lead from these to the readings `lst` and `vec` of triples of
words, in which the format's side is stated.

Main definitions: `codeOf` (the program's record of a code as the format's), `lstF`.
Main theorems: `readL_eq_lst`, `readV_eq_vec`, `le_two_pow_ceilLog2`, `ceilLog2_two_pow`,
`toF_productIndex_squares`, `lstF_productTable`, `toF_codePoint`, `size_generatorTail`,
`size_generatorMessage`, `toF_generatorTail`, `toF_generatorMessage`, `readE_hornerFrom`,
`readE_symbolAt_pt`, `readE_symbolAt`, `readE_symbolAt_enc`, `readE_inner`.

Not claimed. Nothing on codes of more than 2^32 positions, whose points are on several cosets: there
only the statements at the program's own point hold (`toF_generatorTail`, `toF_generatorMessage`,
`readE_symbolAt_pt`). Nothing on a block of the program.
-/
import OnBytes.Iop.Fold
import OnBytes.Slice.ProgField
import OnBytes.Slice.Points
import OnBytes.Slice.SimBase

set_option autoImplicit false

namespace OnBytes.Slice

/-- The program's record of a code as the format's. -/
def codeOf (c : OnBytes.Code) : Fmt.M1.Code := ⟨c.logN, c.ell, c.r⟩

/-- Entry i of a list of words, read in the base field; 0 beyond the end. -/
def lstF (l : List F) (i : ℕ) : GF := toF (l.getD i 0)

/-! ## From the program's elements to triples of words -/

/-- A list of elements of the program is read as the list of their triples. -/
theorem readL_eq_lst : ∀ (l : List E) (i : ℕ), readL l i = lst (l.map E.triple) i
  | [], i => by
      rw [List.map_nil, readL_nil, lst_nil]
  | a :: l, 0 => by
      rw [List.map_cons, readL_cons_zero, lst_cons_zero, readE_def]
  | a :: l, i + 1 => by
      rw [List.map_cons, readL_cons_succ, lst_cons_succ]
      exact readL_eq_lst l i

/-- An array of elements of the program is read as the array of their triples. -/
theorem readV_eq_vec (v : Array E) (i : ℕ) : readV v i = vec (v.map E.triple) i := by
  rw [readV_eq_readL, readL_eq_lst, vec_eq_lst, Array.toList_map]

/-- A list of elements of the program as a point is the point of the list of their triples. -/
theorem readP_eq_ptL (n : ℕ) (l : List E) : readP n l = ptL n (l.map E.triple) :=
  funext fun i => readL_eq_lst l i.val

/-- The weight at a list's point, with the point as a function on `Fin n`. -/
theorem eqW_readL (n : ℕ) (l : List E) (i : ℕ) :
    eqW n (readL l) i = Alg.eqk (readP n l) (fun t : Fin n => i.testBit t.val) := rfl

/-! ## Lists and arrays of words -/

/-- The empty list is read as 0 at every place. -/
theorem lstF_nil (i : ℕ) : lstF [] i = 0 := toF_zero

/-- The first word of a list. -/
theorem lstF_cons_zero (a : F) (l : List F) : lstF (a :: l) 0 = toF a := rfl

/-- A later word of a list. -/
theorem lstF_cons_succ (a : F) (l : List F) (i : ℕ) : lstF (a :: l) (i + 1) = lstF l i := rfl

/-- A word that a list does not have is read as 0. -/
theorem lstF_of_le (l : List F) (i : ℕ) (h : l.length ≤ i) : lstF l i = 0 := by
  unfold lstF
  rw [List.getD_eq_default _ _ h]
  exact toF_zero

/-- An array of words is read as its list. -/
theorem toF_getD (a : Array F) (i : ℕ) : toF (a.getD i 0) = lstF a.toList i := by
  unfold lstF
  rw [Array.getD_eq_getD_getElem?, List.getD_eq_getElem?_getD, Array.getElem?_toList]

/-- Two lists, one after the other. -/
theorem lstF_append : ∀ (A B : List F) (i : ℕ),
    lstF (A ++ B) i = if i < A.length then lstF A i else lstF B (i - A.length)
  | [], _, _ => rfl
  | _ :: _, _, 0 => rfl
  | a :: A, B, i + 1 => by
      have hsub : i + 1 - (a :: A).length = i - A.length := Nat.succ_sub_succ _ _
      rw [hsub]
      exact (lstF_append A B i).trans (if_congr Nat.succ_lt_succ_iff.symm rfl rfl)

/-- A list of which every entry is multiplied by x. -/
theorem lstF_map_mul (x : F) : ∀ (l : List F) (i : ℕ),
    lstF (l.map (mulF · x)) i = lstF l i * toF x
  | [], i => by
      rw [List.map_nil, lstF_nil, zero_mul]
  | a :: l, 0 => by
      rw [List.map_cons, lstF_cons_zero, lstF_cons_zero]
      exact toF_mulF a x
  | a :: l, i + 1 => by
      rw [List.map_cons, lstF_cons_succ, lstF_cons_succ]
      exact lstF_map_mul x l i

/-- The first n entries of a list are read as the list's own. -/
theorem lstF_take (n : ℕ) (l : List F) (i : ℕ) (hi : i < n) : lstF (l.take n) i = lstF l i := by
  unfold lstF
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hi]

/-! ## Logarithms -/

/-- The program's rounded-up logarithm, written out. -/
theorem ceilLog2_eq (n : ℕ) : ceilLog2 n = if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1 := rfl

/-- The rounded-up logarithm is large enough. -/
theorem le_two_pow_ceilLog2 (n : ℕ) : n ≤ 2 ^ ceilLog2 n := by
  rw [ceilLog2_eq]
  by_cases h : n ≤ 1
  · rw [if_pos h, pow_zero]
    exact h
  · rw [if_neg h]
    have hlt : n - 1 < 2 ^ ((n - 1).log2 + 1) := Nat.lt_log2_self
    omega

/-- The rounded-up logarithm is at most every exponent that is large enough. -/
theorem ceilLog2_le (n k : ℕ) (h : n ≤ 2 ^ k) : ceilLog2 n ≤ k := by
  rw [ceilLog2_eq]
  by_cases h1 : n ≤ 1
  · rw [if_pos h1]
    exact Nat.zero_le k
  · rw [if_neg h1]
    have h2 : Nat.log2 (n - 1) < k := (Nat.log2_lt (by omega)).2 (by omega)
    omega

/-- The rounded-up logarithm of a power of two is the exponent. -/
theorem ceilLog2_two_pow (k : ℕ) : ceilLog2 (2 ^ k) = k :=
  Nat.le_antisymm (ceilLog2_le _ _ (Nat.le_refl _))
    ((Nat.pow_le_pow_iff_right Nat.one_lt_two).1 (le_two_pow_ceilLog2 (2 ^ k)))

/-- The program's and the format's rounded-up logarithm are one function. -/
theorem ceilLog2_eq_clog (n : ℕ) : ceilLog2 n = Fmt.M2.clog n := rfl

/-! ## Repeated squares and their products -/

/-- No repeated square: the empty list. -/
theorem squaresOf_zero (z : F) : squaresOf 0 z = [] := rfl

/-- One more repeated square: the word itself, then the squares of its square. -/
theorem squaresOf_succ (n : ℕ) (z : F) : squaresOf (n + 1) z = z :: squaresOf n (mulF z z) := rfl

/-- There are as many repeated squares as were asked for. -/
theorem length_squaresOf : ∀ (n : ℕ) (z : F), (squaresOf n z).length = n
  | 0, z => by
      rw [squaresOf_zero, List.length_nil]
  | n + 1, z => by
      rw [squaresOf_succ, List.length_cons, length_squaresOf n]

/-- Entry i of the repeated squares of z is z to the power 2^i. -/
theorem lstF_squaresOf : ∀ (n : ℕ) (z : F) (i : ℕ),
    lstF (squaresOf n z) i = if i < n then toF z ^ 2 ^ i else 0
  | 0, z, i => by
      rw [squaresOf_zero, if_neg (Nat.not_lt_zero i), lstF_nil]
  | n + 1, z, 0 => by
      rw [squaresOf_succ, lstF_cons_zero, if_pos (Nat.succ_pos n), pow_zero, pow_one]
  | n + 1, z, i + 1 => by
      rw [squaresOf_succ, lstF_cons_succ, lstF_squaresOf n, toF_mulF, ← pow_two, ← pow_mul,
        ← pow_succ']
      exact if_congr Nat.succ_lt_succ_iff.symm rfl rfl

/-- The first k of n repeated squares are the repeated squares up to the smaller number. -/
theorem take_squaresOf : ∀ (k n : ℕ) (z : F), (squaresOf n z).take k = squaresOf (min k n) z
  | 0, n, z => by
      rw [List.take_zero, Nat.zero_min, squaresOf_zero]
  | k + 1, 0, z => by
      rw [Nat.min_zero, squaresOf_zero, List.take_nil]
  | k + 1, n + 1, z => by
      rw [squaresOf_succ, List.take_succ_cons, take_squaresOf k n, Nat.succ_min_succ,
        squaresOf_succ]

/-- The product of no factor is 1. -/
theorem productIndex_nil (j : ℕ) : productIndex [] j = 1 := rfl

/-- The first factor counts if the number is odd; the others go by its half. -/
theorem productIndex_cons (x : F) (f : List F) (j : ℕ) :
    productIndex (x :: f) j =
      if j % 2 == 1 then mulF x (productIndex f (j / 2)) else productIndex f (j / 2) := rfl

/-- One factor taken off the product. -/
theorem toF_productIndex_cons (x : F) (f : List F) (j : ℕ) :
    toF (productIndex (x :: f) j) =
      (if j % 2 = 1 then toF x else 1) * toF (productIndex f (j / 2)) := by
  rw [productIndex_cons]
  by_cases hj : j % 2 = 1
  · rw [if_pos (beq_iff_eq.2 hj), if_pos hj, toF_mulF]
  · rw [if_neg (fun hb => hj (beq_iff_eq.1 hb)), if_neg hj, one_mul]

/-- The product of no factor. -/
theorem toF_productIndex_zero : ∀ f : List F, toF (productIndex f 0) = 1
  | [] => by
      rw [productIndex_nil, toF_one]
  | x :: f => by
      have h0 : ¬ 0 % 2 = 1 := by decide
      rw [toF_productIndex_cons, if_neg h0, one_mul, Nat.zero_div, toF_productIndex_zero f]

/-- The product of the repeated squares of z at the set bits of j is a power of z. -/
theorem toF_productIndex_squares : ∀ (n : ℕ) (z : F) (j : ℕ),
    toF (productIndex (squaresOf n z) j) = toF z ^ (j % 2 ^ n)
  | 0, z, j => by
      rw [squaresOf_zero, productIndex_nil, toF_one, pow_zero, Nat.mod_one, pow_zero]
  | n + 1, z, j => by
      have split : j % 2 ^ (n + 1) = j % 2 + 2 * (j / 2 % 2 ^ n) := by
        rw [pow_succ', Nat.mod_mul]
      rw [squaresOf_succ, toF_productIndex_cons, toF_productIndex_squares n, toF_mulF, split,
        pow_add, pow_mul, pow_two]
      by_cases hj : j % 2 = 1
      · rw [if_pos hj, hj, pow_one]
      · have h0 : j % 2 = 0 := by omega
        rw [if_neg hj, h0, pow_zero]

/-- One step of the loop of `productTable`. -/
def tableStep (n : ℕ) (a : Array F) (x : F) : Array F :=
  if a.size < n then a ++ a.map (mulF · x) else a

/-- A step of the loop while the table is too short: each entry times the factor is appended. -/
theorem tableStep_pos (n : ℕ) (a : Array F) (x : F) (h : a.size < n) :
    tableStep n a x = a ++ a.map (mulF · x) := if_pos h

/-- A step of the loop when the table is long enough: nothing changes. -/
theorem tableStep_neg (n : ℕ) (a : Array F) (x : F) (h : ¬ a.size < n) : tableStep n a x = a :=
  if_neg h

/-- The loop of `productTable` never makes the table shorter, and it goes on until the table has n
entries or the factors end. -/
theorem size_tableFold (n : ℕ) : ∀ (f : List F) (a : Array F), n ≤ a.size * 2 ^ f.length →
    n ≤ (f.foldl (tableStep n) a).size
  | [], a, h => by
      rw [List.length_nil, pow_zero, Nat.mul_one] at h
      exact h
  | x :: f, a, h => by
      rw [List.foldl_cons]
      by_cases hs : a.size < n
      · rw [tableStep_pos n a x hs]
        refine size_tableFold n f _ ?_
        rw [Array.size_append, Array.size_map]
        rw [List.length_cons, pow_succ'] at h
        calc n ≤ a.size * (2 * 2 ^ f.length) := h
          _ = (a.size + a.size) * 2 ^ f.length := by ring
      · rw [tableStep_neg n a x hs]
        refine size_tableFold n f a ?_
        exact Nat.le_trans (Nat.le_of_not_lt hs) (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))

/-- An entry of the table that the loop of `productTable` makes from the table a. -/
theorem lstF_tableFold (n : ℕ) : ∀ (f : List F) (a : Array F) (j : ℕ), 0 < a.size → j < n →
    j < a.size * 2 ^ f.length →
    lstF (f.foldl (tableStep n) a).toList j =
      lstF a.toList (j % a.size) * toF (productIndex f (j / a.size))
  | [], a, j, _, _, hlt => by
      rw [List.length_nil, pow_zero, Nat.mul_one] at hlt
      rw [List.foldl_nil, Nat.mod_eq_of_lt hlt, productIndex_nil, toF_one, mul_one]
  | x :: f, a, j, ha, hj, hlt => by
      rw [List.foldl_cons]
      by_cases hs : a.size < n
      · have hsz : (a ++ a.map (mulF · x)).size = 2 * a.size := by
          rw [Array.size_append, Array.size_map, Nat.two_mul]
        have hlt' : j < (a ++ a.map (mulF · x)).size * 2 ^ f.length := by
          rw [List.length_cons, pow_succ'] at hlt
          rw [hsz]
          calc j < a.size * (2 * 2 ^ f.length) := hlt
            _ = 2 * a.size * 2 ^ f.length := by ring
        have hpos : 0 < (a ++ a.map (mulF · x)).size := by
          rw [hsz]
          omega
        have hmm : j % (2 * a.size) % a.size = j % a.size :=
          Nat.mod_mod_of_dvd j (Dvd.intro_left 2 rfl)
        have hdd : j / a.size / 2 = j / (2 * a.size) := by
          rw [Nat.div_div_eq_div_mul, Nat.mul_comm]
        have hsplit : j % (2 * a.size) = j % a.size + a.size * (j / a.size % 2) := by
          rw [Nat.mul_comm 2, Nat.mod_mul]
        have hr : j % a.size < a.size := Nat.mod_lt _ ha
        rw [tableStep_pos n a x hs, lstF_tableFold n f _ j hpos hj hlt', hsz, Array.toList_append,
          Array.toList_map, lstF_append, Array.length_toList, lstF_map_mul, toF_productIndex_cons,
          hdd]
        by_cases hb : j / a.size % 2 = 1
        · have hge : ¬ j % (2 * a.size) < a.size := by
            rw [hsplit, hb]
            omega
          have hsub : j % (2 * a.size) - a.size = j % a.size := by
            rw [hsplit, hb]
            omega
          rw [if_neg hge, hsub, if_pos hb, mul_assoc]
        · have h0 : j / a.size % 2 = 0 := by omega
          have hlo : j % (2 * a.size) = j % a.size := by
            rw [hsplit, h0]
            omega
          rw [hlo, if_pos hr, if_neg hb, one_mul]
      · have hja : j < a.size := Nat.lt_of_lt_of_le hj (Nat.le_of_not_lt hs)
        have hlt' : j < a.size * 2 ^ f.length :=
          Nat.lt_of_lt_of_le hja (Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _))
        have hd : j / a.size = 0 := Nat.div_eq_of_lt hja
        rw [tableStep_neg n a x hs, lstF_tableFold n f a j ha hj hlt', hd, toF_productIndex_zero,
          toF_productIndex_zero]

/-- The table of products as a loop of `tableStep`, cut to its length. -/
theorem productTable_eq (f : List F) (n : ℕ) :
    productTable f n = (f.foldl (tableStep n) #[1]).extract 0 n := rfl

/-- The table of the first n products has n entries, if the factors can spell n indices. -/
theorem size_productTable (f : List F) (n : ℕ) (h : n ≤ 2 ^ f.length) :
    (productTable f n).size = n := by
  have hs : n ≤ (f.foldl (tableStep n) #[1]).size :=
    size_tableFold n f #[1] (by rw [List.size_toArray, List.length_singleton, Nat.one_mul]; exact h)
  rw [productTable_eq, Array.size_extract]
  omega

/-- Entry j of the table of products is the product at the index j. -/
theorem lstF_productTable (f : List F) (n j : ℕ) (h : n ≤ 2 ^ f.length) (hj : j < n) :
    lstF (productTable f n).toList j = toF (productIndex f j) := by
  have hone : (#[1] : Array F).size = 1 := rfl
  have h1 := lstF_tableFold n f #[1] j Nat.one_pos hj
    (by rw [hone, Nat.one_mul]; exact Nat.lt_of_lt_of_le hj h)
  rw [hone, Nat.mod_one, Nat.div_one] at h1
  have h0 : lstF (#[1] : Array F).toList 0 = 1 := toF_one
  rw [h0, one_mul] at h1
  rw [productTable_eq, Array.toList_extract, List.extract_eq_take_drop, List.drop_zero,
    Nat.sub_zero, lstF_take _ _ _ hj]
  exact h1

/-! ## Points -/

/-- The exponents of two runs of bits add up. -/
theorem expFrom_add (x n m i : ℕ) :
    expFrom x (n + m) i = expFrom x n i + expFrom x m (i + n) := by
  induction n generalizing i with
  | zero => simp [expFrom]
  | succ n ih =>
    rw [Nat.succ_add]
    show _ + expFrom x (n + m) (i + 1) = (_ + expFrom x n (i + 1)) + _
    rw [ih (i + 1), show i + 1 + n = i + (n + 1) by omega, Nat.add_assoc]

/-- Bits that are not set contribute nothing. -/
theorem expFrom_zero (x n i : ℕ) (h : ∀ j, i ≤ j → x.testBit j = false) : expFrom x n i = 0 := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
    show (if x.testBit i = true then _ else 0) + expFrom x n (i + 1) = 0
    rw [h i (Nat.le_refl i), ih (i + 1) fun j hj => h j (by omega)]
    rfl

/-- The state of the program's loop after its first n steps. -/
theorem codePoint_loop (s x : ℕ) (start : UInt64) (hx : ∀ j, s ≤ j → x.testBit j = false) (n : ℕ)
    (hn : n ≤ 32) :
    toF ((List.range n).foldl (fun (zr : UInt64 × UInt64) j =>
        (if 31 - j < s && x.testBit (31 - j) then OnBytes.mulF zr.1 zr.2 else zr.1,
          OnBytes.mulF zr.2 zr.2)) (start, OnBytes.rootOfOrder32)).1 =
        toF start * rootW ^ expFrom x n (32 - n) ∧
      toF ((List.range n).foldl (fun (zr : UInt64 × UInt64) j =>
        (if 31 - j < s && x.testBit (31 - j) then OnBytes.mulF zr.1 zr.2 else zr.1,
          OnBytes.mulF zr.2 zr.2)) (start, OnBytes.rootOfOrder32)).2 = rootW ^ 2 ^ n := by
  induction n with
  | zero =>
    refine ⟨?_, ?_⟩
    · show toF start = toF start * rootW ^ 0
      rw [pow_zero, mul_one]
    · show toF OnBytes.rootOfOrder32 = rootW ^ 2 ^ 0
      rw [pow_zero, pow_one]
      rfl
  | succ n ih =>
    obtain ⟨h1, h2⟩ := ih (by omega)
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    refine ⟨?_, ?_⟩
    · have e1 : 32 - (n + 1) = 31 - n := by omega
      have e2 : 31 - n + 1 = 32 - n := by omega
      rw [e1]
      show _ = toF start * rootW ^ ((if x.testBit (31 - n) = true then 2 ^ (32 - (31 - n + 1))
        else 0) + expFrom x n (31 - n + 1))
      rw [e2, show 32 - (32 - n) = n by omega]
      by_cases hb : x.testBit (31 - n) = true
      · have hs : 31 - n < s := by
          by_contra hc
          rw [hx (31 - n) (by omega)] at hb
          cases hb
        rw [if_pos (by simp [hs, hb]), if_pos hb, toF_mulF, h1, h2, pow_add]
        ring
      · rw [if_neg (by simp [hb]), if_neg hb, h1, Nat.zero_add]
    · rw [toF_mulF, h2, ← pow_add, pow_succ 2 n]
      congr 1
      omega

/-- The program's point of a position is the format's, read in the field, for a code of at most
2^32 positions. -/
theorem toF_codePoint (a x : ℕ) (ha : a ≤ 32) (hx : x < 2 ^ a) :
    toF (OnBytes.codePoint a x) = toF (Fmt.M1.point a x) := by
  have hbits : ∀ j, a ≤ j → x.testBit j = false := fun j hj =>
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) hj))
  have hmin : min a 32 = a := Nat.min_eq_left ha
  have h := (codePoint_loop a x (OnBytes.powF 7 (1 + x / 2 ^ a)) hbits 32 (Nat.le_refl 32)).1
  unfold OnBytes.codePoint
  simp only [hmin]
  rw [h, toF_point, toF_powF, Nat.div_eq_of_lt hx, Nat.add_zero, pow_one, Nat.sub_self,
    show 32 = a + (32 - a) by omega, expFrom_add, Nat.zero_add,
    expFrom_zero x (32 - a) a hbits, Nat.add_zero]

/-! ## Generator rows -/

/-- A table of products of the first k of n repeated squares of z holds the powers of z. -/
theorem lstF_powerTable (k n : ℕ) (z : F) (m j : ℕ) (hk : m ≤ 2 ^ k) (hn : m ≤ 2 ^ n)
    (hj : j < m) :
    lstF (productTable ((squaresOf n z).take k) m).toList j = toF z ^ j := by
  have hm : m ≤ 2 ^ min k n := by
    rcases Nat.le_total k n with h | h
    · rw [Nat.min_eq_left h]
      exact hk
    · rw [Nat.min_eq_right h]
      exact hn
  rw [take_squaresOf, lstF_productTable _ _ _ (by rw [length_squaresOf]; exact hm) hj,
    toF_productIndex_squares, Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le hj hm)]

/-- The table of powers has the length that was asked for, if the factors can spell it. -/
theorem size_powerTable (k n : ℕ) (z : F) (m : ℕ) (hk : m ≤ 2 ^ k) (hn : m ≤ 2 ^ n) :
    (productTable ((squaresOf n z).take k) m).size = m := by
  have hm : m ≤ 2 ^ min k n := by
    rcases Nat.le_total k n with h | h
    · rw [Nat.min_eq_left h]
      exact hk
    · rw [Nat.min_eq_right h]
      exact hn
  rw [take_squaresOf, size_productTable _ _ (by rw [length_squaresOf]; exact hm)]

/-- The factors of a generator row can spell every coefficient's exponent. -/
theorem dim_le_logDim (c : OnBytes.Code) : c.ell + c.r ≤ 2 ^ c.logDim :=
  le_two_pow_ceilLog2 c.dim

/-- The tail has at most 2 ^ logDim entries. -/
theorem r_le_logDim (c : OnBytes.Code) : c.r ≤ 2 ^ c.logDim :=
  Nat.le_trans (Nat.le_add_left _ _) (dim_le_logDim c)

/-- The message has at most 2 ^ logDim entries. -/
theorem ell_le_logDim (c : OnBytes.Code) : c.ell ≤ 2 ^ c.logDim :=
  Nat.le_trans (Nat.le_add_right _ _) (dim_le_logDim c)

/-- The program's row on the tail, with its factors written out. -/
theorem generatorTail_eq (c : OnBytes.Code) (x : ℕ) :
    generatorTail c x = (productTable ((squaresOf c.logDim (codePoint c.logN x)).take
      (ceilLog2 c.r)) c.r).map (mulF · 1) := rfl

/-- The program's row on the message, with its factors written out. -/
theorem generatorMessage_eq (c : OnBytes.Code) (x : ℕ) :
    generatorMessage c x = (productTable ((squaresOf c.logDim (codePoint c.logN x)).take
      (ceilLog2 c.ell)) c.ell).map
        (mulF · (productIndex (squaresOf c.logDim (codePoint c.logN x)) c.r)) := rfl

/-- The factors of a generator row are the repeated squares of the point. -/
theorem generatorAt_f (c : OnBytes.Code) (x : ℕ) :
    (generatorAt c x).f = squaresOf c.logDim (codePoint c.logN x) := rfl

/-- The factor in front of the message's sum, as the program computes it. -/
theorem generatorAt_messageScale (c : OnBytes.Code) (x : ℕ) :
    (generatorAt c x).messageScale =
      productIndex (squaresOf c.logDim (codePoint c.logN x)) c.r := rfl

/-- The factor in front of the tail's sum is the word 1. -/
theorem generatorAt_tailScale (c : OnBytes.Code) (x : ℕ) : (generatorAt c x).tailScale = 1 := rfl

/-- The factor in front of the tail's sum is read as 1. -/
theorem toF_tailScale (c : OnBytes.Code) (x : ℕ) : toF (generatorAt c x).tailScale = 1 := by
  rw [generatorAt_tailScale, toF_one]

/-- The factor in front of the message's sum is the point to the power r, if the code has a message
entry at all. -/
theorem toF_messageScale (c : OnBytes.Code) (x : ℕ) (h : 0 < c.ell) :
    toF (generatorAt c x).messageScale = toF (codePoint c.logN x) ^ c.r := by
  have hr : c.r < 2 ^ c.logDim := by
    have hd := dim_le_logDim c
    omega
  rw [generatorAt_messageScale, toF_productIndex_squares, Nat.mod_eq_of_lt hr]

/-- The generator row on the tail has r entries. -/
theorem size_generatorTail (c : OnBytes.Code) (x : ℕ) : (generatorTail c x).size = c.r := by
  rw [generatorTail_eq, Array.size_map]
  exact size_powerTable _ _ _ _ (le_two_pow_ceilLog2 c.r) (r_le_logDim c)

/-- The generator row on the message has as many entries as the message. -/
theorem size_generatorMessage (c : OnBytes.Code) (x : ℕ) :
    (generatorMessage c x).size = c.ell := by
  rw [generatorMessage_eq, Array.size_map]
  exact size_powerTable _ _ _ _ (le_two_pow_ceilLog2 c.ell) (ell_le_logDim c)

/-- The program's generator row on the tail: the powers of the point from exponent 0 on. -/
theorem toF_generatorTail (c : OnBytes.Code) (x q : ℕ) (hq : q < c.r) :
    toF ((generatorTail c x).getD q 0) = toF (codePoint c.logN x) ^ q := by
  rw [generatorTail_eq, toF_getD, Array.toList_map, lstF_map_mul,
    lstF_powerTable _ _ _ _ _ (le_two_pow_ceilLog2 c.r) (r_le_logDim c) hq, toF_one, mul_one]

/-- The program's generator row on the message: the powers of the point from exponent r on. -/
theorem toF_generatorMessage (c : OnBytes.Code) (x j : ℕ) (hj : j < c.ell) :
    toF ((generatorMessage c x).getD j 0) = toF (codePoint c.logN x) ^ (c.r + j) := by
  have hr : c.r < 2 ^ c.logDim := by
    have hd := dim_le_logDim c
    omega
  rw [generatorMessage_eq, toF_getD, Array.toList_map, lstF_map_mul,
    lstF_powerTable _ _ _ _ _ (le_two_pow_ceilLog2 c.ell) (ell_le_logDim c) hj,
    toF_productIndex_squares, Nat.mod_eq_of_lt hr, pow_add, mul_comm]

/-! ## Symbols -/

/-- One step of Horner's rule in the field, coordinate by coordinate. -/
theorem cubic_hornerStep (u0 u1 u2 w : GF) (y : GE) :
    (⟨u0 * w + y.c0, u1 * w + y.c1, u2 * w + y.c2⟩ : GE) =
      algebraMap GF GE w * ⟨u0, u1, u2⟩ + y := by
  rw [← Algebra.smul_def]
  apply Code.Cubic.ext <;>
    simp only [Code.Cubic.add_c0, Code.Cubic.add_c1, Code.Cubic.add_c2, Code.Cubic.smul_c0,
      Code.Cubic.smul_c1, Code.Cubic.smul_c2, mul_comm]

/-- One step of Horner's rule on single words. -/
theorem readE_hornerStep (c0 c1 c2 z : F) (x : E) :
    readE (E.mk3 (addF (mulF c0 z) x.c0) (addF (mulF c1 z) x.c1) (addF (mulF c2 z) x.c2)) =
      algebraMap GF GE (toF z) * readE (E.mk3 c0 c1 c2) + readE x := by
  rw [readE_mk3, readE_mk3, toF_addF, toF_addF, toF_addF, toF_mulF, toF_mulF, toF_mulF,
    ← readE_c0, ← readE_c1, ← readE_c2]
  exact cubic_hornerStep _ _ _ _ _

/-- The end of Horner's rule, as an equation between functions of the running value. -/
theorem hornerFrom_zero_fun (a : Array E) (z : F) :
    hornerFrom a z 0 = fun c0 c1 c2 => E.mk3 c0 c1 c2 := rfl

/-- One step of Horner's rule, as an equation between functions of the running value. -/
theorem hornerFrom_succ_fun (a : Array E) (z : F) (n : ℕ) :
    hornerFrom a z (n + 1) = fun c0 c1 c2 =>
      hornerFrom a z n (addF (mulF c0 z) (a.getD n zeroE).c0)
        (addF (mulF c1 z) (a.getD n zeroE).c1) (addF (mulF c2 z) (a.getD n zeroE).c2) := rfl

/-- Horner's rule on single words, from the running value s = (c0, c1, c2): s z^n plus the sum of
a[i] z^i over the i below n. -/
theorem readE_hornerFrom (a : Array E) (z : F) (n : ℕ) (c0 c1 c2 : F) :
    readE (hornerFrom a z n c0 c1 c2) =
      algebraMap GF GE (toF z ^ n) * readE (E.mk3 c0 c1 c2) +
        ∑ i ∈ Finset.range n, algebraMap GF GE (toF z ^ i) * readV a i := by
  induction n generalizing c0 c1 c2 with
  | zero =>
    rw [congrFun (congrFun (congrFun (hornerFrom_zero_fun a z) c0) c1) c2, pow_zero, map_one,
      one_mul, Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n ih =>
    have hv : readE (a.getD n zeroE) = readV a n := rfl
    rw [congrFun (congrFun (congrFun (hornerFrom_succ_fun a z n) c0) c1) c2, ih,
      readE_hornerStep, hv, Finset.sum_range_succ, pow_succ, map_mul]
    ring

/-- The program's symbol, written out as two runs of Horner's rule. -/
theorem symbolAt_eq (c : OnBytes.Code) (x : ℕ) (message tail : Array E) :
    symbolAt c x message tail = hornerFrom tail (codePoint c.logN x) c.r
      (hornerFrom message (codePoint c.logN x) c.ell 0 0 0).c0
      (hornerFrom message (codePoint c.logN x) c.ell 0 0 0).c1
      (hornerFrom message (codePoint c.logN x) c.ell 0 0 0).c2 := rfl

/-- The program's symbol: the polynomial with the tail's and then the message's entries as
coefficients, at the program's point. -/
theorem readE_symbolAt_pt (c : OnBytes.Code) (x : ℕ) (message tail : Array E) :
    readE (symbolAt c x message tail) =
      (∑ q ∈ Finset.range c.r, algebraMap GF GE (toF (codePoint c.logN x) ^ q) * readV tail q) +
        ∑ j ∈ Finset.range c.ell,
          algebraMap GF GE (toF (codePoint c.logN x) ^ (c.r + j)) * readV message j := by
  have h0 : readE (E.mk3 0 0 0) = 0 := readE_zero
  rw [symbolAt_eq, readE_hornerFrom, E.mk3_eta, readE_hornerFrom, h0, mul_zero, zero_add,
    Finset.mul_sum, add_comm]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [pow_add, map_mul, mul_assoc]

/-- The program's symbol of a word, for a code of at most 2^32 positions: the value of the format's
symbol at the triples of the message and the tail. -/
theorem readE_symbolAt (c : OnBytes.Code) (x : ℕ) (ha : c.logN ≤ 32) (hx : x < 2 ^ c.logN)
    (m t : Array E) :
    readE (symbolAt c x m t) =
      symV (codeOf c) x (m.toList.map E.triple) (t.toList.map E.triple) := by
  rw [readE_symbolAt_pt, toF_codePoint c.logN x ha hx]
  unfold symV
  simp only [readV_eq_readL, readL_eq_lst]
  rfl

/-- The program's symbol of a word is the library's encoder at the code's own positions. -/
theorem readE_symbolAt_enc (c : OnBytes.Code) (ha : c.logN ≤ 32) (x : Fin (2 ^ (codeOf c).a))
    (m t : Array E) :
    readE (symbolAt c x.val m t) =
      (ldOf (codeOf c) (codeOf c).a).enc (fun j => readV m j.val) (fun q => readV t q.val) x
        () := by
  have h := toE_symE_enc (codeOf c) x (m.toList.map E.triple) (t.toList.map E.triple)
  simp only [← readL_eq_lst, ← readV_eq_readL] at h
  have h1 : readE (symbolAt c x.val m t) =
      toE (Fmt.M1.symE (codeOf c) x.val (m.toList.map E.triple) (t.toList.map E.triple)) := by
    rw [readE_symbolAt c x.val ha x.isLt]
    exact (toE_symE (codeOf c) x.val _ _).symm
  exact h1.trans h

/-- The position of a shorter word that goes with a position is the format's. -/
theorem shortPosition_eq (c : OnBytes.Code) (x : ℕ) :
    shortPosition c.logN x = Fmt.M1.cp (codeOf c) x := rfl

/-! ## Inner products -/

/-- The program's inner product, as a sum over any range that holds the shorter vector. -/
theorem readE_inner (a b : Array E) (n : ℕ) (h : min a.size b.size ≤ n) :
    readE (inner a b) = ∑ i ∈ Finset.range n, readV a i * readV b i := by
  have hk : ∀ k, readE ((List.range k).foldl (fun s i =>
      maddE s (a.getD i zeroE) (b.getD i zeroE)) zeroE) =
      ∑ i ∈ Finset.range k, readV a i * readV b i := by
    intro k
    induction k with
    | zero => exact readE_zero
    | succ k ih =>
      rw [List.range_succ, List.foldl_append, Finset.sum_range_succ]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [readE_maddE, ih]
      rfl
  unfold inner
  rw [hk]
  refine Finset.sum_subset (Finset.range_subset_range.2 h) fun i _ hi => ?_
  have hi' : min a.size b.size ≤ i := Nat.le_of_not_lt fun hlt => hi (Finset.mem_range.2 hlt)
  rcases min_le_iff.1 hi' with ha | hb
  · rw [readV_of_le a i ha, zero_mul]
  · rw [readV_of_le b i hb, mul_zero]

end OnBytes.Slice

#print axioms OnBytes.Slice.readL_eq_lst
#print axioms OnBytes.Slice.readV_eq_vec
#print axioms OnBytes.Slice.readP_eq_ptL
#print axioms OnBytes.Slice.eqW_readL
#print axioms OnBytes.Slice.lstF_nil
#print axioms OnBytes.Slice.lstF_cons_zero
#print axioms OnBytes.Slice.lstF_cons_succ
#print axioms OnBytes.Slice.lstF_of_le
#print axioms OnBytes.Slice.toF_getD
#print axioms OnBytes.Slice.lstF_append
#print axioms OnBytes.Slice.lstF_map_mul
#print axioms OnBytes.Slice.lstF_take
#print axioms OnBytes.Slice.ceilLog2_eq
#print axioms OnBytes.Slice.le_two_pow_ceilLog2
#print axioms OnBytes.Slice.ceilLog2_le
#print axioms OnBytes.Slice.ceilLog2_two_pow
#print axioms OnBytes.Slice.ceilLog2_eq_clog
#print axioms OnBytes.Slice.squaresOf_zero
#print axioms OnBytes.Slice.squaresOf_succ
#print axioms OnBytes.Slice.length_squaresOf
#print axioms OnBytes.Slice.lstF_squaresOf
#print axioms OnBytes.Slice.take_squaresOf
#print axioms OnBytes.Slice.productIndex_nil
#print axioms OnBytes.Slice.productIndex_cons
#print axioms OnBytes.Slice.toF_productIndex_cons
#print axioms OnBytes.Slice.toF_productIndex_zero
#print axioms OnBytes.Slice.toF_productIndex_squares
#print axioms OnBytes.Slice.tableStep_pos
#print axioms OnBytes.Slice.tableStep_neg
#print axioms OnBytes.Slice.size_tableFold
#print axioms OnBytes.Slice.lstF_tableFold
#print axioms OnBytes.Slice.productTable_eq
#print axioms OnBytes.Slice.size_productTable
#print axioms OnBytes.Slice.lstF_productTable
#print axioms OnBytes.Slice.expFrom_add
#print axioms OnBytes.Slice.expFrom_zero
#print axioms OnBytes.Slice.codePoint_loop
#print axioms OnBytes.Slice.toF_codePoint
#print axioms OnBytes.Slice.lstF_powerTable
#print axioms OnBytes.Slice.size_powerTable
#print axioms OnBytes.Slice.dim_le_logDim
#print axioms OnBytes.Slice.r_le_logDim
#print axioms OnBytes.Slice.ell_le_logDim
#print axioms OnBytes.Slice.generatorTail_eq
#print axioms OnBytes.Slice.generatorMessage_eq
#print axioms OnBytes.Slice.generatorAt_f
#print axioms OnBytes.Slice.generatorAt_messageScale
#print axioms OnBytes.Slice.generatorAt_tailScale
#print axioms OnBytes.Slice.toF_tailScale
#print axioms OnBytes.Slice.toF_messageScale
#print axioms OnBytes.Slice.size_generatorTail
#print axioms OnBytes.Slice.size_generatorMessage
#print axioms OnBytes.Slice.toF_generatorTail
#print axioms OnBytes.Slice.toF_generatorMessage
#print axioms OnBytes.Slice.cubic_hornerStep
#print axioms OnBytes.Slice.readE_hornerStep
#print axioms OnBytes.Slice.hornerFrom_zero_fun
#print axioms OnBytes.Slice.hornerFrom_succ_fun
#print axioms OnBytes.Slice.readE_hornerFrom
#print axioms OnBytes.Slice.symbolAt_eq
#print axioms OnBytes.Slice.readE_symbolAt_pt
#print axioms OnBytes.Slice.readE_symbolAt
#print axioms OnBytes.Slice.readE_symbolAt_enc
#print axioms OnBytes.Slice.shortPosition_eq
#print axioms OnBytes.Slice.readE_inner
