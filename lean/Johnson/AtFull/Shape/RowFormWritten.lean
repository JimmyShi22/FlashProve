-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Shape/RowFormWritten.lean: THE VERIFIER's TEST OF ITS OWN LEDGER "THE WRITTEN-OUT
WEIGHTS OF A VIRTUAL ROW ARE ITS PRODUCT FORM's" ("K9.row-form-values",
Johnson/Desc/First/Batch/Text.lean; the program's "internal-row-form", OnBytes/Model/Trees.lean)
ACCEPTS AT EACH OF THE FOUR MAKES OF A ROW THAT THE STEP "THE WEIGHTS OF EVERY VIRTUAL ROW" LAYS
(`coefBody`, Johnson/Desc/First/TailClaims/Coefficients.lean): 1 on every row; the powers of an
element; the equality polynomial's table on all rows; that table on an aligned block of rows. AS
MACHINE WORDS, AT EVERY POINT AND EVERY BASE, WHETHER OR NOT THEIR WORDS ARE BELOW THE PRIME.
General laws on plain data; no head; nothing is evaluated.

Why it is no triviality. The two sides are computed by different texts. The table's step turns an
entry a into a - a z and a z, the first coordinate at the top bit (`eqTabStep`,
OnBytes/Model/Frame.lean); the product form written out turns the whole array into (all times lo) ++
(all times hi) with lo = 1 - z, bit 0 first (`productWritten`, Trees.lean). The powers are made by a
loop c, c x, c x x (`powers`, Frame.lean); the form has the repeated squares. So the equations hold
by the field's laws, not by the texts.

How. Both sides are read in the library's field (`Reading.gl`, OnBytes/Model/HideLaws.lean), where
they are one element; every entry on either side is 1, 0, or a result of a product or a difference,
and such a result is three words below the prime whatever goes in (`Fmt.Fld.ok_add`, `ok_sub`); and
two elements of words below the prime that read alike are one (`readE_inj`,
OnBytes/Slice/ProgField.lean). The table's value is the library's (`eqTab_value`,
Johnson/Road/FormsKeysEq.lean).

Main names.
* `written_value`, `written_size`, `written_ok`: a product form written out: entry i reads as the
  product over the bits t of i of hi[t] or lo[t]; 2^(pairs) entries; words below the prime.
* `powers_value`, `powers_ok`; `squares_value`, `squaresW_size`; `prod_bits_pow`; `eqTab_ok`;
  `alignedBlock_iff`.
* `FormHolds X r`: at each row i < X.R of the array the two vectors have the same entry.
  `formHolds_of`: from the equation in the field, where r.coef holds words below the prime.
* `formHolds_ones`: formOnes, with X.R ones. `formHolds_powers`: formPowers at base b and X.R rows,
  with powers b X.R. `formHolds_table`: formPoint at z and first row 0, with eqTab z, where clog2
  X.R = z.size. `formHolds_block`: formPoint at z and first row r0, with `blockTab z r0 X.R` (the
  table on the rows r0 to r0 + 2^z.size - 1, 0 elsewhere), where z.size ≤ clog2 X.R, r0 is a
  multiple of 2^z.size and r0 < 2^(clog2 X.R).
* `formHolds_test`: FormHolds X r gives the verifier's own Bool.
* Small ones beneath. `writtenStep`, `productWritten_eq`, `written_fold`, `bitsProd`: the
  written-out form as a fold of one step, and the product that entry i stands for. `okE_mulW`,
  `okE_subW`, `WordsOk`, `WordsOk.getD`, `eq_of_gl`: words below the prime. `powersLoop_laws`,
  `squares_laws`: the two loops. `rowProduct_size`, `rowProduct_lo`, `rowProduct_hi`.
  `blockTab_getD`, `blockTab_ok`. `everyFrom_of`.

Limits. FOUR MAKES OF ONE ROW: NOTHING ON A LEDGER: that each row of a ledger which has a product
form is of one of these makes, with these very letters (the array's number of rows for the powers'
count; 2^z.size for a piece's number of rows; an aligned first row), is not shown here. The three
makes with a point or with ones ask that the row in front has no lists of factors (rowLo, rowHi
empty): these makes do not clear them. The test on the form's sizes ("K9.row-form") is not treated.
Nothing on soundness, completeness or hiding.
-/
import OnBytes.Model.Trees
import OnBytes.Model.HideLaws
import OnBytes.Slice.ProgField
import Johnson.Road.FormsKeysEq
import OnBytes.Slice.ProgCodes
import OnBytes.Model.Tail
import Johnson.Desc.First.Batch.Lay

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Shape
open OnBytes OnBytes.Model
open OnBytes.Model.HTailF2 (formOnes formPoint formPowers squares)
open Finset

variable {K : Type} [CommRing K] (ρ : Reading K)

/-- One step of productWritten. -/
def writtenStep (w : IndexWeights) (all : Array E) (t : Nat) : Array E :=
  all.map (fun x => mulE x (w.lo.getD t zeroE)) ++ all.map (fun x => mulE x (w.hi.getD t zeroE))

/-- productWritten is the fold of that step. -/
theorem productWritten_eq (w : IndexWeights) :
    productWritten w = (List.range w.lo.size).foldl (writtenStep w) #[oneE] := rfl

/-- The product that entry i stands for, over the first k bits. -/
def bitsProd (w : IndexWeights) (k i : Nat) : K :=
  ∏ t ∈ range k, (if i.testBit t then ρ.val (w.hi.getD t zeroE) else ρ.val (w.lo.getD t zeroE))

/-- Behind k steps the array has 2^k entries, and entry i reads as the product over i's first k
bits. -/
theorem written_fold (w : IndexWeights) : ∀ k : Nat,
    ((List.range k).foldl (writtenStep w) #[oneE]).size = 2 ^ k ∧
      ∀ i, i < 2 ^ k →
        ρ.val (((List.range k).foldl (writtenStep w) #[oneE]).getD i zeroE) = bitsProd ρ w k i
  | 0 => by
    refine ⟨rfl, fun i hi => ?_⟩
    obtain rfl : i = 0 := by simpa using hi
    simp [bitsProd, ρ.one]
  | k + 1 => by
    obtain ⟨hs, hv⟩ := written_fold w k
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range k).foldl (writtenStep w) #[oneE] = A at hs hv
    refine ⟨by
      simp only [writtenStep, Array.size_append, Array.size_map, hs, Nat.pow_succ]
      omega, fun i hi => ?_⟩
    unfold bitsProd
    rw [prod_range_succ]
    by_cases h : i < 2 ^ k
    · have e : (writtenStep w A k).getD i zeroE = mulE (A.getD i zeroE) (w.lo.getD k zeroE) := by
        simp [writtenStep, Array.getD, hs, h]
        omega
      rw [e, ρ.mul, hv i h, Nat.testBit_lt_two_pow h]
      rfl
    · have hj : i - 2 ^ k < 2 ^ k := by
        rw [Nat.pow_succ] at hi
        omega
      have ei : i = 2 ^ k + (i - 2 ^ k) := by omega
      have e : (writtenStep w A k).getD i zeroE =
          mulE (A.getD (i - 2 ^ k) zeroE) (w.hi.getD k zeroE) := by
        have hi' : i < 2 ^ k + 2 ^ k := by
          rw [Nat.pow_succ] at hi
          omega
        simp [writtenStep, Array.getD, Array.getElem_append, hs, h, hj, hi']
      have hb : i.testBit k = true := by
        rw [ei, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj]
        rfl
      rw [e, ρ.mul, hv _ hj, hb]
      unfold bitsProd
      congr 1
      refine prod_congr rfl fun t ht => ?_
      have ht' : t < k := mem_range.1 ht
      rw [ei, Nat.testBit_two_pow_add_gt ht']
      simp

/-- **Entry i of a product form written out reads as the product, over the bits t of i, of hi[t]
where the bit is set and of lo[t] where it is not**: at every reading. -/
theorem written_value (w : IndexWeights) (i : Nat) (hi : i < 2 ^ w.lo.size) :
    ρ.val ((productWritten w).getD i zeroE) = bitsProd ρ w w.lo.size i :=
  (written_fold ρ w w.lo.size).2 i hi

/-- It has one entry for each index of as many bits as the form has pairs. -/
theorem written_size (w : IndexWeights) : (productWritten w).size = 2 ^ w.lo.size :=
  (written_fold Reading.gl w w.lo.size).1

/-! ## Words below the prime -/

/-- A product is three words below the prime, whatever the factors. -/
theorem okE_mulW (a b : E) : okE (mulE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.mulE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.mulE
  simp [Fmt.Fld.ok_add]

/-- So is a difference. -/
theorem okE_subW (a b : E) : okE (subE a b) = true := by
  rw [OnBytes.okE_triple, OnBytes.subE_triple]
  unfold Fmt.Fld.okE Fmt.Fld.subE
  simp [Fmt.Fld.ok_sub]

/-- All entries of an array are words below the prime. -/
def WordsOk (A : Array E) : Prop := ∀ x ∈ A.toList, okE x = true

/-- Then so is what is read at any index, the default 0 too. -/
theorem WordsOk.getD {A : Array E} (h : WordsOk A) (i : Nat) : okE (A.getD i zeroE) = true := by
  by_cases hi : i < A.size
  · have : A.getD i zeroE = A[i] := by simp [Array.getD, hi]
    rw [this]
    exact h _ (Array.getElem_mem_toList hi)
  · have : A.getD i zeroE = zeroE := by simp [Array.getD, hi]
    rw [this]
    rfl

/-- A product form written out holds words below the prime alone, whatever its pairs. -/
theorem written_ok (w : IndexWeights) : WordsOk (productWritten w) := by
  rw [productWritten_eq]
  have key : ∀ (l : List Nat) (A : Array E), WordsOk A → WordsOk (l.foldl (writtenStep w) A) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons t l ih =>
      intro A _
      refine ih _ fun x hx => ?_
      unfold writtenStep at hx
      rw [Array.toList_append, List.mem_append, Array.toList_map, Array.toList_map] at hx
      rcases hx with hx | hx <;> obtain ⟨y, -, rfl⟩ := List.mem_map.1 hx <;> exact okE_mulW _ _
  refine key _ _ fun x hx => ?_
  obtain rfl : x = oneE := by simpa using hx
  rfl

/-- Two words below the prime that read alike in the library's field are one. -/
theorem eq_of_gl {a b : E} (ha : okE a = true) (hb : okE b = true)
    (h : Reading.gl.val a = Reading.gl.val b) : a = b :=
  OnBytes.Slice.readE_inj a b ha hb h

/-! ## The powers -/

/-- The loop of `powers`: its size; it leaves what is laid; what it appends reads as c, c x, c x^2
and so on; it keeps "words below the prime". -/
theorem powersLoop_laws (x : E) : ∀ (n : Nat) (c : E) (a : Array E),
    (powersLoop x n c a).size = a.size + n ∧
      (∀ i, i < a.size → (powersLoop x n c a).getD i zeroE = a.getD i zeroE) ∧
      (∀ j, j < n → ρ.val ((powersLoop x n c a).getD (a.size + j) zeroE) =
        ρ.val c * ρ.val x ^ j) ∧
      (WordsOk a → okE c = true → WordsOk (powersLoop x n c a))
  | 0, c, a => ⟨rfl, fun _ _ => rfl, fun _ h => absurd h (Nat.not_lt_zero _), fun h _ => h⟩
  | n + 1, c, a => by
    obtain ⟨h1, h2, h3, h4⟩ := powersLoop_laws x n (mulE c x) (a.push c)
    have hs : (a.push c).size = a.size + 1 := Array.size_push _
    refine ⟨?_, fun i hi => ?_, fun j hj => ?_, fun ha hc => ?_⟩
    · show (powersLoop x n (mulE c x) (a.push c)).size = _
      rw [h1, hs]
      omega
    · show (powersLoop x n (mulE c x) (a.push c)).getD i zeroE = _
      rw [h2 i (by omega)]
      simp [Array.getD, Array.getElem_push, hi, Nat.lt_succ_of_lt hi]
    · show ρ.val ((powersLoop x n (mulE c x) (a.push c)).getD (a.size + j) zeroE) = _
      cases j with
      | zero =>
        rw [Nat.add_zero, h2 a.size (by omega)]
        simp [Array.getD]
      | succ j =>
        have := h3 j (by omega)
        rw [hs] at this
        rw [show a.size + (j + 1) = a.size + 1 + j from by omega, this, ρ.mul]
        ring
    · show WordsOk (powersLoop x n (mulE c x) (a.push c))
      refine h4 (fun y hy => ?_) (okE_mulW _ _)
      rw [Array.toList_push, List.mem_append] at hy
      rcases hy with hy | hy
      · exact ha y hy
      · obtain rfl : y = c := by simpa using hy
        exact hc

/-- **Entry i of the n powers of x reads as x^i.** -/
theorem powers_value (x : E) (n i : Nat) (hi : i < n) :
    ρ.val ((powers x n).getD i zeroE) = ρ.val x ^ i := by
  have := (powersLoop_laws ρ x n oneE (Array.emptyWithCapacity n)).2.2.1 i hi
  simpa [powers, ρ.one] using this

/-- The powers are words below the prime, whatever x. -/
theorem powers_ok (x : E) (n : Nat) : WordsOk (powers x n) :=
  (powersLoop_laws Reading.gl x n oneE (Array.emptyWithCapacity n)).2.2.2
    (fun y hy => by simp at hy) rfl

/-- In a commutative ring: the product of y^(2^t) over the set bits t of i is y^i. -/
theorem prod_bits_pow (y : K) : ∀ (n i : Nat), i < 2 ^ n →
    ∏ t ∈ range n, (if i.testBit t then y ^ 2 ^ t else 1) = y ^ i
  | 0, i, hi => by
    obtain rfl : i = 0 := by simpa using hi
    simp
  | n + 1, i, hi => by
    rw [prod_range_succ]
    by_cases h : i < 2 ^ n
    · rw [prod_bits_pow y n i h, Nat.testBit_lt_two_pow h]
      simp
    · have hj : i - 2 ^ n < 2 ^ n := by
        rw [Nat.pow_succ] at hi
        omega
      have ei : i = 2 ^ n + (i - 2 ^ n) := by omega
      have hb : i.testBit n = true := by
        rw [ei, Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hj]
        rfl
      have hp : ∏ t ∈ range n, (if i.testBit t then y ^ 2 ^ t else 1) = y ^ (i - 2 ^ n) := by
        rw [← prod_bits_pow y n _ hj]
        refine prod_congr rfl fun t ht => ?_
        rw [ei, Nat.testBit_two_pow_add_gt (mem_range.1 ht)]
        simp
      rw [hp, hb, if_pos rfl, ← pow_add]
      congr 1
      omega

/-! ## A virtual row's product form -/

/-- A row's product form has a pair for each bit of a row's number. -/
theorem rowProduct_size (X : HTree) (r : HRow) : (rowProduct X r).lo.size = clog2 X.R := by
  simp [rowProduct]

/-- Its factors at a bit that is not set. -/
theorem rowProduct_lo (X : HTree) (r : HRow) {t : Nat} (ht : t < clog2 X.R) :
    (rowProduct X r).lo.getD t zeroE = (rowFactors r t).1 := by
  simp [rowProduct, Array.getD, ht]

/-- Its factors at a bit that is set. -/
theorem rowProduct_hi (X : HTree) (r : HRow) {t : Nat} (ht : t < clog2 X.R) :
    (rowProduct X r).hi.getD t zeroE = (rowFactors r t).2 := by
  simp [rowProduct, Array.getD, ht]

/-- **The written-out weights are the product form's**, at each of the array's rows: what the
verifier's test "K9.row-form-values" asks. -/
def FormHolds (X : HTree) (r : HRow) : Prop :=
  ∀ i, i < X.R → (productWritten (rowProduct X r)).getD i zeroE = r.coef.getD i zeroE

/-- It follows from the equation in the library's field, where the written-out weights are words
below the prime. -/
theorem formHolds_of (X : HTree) (r : HRow) (hok : WordsOk r.coef)
    (h : ∀ i, i < X.R → ∏ t ∈ range (clog2 X.R),
      (if i.testBit t then Reading.gl.val (rowFactors r t).2
        else Reading.gl.val (rowFactors r t).1) = Reading.gl.val (r.coef.getD i zeroE)) :
    FormHolds X r := by
  intro i hi
  refine eq_of_gl ((written_ok _).getD i) (hok.getD i) ?_
  have hi2 : i < 2 ^ (rowProduct X r).lo.size := by
    rw [rowProduct_size]
    exact Nat.lt_of_lt_of_le hi (OnBytes.Slice.le_two_pow_ceilLog2 X.R)
  rw [written_value Reading.gl _ i hi2, ← h i hi]
  unfold bitsProd
  rw [rowProduct_size]
  refine prod_congr rfl fun t ht => ?_
  rw [rowProduct_lo X r (mem_range.1 ht), rowProduct_hi X r (mem_range.1 ht)]

/-! ### "1 on every row" -/

/-- **A row with the form "1 on every row" and R ones written out.** -/
theorem formHolds_ones (X : HTree) (row : HRow) (h1 : row.rowLo = #[]) (h2 : row.rowHi = #[]) :
    FormHolds X (formOnes { row with coef := Array.replicate X.R oneE }) := by
  refine formHolds_of X _ (fun x hx => ?_) fun i hi => ?_
  · have hx' : x ∈ (Array.replicate X.R oneE).toList := hx
    rw [Array.toList_replicate] at hx'
    rw [List.eq_of_mem_replicate hx']
    rfl
  · have ef : ∀ t, rowFactors (formOnes { row with coef := Array.replicate X.R oneE }) t =
        (oneE, oneE) := by
      intro t
      simp [rowFactors, formOnes, h1, h2]
    have ec : (formOnes { row with coef := Array.replicate X.R oneE }).coef.getD i zeroE =
        oneE := by
      show (Array.replicate X.R oneE).getD i zeroE = oneE
      simp [Array.getD, hi]
    rw [ec, Reading.gl.one]
    refine prod_eq_one fun t _ => ?_
    rw [ef t]
    simp [Reading.gl.one]

/-! ### The powers of an element -/

/-- The loop of `squares`: its size; the element that it carries; entry t reads as b^(2^t). -/
theorem squares_laws (b : E) : ∀ n : Nat,
    (((List.range n).foldl (fun (s : Array E × E) _ => (s.1.push s.2, mulE s.2 s.2))
      (#[], b)).1.size = n) ∧
    (ρ.val ((List.range n).foldl (fun (s : Array E × E) _ => (s.1.push s.2, mulE s.2 s.2))
      (#[], b)).2 = ρ.val b ^ 2 ^ n) ∧
    ∀ t, t < n → ρ.val (((List.range n).foldl
      (fun (s : Array E × E) _ => (s.1.push s.2, mulE s.2 s.2)) (#[], b)).1.getD t zeroE) =
        ρ.val b ^ 2 ^ t
  | 0 => ⟨rfl, by simp, fun _ h => absurd h (Nat.not_lt_zero _)⟩
  | n + 1 => by
    obtain ⟨h1, h2, h3⟩ := squares_laws b n
    rw [List.range_succ, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    generalize (List.range n).foldl (fun (s : Array E × E) _ => (s.1.push s.2, mulE s.2 s.2))
      (#[], b) = s at h1 h2 h3
    refine ⟨by simp [h1], ?_, fun t ht => ?_⟩
    · rw [ρ.mul, h2, ← pow_add]
      congr 1
      rw [Nat.pow_succ]
      omega
    · by_cases h : t < n
      · rw [← h3 t h]
        simp [Array.getD, Array.getElem_push, h1, h, Nat.lt_succ_of_lt h]
      · obtain rfl : t = n := by omega
        rw [← h2]
        simp [Array.getD, Array.getElem_push, h1]

/-- As many squares as asked. -/
theorem squaresW_size (b : E) (n : Nat) : (squares b n).size = n :=
  (squares_laws Reading.gl b n).1

/-- Entry t of the repeated squares of b reads as b^(2^t). -/
theorem squares_value (b : E) (n t : Nat) (ht : t < n) :
    ρ.val ((squares b n).getD t zeroE) = ρ.val b ^ 2 ^ t :=
  (squares_laws ρ b n).2.2 t ht

/-- **A row with the form "b^r on row r" and the R powers of b written out.** -/
theorem formHolds_powers (X : HTree) (row : HRow) (b : E) :
    FormHolds X (formPowers { row with coef := powers b X.R } b X.R) := by
  refine formHolds_of X _ (powers_ok b X.R) fun i hi => ?_
  have ec : (formPowers { row with coef := powers b X.R } b X.R).coef = powers b X.R := rfl
  rw [ec, powers_value Reading.gl b X.R i hi,
    ← prod_bits_pow (Reading.gl.val b) (clog2 X.R) i
      (Nat.lt_of_lt_of_le hi (OnBytes.Slice.le_two_pow_ceilLog2 X.R))]
  refine prod_congr rfl fun t ht => ?_
  have ht' : t < clog2 X.R := mem_range.1 ht
  have ef : rowFactors (formPowers { row with coef := powers b X.R } b X.R) t =
      (oneE, (squares b (clog2 X.R)).getD t zeroE) := by
    have hne : (Array.replicate (clog2 X.R) oneE).isEmpty = false := by
      simp
      omega
    simp [rowFactors, formPowers, hne, Array.getD, ht']
  rw [ef]
  simp only
  rw [squares_value Reading.gl b _ t ht', Reading.gl.one]

/-! ### The equality polynomial's table, on all rows -/

/-- The equality polynomial's table holds words below the prime alone, whatever the point. -/
theorem eqTab_ok (z : Array E) : WordsOk (eqTab z) := by
  unfold eqTab
  rw [← Array.foldl_toList]
  have key : ∀ (l : List E) (A : Array E), WordsOk A → WordsOk (l.foldl eqTabStep A) := by
    intro l
    induction l with
    | nil => exact fun _ h => h
    | cons zv l ih =>
      intro A _
      refine ih _ fun x hx => ?_
      rw [OnBytes.Road.eqTabStep_toList] at hx
      obtain ⟨a, -, ha⟩ := List.mem_flatMap.1 hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact okE_subW _ _
      · exact okE_mulW _ _
  refine key _ _ fun x hx => ?_
  obtain rfl : x = oneE := by simpa using hx
  rfl

/-- **A row with the form "the equality polynomial at z" on all rows, and z's table written out**,
where z has a coordinate for each bit of a row's number. -/
theorem formHolds_table (X : HTree) (row : HRow) (z : Array E) (h1 : row.rowLo = #[])
    (h2 : row.rowHi = #[]) (hz : clog2 X.R = z.size) :
    FormHolds X (formPoint { row with coef := eqTab z } z 0) := by
  refine formHolds_of X _ (eqTab_ok z) fun i hi => ?_
  have hi2 : i < 2 ^ z.size := by
    rw [← hz]
    exact Nat.lt_of_lt_of_le hi (OnBytes.Slice.le_two_pow_ceilLog2 X.R)
  have ec : (formPoint { row with coef := eqTab z } z 0).coef = eqTab z := rfl
  rw [ec, OnBytes.Road.eqTab_value Reading.gl z i hi2, hz]
  unfold Blocks.eqN
  rw [← prod_range_reflect]
  refine prod_congr rfl fun t ht => ?_
  have ht' : t < z.size := mem_range.1 ht
  have hu : z.size - 1 - t < z.size := by omega
  have eu : z.size - 1 - (z.size - 1 - t) = t := by omega
  have ef : rowFactors (formPoint { row with coef := eqTab z } z 0) (z.size - 1 - t) =
      (subE oneE (z.getD t zeroE), z.getD t zeroE) := by
    simp [rowFactors, formPoint, h1, h2, hu, eu]
  rw [ef]
  simp only
  rw [Reading.gl.sub, Reading.gl.one]
  simp [OnBytes.Road.pt]

/-! ### The equality polynomial's table on a block of rows -/

/-- The rows of an aligned block of 2^n rows are those whose bits from n on are the first row's. -/
theorem alignedBlock_iff {n B i r0 : Nat} (hi : i < 2 ^ B) (hr : r0 < 2 ^ B)
    (hal : r0 % 2 ^ n = 0) :
    (∀ u ∈ range (B - n), i.testBit (n + u) = r0.testBit (n + u)) ↔
      (r0 ≤ i ∧ i < r0 + 2 ^ n) := by
  have hP : 0 < 2 ^ n := Nat.two_pow_pos n
  have hD : (∀ u ∈ range (B - n), i.testBit (n + u) = r0.testBit (n + u)) ↔
      i / 2 ^ n = r0 / 2 ^ n := by
    constructor
    · intro h
      refine Nat.eq_of_testBit_eq fun k => ?_
      rw [Nat.testBit_div_two_pow, Nat.testBit_div_two_pow, Nat.add_comm k n]
      by_cases hk : k < B - n
      · exact h k (mem_range.2 hk)
      · have hB : 2 ^ B ≤ 2 ^ (n + k) := Nat.pow_le_pow_right (by omega) (by omega)
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hi hB),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hr hB)]
    · intro e u _
      rw [Nat.add_comm n u, ← Nat.testBit_div_two_pow, ← Nat.testBit_div_two_pow, e]
  rw [hD]
  have h1 := Nat.div_add_mod i (2 ^ n)
  have h2 := Nat.div_add_mod r0 (2 ^ n)
  have h3 := Nat.mod_lt i hP
  constructor
  · intro e
    rw [e] at h1
    omega
  · rintro ⟨a, b⟩
    refine Nat.div_eq_of_lt_le ?_ ?_
    · rw [Nat.mul_comm]
      omega
    · rw [Nat.add_mul, Nat.one_mul, Nat.mul_comm]
      omega

/-- The weights that the smallness test writes for a piece: the table on the rows r0, ..,
r0 + 2^n - 1, and 0 elsewhere. -/
def blockTab (z : Array E) (r0 R : Nat) : Array E :=
  (Array.range R).map fun r =>
    if r0 ≤ r ∧ r < r0 + 2 ^ z.size then (eqTab z).getD (r - r0) zeroE else zeroE

/-- Its entry at a row of the array. -/
theorem blockTab_getD (z : Array E) (r0 R : Nat) {i : Nat} (hi : i < R) :
    (blockTab z r0 R).getD i zeroE =
      if r0 ≤ i ∧ i < r0 + 2 ^ z.size then (eqTab z).getD (i - r0) zeroE else zeroE := by
  simp [blockTab, Array.getD, hi]

/-- They are words below the prime, whatever the point. -/
theorem blockTab_ok (z : Array E) (r0 R : Nat) : WordsOk (blockTab z r0 R) := by
  intro x hx
  unfold blockTab at hx
  rw [Array.toList_map] at hx
  obtain ⟨r, -, rfl⟩ := List.mem_map.1 hx
  split
  · exact (eqTab_ok z).getD _
  · rfl

/-- **A row with the form "the equality polynomial at z on the block that begins at r0", and these
weights written out**, where the block is aligned. -/
theorem formHolds_block (X : HTree) (row : HRow) (z : Array E) (r0 : Nat) (h1 : row.rowLo = #[])
    (h2 : row.rowHi = #[]) (hz : z.size ≤ clog2 X.R) (hal : r0 % 2 ^ z.size = 0)
    (hr : r0 < 2 ^ clog2 X.R) :
    FormHolds X (formPoint { row with coef := blockTab z r0 X.R } z r0) := by
  refine formHolds_of X _ (blockTab_ok z r0 X.R) fun i hi => ?_
  have hi2 : i < 2 ^ clog2 X.R :=
    Nat.lt_of_lt_of_le hi (OnBytes.Slice.le_two_pow_ceilLog2 X.R)
  have ec : (formPoint { row with coef := blockTab z r0 X.R } z r0).coef = blockTab z r0 X.R := rfl
  rw [ec, blockTab_getD z r0 X.R hi]
  obtain ⟨m, hm⟩ : ∃ m, clog2 X.R = z.size + m := ⟨clog2 X.R - z.size, by omega⟩
  rw [hm, prod_range_add]
  have elow : ∀ t, t < z.size →
      rowFactors (formPoint { row with coef := blockTab z r0 X.R } z r0) t =
        (subE oneE (z.getD (z.size - 1 - t) zeroE), z.getD (z.size - 1 - t) zeroE) := by
    intro t ht
    simp [rowFactors, formPoint, h1, h2, ht]
  have ehigh : ∀ u, rowFactors (formPoint { row with coef := blockTab z r0 X.R } z r0)
      (z.size + u) = if r0.testBit (z.size + u) then (zeroE, oneE) else (oneE, zeroE) := by
    intro u
    simp [rowFactors, formPoint, h1, h2]
  have e2 : ∏ u ∈ range m,
      (if i.testBit (z.size + u) then Reading.gl.val (rowFactors
          (formPoint { row with coef := blockTab z r0 X.R } z r0) (z.size + u)).2
        else Reading.gl.val (rowFactors
          (formPoint { row with coef := blockTab z r0 X.R } z r0) (z.size + u)).1) =
      if ∀ u ∈ range m, i.testBit (z.size + u) = r0.testBit (z.size + u) then 1 else 0 := by
    rw [← prod_const_one (s := range m), ← prod_ite_zero]
    refine prod_congr rfl fun u _ => ?_
    rw [ehigh u]
    cases i.testBit (z.size + u) <;> cases r0.testBit (z.size + u) <;>
      simp [Reading.gl.one, Reading.gl.zero]
  rw [e2]
  have hb := alignedBlock_iff (n := z.size) hi2 hr hal
  rw [show clog2 X.R - z.size = m from by omega] at hb
  by_cases hc : r0 ≤ i ∧ i < r0 + 2 ^ z.size
  · rw [if_pos hc, if_pos (hb.2 hc), mul_one,
      OnBytes.Road.eqTab_value Reading.gl z (i - r0) (by omega)]
    unfold Blocks.eqN
    rw [← prod_range_reflect]
    refine prod_congr rfl fun t ht => ?_
    have ht' : t < z.size := mem_range.1 ht
    have hu : z.size - 1 - t < z.size := by omega
    have eu : z.size - 1 - (z.size - 1 - t) = t := by omega
    rw [elow _ hu, eu]
    simp only
    have em : i - r0 = i % 2 ^ z.size := by
      have h5 := Nat.div_add_mod r0 (2 ^ z.size)
      have h6 : i = 2 ^ z.size * (r0 / 2 ^ z.size) + (i - r0) := by omega
      rw [h6, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [em, Nat.testBit_mod_two_pow, Reading.gl.sub, Reading.gl.one]
    simp [OnBytes.Road.pt, hu]
  · rw [if_neg hc, if_neg (fun h => hc (hb.1 h)), mul_zero, Reading.gl.zero]

/-! ## The verifier's own test -/

/-- A test that holds at each number from i on, count numbers. -/
theorem everyFrom_of (p : Nat → Bool) : ∀ (count i : Nat),
    (∀ j, i ≤ j → j < i + count → p j = true) →
      VerifiableInference.Desc.K9.everyFrom p count i = true
  | 0, _, _ => rfl
  | count + 1, i, h => by
    rw [VerifiableInference.Desc.K9.everyFrom, Bool.and_eq_true]
    exact ⟨h i (Nat.le_refl _) (by omega),
      everyFrom_of p count (i + 1) fun j h1 h2 => h j (by omega) (by omega)⟩

/-- **So the verifier's test "K9.row-form-values" accepts.** -/
theorem formHolds_test {X : HTree} {r : HRow} (h : FormHolds X r) :
    VerifiableInference.Desc.K9.everyBelow X.R (fun i =>
      (productWritten (rowProduct X r)).getD i zeroE == r.coef.getD i zeroE) = true :=
  everyFrom_of _ _ _ fun j _ hj => beq_iff_eq.2 (h j (by omega))

end Johnson.AtFull.Shape

#print axioms Johnson.AtFull.Shape.productWritten_eq
#print axioms Johnson.AtFull.Shape.written_fold
#print axioms Johnson.AtFull.Shape.written_value
#print axioms Johnson.AtFull.Shape.written_size
#print axioms Johnson.AtFull.Shape.okE_mulW
#print axioms Johnson.AtFull.Shape.okE_subW
#print axioms Johnson.AtFull.Shape.WordsOk.getD
#print axioms Johnson.AtFull.Shape.written_ok
#print axioms Johnson.AtFull.Shape.eq_of_gl
#print axioms Johnson.AtFull.Shape.powersLoop_laws
#print axioms Johnson.AtFull.Shape.powers_value
#print axioms Johnson.AtFull.Shape.powers_ok
#print axioms Johnson.AtFull.Shape.prod_bits_pow
#print axioms Johnson.AtFull.Shape.rowProduct_size
#print axioms Johnson.AtFull.Shape.rowProduct_lo
#print axioms Johnson.AtFull.Shape.rowProduct_hi
#print axioms Johnson.AtFull.Shape.formHolds_of
#print axioms Johnson.AtFull.Shape.formHolds_ones
#print axioms Johnson.AtFull.Shape.squares_laws
#print axioms Johnson.AtFull.Shape.squaresW_size
#print axioms Johnson.AtFull.Shape.squares_value
#print axioms Johnson.AtFull.Shape.formHolds_powers
#print axioms Johnson.AtFull.Shape.eqTab_ok
#print axioms Johnson.AtFull.Shape.formHolds_table
#print axioms Johnson.AtFull.Shape.alignedBlock_iff
#print axioms Johnson.AtFull.Shape.blockTab_getD
#print axioms Johnson.AtFull.Shape.blockTab_ok
#print axioms Johnson.AtFull.Shape.formHolds_block
#print axioms Johnson.AtFull.Shape.everyFrom_of
#print axioms Johnson.AtFull.Shape.formHolds_test
