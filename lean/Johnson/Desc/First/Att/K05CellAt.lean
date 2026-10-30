-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/K05CellAt.lean: TWO WRITINGS OF ONE PLAN, SECOND PART: AT WHICH PLACE OF ITS
ORACLE MESSAGE's TABLE AN ELEMENT OF AN ARRAY LIES. The batching kind's dataOf
(Johnson/Desc/First/Batch/Law/AsRow.lean) reads element (i, c) of an array as a SUM: over the
array's blocks, and in a block over every index J of the table, of "J is in the block's rectangle"
times "the block's element at J is (i, c)" times the table's entry J (cellOfBlock). Its docstring:
"Meant: one entry, or none. Not proved here." The closed callers of the lookups find the element by
laidPlace (Johnson/Desc/First/Look/K3CallerBase.lean): the first block that holds it, then that
block's rule. Here the two are tied, under the programs' own test on an array's layout
(laidMatrixOk, OnBytes/Iop/ReqRows.lean).

IS IT EMPTY HERE? The theorems on one block and on a list hold at every block with BlockFacts
(Johnson/Desc/First/Batch/Law/Laid.lean: what laidBlockOk says). No layout is evaluated here.

Main names:
  `laidPlace_one`: the lookups' laidPlace is the description's laidAt (Johnson/Desc/LaidAt.lean):
    two of the three writings are one function.
  `digit`, `digits_at`, `digits_one`: four digits in a mixed radix: a number below a A p Q is
    u + a (fr + A (v + p fp)) just if these are its digits.
  `numIn`, `numIn_lt`, `num_of_halves`: an element's number within its block, and back.
  `tableIndex R (row, place)` := row + 2 ^ R * place: the table's index. `tableIndex_parts`.
  `cellOfBlock_holds`: **at an element that the block holds the sum is the table's entry at the row
    and place at which the block lays the element.** `cellOfBlock_not`: at any other element it is
    0.
  `laidIn_row_lt`: that row is a row of the table.
  `blocks_sum`: over a list of blocks no two of which meet: the entry at laidPlace's answer; 0 WHERE
    NO BLOCK HOLDS THE ELEMENT (there the callers' reading is 0 as well).
  `dataOf_cell`: **dataOf's cell is the table's entry at tableIndex of laidPlace's answer**, where
    the layout has the array, the live request finds its message, and laidMatrixOk says yes.
Limits. That every element inside an array's sizes is held by a block (no hole) is not shown:
laidMatrixOk's count of elements would give it; it is not needed for the equation. Nothing on which
message (Johnson/Desc/First/Att/K05SeatsOne.lean) or which seat of the book. General in the sort of
link, though the file stands among the files of kind K5.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallerBase
import Johnson.Desc.First.Batch.Law.AsRow
import Johnson.Desc.LaidAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open OnBytes OnBytes.Params
open VerifiableInference.Desc.First.Look (laidHolds laidPlace)
open VerifiableInference.Desc.K9L (cellOfBlock inBlock xOf iOf cOf BlockFacts blockFacts dataOf)

/-! ## Two of the three writings are one function -/

/-- The lookups' writing of "where a block lays an element" is the description's. -/
theorem laidIn_one (b : LaidBlock) (i c : ℕ) :
    VerifiableInference.Desc.laidIn b i c =
      if laidHolds b i c = true then some (VerifiableInference.Desc.First.Look.laidIn b i c) else none := by
  unfold VerifiableInference.Desc.laidIn laidHolds VerifiableInference.Desc.First.Look.laidIn
  by_cases h : b.firstI ≤ i ∧ i < b.firstI + 2 ^ b.bitsI ∧ b.firstC ≤ c ∧ c < b.firstC + 2 ^ b.bitsC
  · obtain ⟨h1, h2, h3, h4⟩ := h
    simp [h1, h2, h3, h4]
  · rw [if_neg h, if_neg]
    intro h'
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h'
    exact h ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

/-- **The two writings of "where an array lays an element" are one.** -/
theorem laidPlace_one (a : ReqArray) (i c : ℕ) :
    laidPlace a.blocks i c = VerifiableInference.Desc.laidAt a i c := by
  unfold laidPlace VerifiableInference.Desc.laidAt
  induction a.blocks with
  | nil => rfl
  | cons b l ih =>
    rw [List.find?_cons, List.findSome?_cons, laidIn_one]
    by_cases h : laidHolds b i c = true
    · simp [h]
    · simp only [h, if_false, Bool.false_eq_true]
      exact ih

/-! ## Four digits in a mixed radix -/

theorem digit (j a z : ℕ) (h : j < a) : (j + a * z) % a = j ∧ (j + a * z) / a = z := by
  have ha : 0 < a := Nat.lt_of_le_of_lt (Nat.zero_le _) h
  exact ⟨by rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h],
    by rw [Nat.add_mul_div_left _ _ ha, Nat.div_eq_of_lt h, Nat.zero_add]⟩

/-- The four digits of u + a (fr + A (v + p fp)). -/
theorem digits_at (a A p Q fr fp u v : ℕ) (hu : u < a) (hfr : fr < A) (hv : v < p) (hfp : fp < Q) :
    let J := (a * fr + u) + a * A * (p * fp + v)
    J % a = u ∧ J / a % A = fr ∧ J / (a * A) % p = v ∧ J / (a * A * p) % Q = fp ∧
      J < a * A * (p * Q) := by
  intro J
  have e : J = u + a * (fr + A * (v + p * fp)) := by
    show (a * fr + u) + a * A * (p * fp + v) = _
    ring
  obtain ⟨d1, d2⟩ := digit u a (fr + A * (v + p * fp)) hu
  obtain ⟨d3, d4⟩ := digit fr A (v + p * fp) hfr
  obtain ⟨d5, d6⟩ := digit v p fp hv
  refine ⟨by rw [e, d1], by rw [e, d2, d3], ?_, ?_, ?_⟩
  · rw [← Nat.div_div_eq_div_mul, e, d2, d4, d5]
  · rw [← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul, e, d2, d4, d6, Nat.mod_eq_of_lt hfp]
  · rw [e]
    have h1 : v + p * fp < p * Q := by
      calc v + p * fp < p + p * fp := by omega
        _ = p * (fp + 1) := by ring
        _ ≤ p * Q := Nat.mul_le_mul_left _ hfp
    have h2 : fr + A * (v + p * fp) < A * (p * Q) := by
      calc fr + A * (v + p * fp) < A + A * (v + p * fp) := by omega
        _ = A * (v + p * fp + 1) := by ring
        _ ≤ A * (p * Q) := Nat.mul_le_mul_left _ h1
    calc u + a * (fr + A * (v + p * fp)) < a + a * (fr + A * (v + p * fp)) := by omega
      _ = a * (fr + A * (v + p * fp) + 1) := by ring
      _ ≤ a * (A * (p * Q)) := Nat.mul_le_mul_left _ h2
      _ = a * A * (p * Q) := by ring

/-- A number below a A p Q with these four digits is that number. -/
theorem digits_one (a A p Q fr fp u v J : ℕ) 
    (hJ : J < a * A * (p * Q)) (h0 : J % a = u) (h1 : J / a % A = fr) (h2 : J / (a * A) % p = v)
    (h3 : J / (a * A * p) % Q = fp) : J = (a * fr + u) + a * A * (p * fp + v) := by
  have hq : J / (a * A * p) < Q := by
    apply Nat.div_lt_of_lt_mul
    calc J < a * A * (p * Q) := hJ
      _ = a * A * p * Q := by ring
  rw [Nat.mod_eq_of_lt hq] at h3
  have e0 := Nat.mod_add_div J a
  have e1 := Nat.mod_add_div (J / a) A
  have e2 := Nat.mod_add_div (J / (a * A)) p
  rw [Nat.div_div_eq_div_mul] at e1 e2
  rw [h0] at e0
  rw [h1] at e1
  rw [h2, h3] at e2
  rw [← e0, ← e1, ← e2]
  ring


/-! ## One block -/

/-- The element's number within its block. -/
def numIn (b : LaidBlock) (i c : ℕ) : ℕ :=
  if b.iIsLow then (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI)
  else (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC)

theorem numIn_lt (b : LaidBlock) (i c : ℕ) (h : laidHolds b i c = true) :
    numIn b i c < 2 ^ b.bitsI * 2 ^ b.bitsC ∧ b.firstI + iOf b (numIn b i c) = i ∧
      b.firstC + cOf b (numIn b i c) = c := by
  unfold laidHolds at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  have hi : i - b.firstI < 2 ^ b.bitsI := by omega
  have hc : c - b.firstC < 2 ^ b.bitsC := by omega
  unfold numIn iOf cOf
  by_cases hl : b.iIsLow = true
  · simp only [hl, if_true]
    obtain ⟨d1, d2⟩ := digit (i - b.firstI) (2 ^ b.bitsI) (c - b.firstC) hi
    have e : (c - b.firstC) * 2 ^ b.bitsI + (i - b.firstI) =
        (i - b.firstI) + 2 ^ b.bitsI * (c - b.firstC) := by ring
    rw [e, d1, d2]
    refine ⟨?_, by omega, by omega⟩
    calc (i - b.firstI) + 2 ^ b.bitsI * (c - b.firstC)
        < 2 ^ b.bitsI + 2 ^ b.bitsI * (c - b.firstC) := by omega
      _ = 2 ^ b.bitsI * (c - b.firstC + 1) := by ring
      _ ≤ 2 ^ b.bitsI * 2 ^ b.bitsC := Nat.mul_le_mul_left _ hc
  · simp only [hl, if_false, Bool.false_eq_true]
    obtain ⟨d1, d2⟩ := digit (c - b.firstC) (2 ^ b.bitsC) (i - b.firstI) hc
    have e : (i - b.firstI) * 2 ^ b.bitsC + (c - b.firstC) =
        (c - b.firstC) + 2 ^ b.bitsC * (i - b.firstI) := by ring
    rw [e, d1, d2]
    refine ⟨?_, by omega, by omega⟩
    calc (c - b.firstC) + 2 ^ b.bitsC * (i - b.firstI)
        < 2 ^ b.bitsC + 2 ^ b.bitsC * (i - b.firstI) := by omega
      _ = 2 ^ b.bitsC * (i - b.firstI + 1) := by ring
      _ ≤ 2 ^ b.bitsC * 2 ^ b.bitsI := Nat.mul_le_mul_left _ hi
      _ = 2 ^ b.bitsI * 2 ^ b.bitsC := by ring

/-- A number is made again of its two halves. -/
theorem num_of_halves (b : LaidBlock) (x i c : ℕ) (hi : b.firstI + iOf b x = i)
    (hc : b.firstC + cOf b x = c) : x = numIn b i c := by
  subst hi
  subst hc
  unfold numIn iOf cOf
  by_cases hl : b.iIsLow = true
  · simp only [hl, if_true]
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact (Nat.div_add_mod' x _).symm
  · simp only [hl, if_false, Bool.false_eq_true]
    rw [Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
    exact (Nat.div_add_mod' x _).symm

/-- The table's index of a row and a place. -/
def tableIndex (R : ℕ) (rp : ℕ × ℕ) : ℕ := rp.1 + 2 ^ R * rp.2

section
variable {K : Type} [CommRing K]

/-- **ONE BLOCK: the sum that reads an element off a table is the table's entry at the row and place
at which the block lays the element.** -/
theorem cellOfBlock_holds (b : LaidBlock) (R P : ℕ) (F : BlockFacts b R P) (tab : ℕ → K) (i c : ℕ)
    (h : laidHolds b i c = true) :
    cellOfBlock b R P tab i c =
      tab (tableIndex R (VerifiableInference.Desc.First.Look.laidIn b i c)) := by
  obtain ⟨hx, hi, hc⟩ := numIn_lt b i c h
  -- the four radices
  have eR : 2 ^ R = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) := by
    rw [← pow_add, Nat.add_sub_cancel' F.hR]
  have eP : 2 ^ P = 2 ^ b.placeBits * 2 ^ (P - b.placeBits) := by
    rw [← pow_add, Nat.add_sub_cancel' F.hP]
  have exb : 2 ^ b.bitsI * 2 ^ b.bitsC = 2 ^ b.placeBits * 2 ^ b.rowBits := by
    rw [← pow_add, ← pow_add, ← F.hs, Nat.add_comm]
  have pa : 0 < 2 ^ b.rowBits := Nat.two_pow_pos _
  have pA : 0 < 2 ^ (R - b.rowBits) := Nat.two_pow_pos _
  have pp : 0 < 2 ^ b.placeBits := Nat.two_pow_pos _
  have pQ : 0 < 2 ^ (P - b.placeBits) := Nat.two_pow_pos _
  generalize hxx : numIn b i c = x at hx hi hc
  -- the digits
  have hv : x % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ pp
  have hu : x / 2 ^ b.placeBits < 2 ^ b.rowBits := by
    apply Nat.div_lt_of_lt_mul
    rw [← exb]
    exact hx
  have efr : b.firstRow = 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits) := by
    have := Nat.mod_add_div b.firstRow (2 ^ b.rowBits)
    rw [F.alRow, Nat.zero_add] at this
    exact this.symm
  have efp : b.firstPlace = 2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits) := by
    have := Nat.mod_add_div b.firstPlace (2 ^ b.placeBits)
    rw [F.alPlace, Nat.zero_add] at this
    exact this.symm
  have hfr : b.firstRow / 2 ^ b.rowBits < 2 ^ (R - b.rowBits) := by
    apply Nat.div_lt_of_lt_mul
    rw [← eR]
    exact F.rowLt
  have hfp : b.firstPlace / 2 ^ b.placeBits < 2 ^ (P - b.placeBits) := by
    apply Nat.div_lt_of_lt_mul
    rw [← eP]
    exact F.placeLt
  -- the index, in four digits
  have eJ : tableIndex R (VerifiableInference.Desc.First.Look.laidIn b i c) =
      (2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits) + x / 2 ^ b.placeBits) +
        2 ^ b.rowBits * 2 ^ (R - b.rowBits) *
          (2 ^ b.placeBits * (b.firstPlace / 2 ^ b.placeBits) + x % 2 ^ b.placeBits) := by
    show (b.firstRow + numIn b i c / 2 ^ b.placeBits) +
      2 ^ R * (b.firstPlace + numIn b i c % 2 ^ b.placeBits) = _
    rw [hxx, ← efr, ← efp, ← eR]
  obtain ⟨d0, d1, d2, d3, dlt⟩ := digits_at (2 ^ b.rowBits) (2 ^ (R - b.rowBits)) (2 ^ b.placeBits)
    (2 ^ (P - b.placeBits)) (b.firstRow / 2 ^ b.rowBits) (b.firstPlace / 2 ^ b.placeBits)
    (x / 2 ^ b.placeBits) (x % 2 ^ b.placeBits) hu hfr hv hfp
  rw [← eJ] at d0 d1 d2 d3 dlt
  generalize tableIndex R (VerifiableInference.Desc.First.Look.laidIn b i c) = J0 at eJ d0 d1 d2 d3 dlt ⊢
  have eRp : 2 ^ (R + b.placeBits) = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) * 2 ^ b.placeBits := by
    rw [pow_add, eR]
  have eRP : 2 ^ (R + P) = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) *
      (2 ^ b.placeBits * 2 ^ (P - b.placeBits)) := by
    rw [pow_add, eR, eP]
  unfold cellOfBlock
  rw [Finset.sum_eq_single J0]
  · -- at the index itself
    have hxo : xOf b R J0 = x := by
      unfold xOf
      rw [d0, eR, d2]
      exact Nat.div_add_mod x _
    have hin : (inBlock b R P J0 : K) = 1 := by
      unfold inBlock
      rw [d1, eRp, d3, Nat.mod_eq_of_lt hfr, Nat.mod_eq_of_lt hfp]
      simp
    rw [hin, hxo, if_pos ⟨hi, hc⟩, one_mul]
  · -- at every other index
    intro J hJ hne
    by_cases hcond : b.firstI + iOf b (xOf b R J) = i ∧ b.firstC + cOf b (xOf b R J) = c
    · have hxJ : xOf b R J = x := (num_of_halves b _ i c hcond.1 hcond.2).trans hxx
      by_cases h1 : J / 2 ^ b.rowBits % 2 ^ (R - b.rowBits) =
          b.firstRow / 2 ^ b.rowBits % 2 ^ (R - b.rowBits)
      · by_cases h3 : J / 2 ^ (R + b.placeBits) % 2 ^ (P - b.placeBits) =
            b.firstPlace / 2 ^ b.placeBits % 2 ^ (P - b.placeBits)
        · exfalso
          apply hne
          unfold xOf at hxJ
          have hj2 : J / 2 ^ R % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ pp
          obtain ⟨g1, g2⟩ := digit (J / 2 ^ R % 2 ^ b.placeBits) (2 ^ b.placeBits)
            (J % 2 ^ b.rowBits) hj2
          rw [Nat.add_comm, hxJ] at g1 g2
          rw [Nat.mod_eq_of_lt hfr] at h1
          rw [Nat.mod_eq_of_lt hfp, eRp] at h3
          rw [eR] at g1
          rw [eJ]
          exact digits_one _ _ _ _ _ _ _ _ J (by rw [← eRP]; exact Finset.mem_range.1 hJ) g2.symm h1
            g1.symm h3
        · unfold inBlock
          rw [if_neg h3, mul_zero, zero_mul]
      · unfold inBlock
        rw [if_neg h1, zero_mul, zero_mul]
    · rw [if_neg hcond, mul_zero]
  · intro hn
    exact absurd (Finset.mem_range.2 (by rw [eRP]; exact dlt)) hn

/-- The row at which a block lays an element that it holds is a row of the table. -/
theorem laidIn_row_lt (b : LaidBlock) (R P : ℕ) (F : BlockFacts b R P) (i c : ℕ)
    (h : laidHolds b i c = true) : (VerifiableInference.Desc.First.Look.laidIn b i c).1 < 2 ^ R := by
  obtain ⟨hx, _, _⟩ := numIn_lt b i c h
  have eR : 2 ^ R = 2 ^ b.rowBits * 2 ^ (R - b.rowBits) := by
    rw [← pow_add, Nat.add_sub_cancel' F.hR]
  have exb : 2 ^ b.bitsI * 2 ^ b.bitsC = 2 ^ b.placeBits * 2 ^ b.rowBits := by
    rw [← pow_add, ← pow_add, ← F.hs, Nat.add_comm]
  have hu : numIn b i c / 2 ^ b.placeBits < 2 ^ b.rowBits := by
    apply Nat.div_lt_of_lt_mul
    rw [← exb]
    exact hx
  have efr : b.firstRow = 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits) := by
    have := Nat.mod_add_div b.firstRow (2 ^ b.rowBits)
    rw [F.alRow, Nat.zero_add] at this
    exact this.symm
  have hfr : b.firstRow / 2 ^ b.rowBits < 2 ^ (R - b.rowBits) := by
    apply Nat.div_lt_of_lt_mul
    rw [← eR]
    exact F.rowLt
  show b.firstRow + numIn b i c / 2 ^ b.placeBits < 2 ^ R
  rw [efr, eR]
  calc 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits) + numIn b i c / 2 ^ b.placeBits
      < 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits) + 2 ^ b.rowBits := by omega
    _ = 2 ^ b.rowBits * (b.firstRow / 2 ^ b.rowBits + 1) := by ring
    _ ≤ 2 ^ b.rowBits * 2 ^ (R - b.rowBits) := Nat.mul_le_mul_left _ hfr

/-- The index of a row below 2 ^ R and a place gives them back. -/
theorem tableIndex_parts (R : ℕ) (rp : ℕ × ℕ) (h : rp.1 < 2 ^ R) :
    tableIndex R rp % 2 ^ R = rp.1 ∧ tableIndex R rp / 2 ^ R = rp.2 := digit rp.1 (2 ^ R) rp.2 h

/-- **ONE BLOCK, an element that it does not hold: the sum is 0.** -/
theorem cellOfBlock_not (b : LaidBlock) (R P : ℕ) (F : BlockFacts b R P) (tab : ℕ → K) (i c : ℕ)
    (h : laidHolds b i c = false) : cellOfBlock b R P tab i c = 0 := by
  unfold cellOfBlock
  refine Finset.sum_eq_zero fun J _ => ?_
  rw [if_neg, mul_zero]
  rintro ⟨hi, hc⟩
  have pp : 0 < 2 ^ b.placeBits := Nat.two_pow_pos _
  have pa : 0 < 2 ^ b.rowBits := Nat.two_pow_pos _
  have hx : xOf b R J < 2 ^ b.bitsI * 2 ^ b.bitsC := by
    have exb : 2 ^ b.bitsI * 2 ^ b.bitsC = 2 ^ b.placeBits * 2 ^ b.rowBits := by
      rw [← pow_add, ← pow_add, ← F.hs, Nat.add_comm]
    rw [exb]
    unfold xOf
    have h1 : J % 2 ^ b.rowBits < 2 ^ b.rowBits := Nat.mod_lt _ pa
    have h2 : J / 2 ^ R % 2 ^ b.placeBits < 2 ^ b.placeBits := Nat.mod_lt _ pp
    calc 2 ^ b.placeBits * (J % 2 ^ b.rowBits) + J / 2 ^ R % 2 ^ b.placeBits
        < 2 ^ b.placeBits * (J % 2 ^ b.rowBits) + 2 ^ b.placeBits := by omega
      _ = 2 ^ b.placeBits * (J % 2 ^ b.rowBits + 1) := by ring
      _ ≤ 2 ^ b.placeBits * 2 ^ b.rowBits := Nat.mul_le_mul_left _ h1
  have hI : iOf b (xOf b R J) < 2 ^ b.bitsI := by
    unfold iOf
    by_cases hl : b.iIsLow = true
    · simp only [hl, if_true]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
    · simp only [hl, if_false, Bool.false_eq_true]
      apply Nat.div_lt_of_lt_mul
      rw [Nat.mul_comm]
      exact hx
  have hC : cOf b (xOf b R J) < 2 ^ b.bitsC := by
    unfold cOf
    by_cases hl : b.iIsLow = true
    · simp only [hl, if_true]
      exact Nat.div_lt_of_lt_mul hx
    · simp only [hl, if_false, Bool.false_eq_true]
      exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have : laidHolds b i c = true := by
    unfold laidHolds
    simp only [Bool.and_eq_true, decide_eq_true_eq]
    omega
  rw [h] at this
  cases this

/-- Two blocks that hold one element meet, in the programs' sense. -/
theorem meet_of_holds (x y : LaidBlock) (i c : ℕ) (hx : laidHolds x i c = true)
    (hy : laidHolds y i c = true) :
    (laidMeet x.firstI x.bitsI y.firstI y.bitsI && laidMeet x.firstC x.bitsC y.firstC y.bitsC) =
      true := by
  unfold laidHolds at hx hy
  unfold laidMeet
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hx hy ⊢
  omega

/-- **A LIST OF BLOCKS, no two of which meet: the sum over the blocks is the table's entry at the
place at which the first block that holds the element lays it; 0 where none holds it.** -/
theorem blocks_sum (R P : ℕ) (tab : ℕ → K) (i c : ℕ) :
    ∀ l : List LaidBlock, (∀ b ∈ l, BlockFacts b R P) →
      noPair (fun (x y : LaidBlock) =>
        laidMeet x.firstI x.bitsI y.firstI y.bitsI && laidMeet x.firstC x.bitsC y.firstC y.bitsC)
        l = true →
      (l.map fun b => cellOfBlock b R P tab i c).sum =
        match laidPlace l i c with
        | some rp => tab (tableIndex R rp)
        | none => 0
  | [], _, _ => rfl
  | b :: l, hF, hn => by
    unfold noPair at hn
    obtain ⟨hn1, hn2⟩ := Eq.mp (Bool.and_eq_true _ _) hn
    have ih := blocks_sum R P tab i c l (fun x hx => hF x (List.mem_cons_of_mem _ hx)) hn2
    rw [List.map_cons, List.sum_cons]
    unfold laidPlace at ih ⊢
    rw [List.find?_cons]
    by_cases h : laidHolds b i c = true
    · rw [h, cellOfBlock_holds b R P (hF b List.mem_cons_self) tab i c h]
      have hz : (l.map fun b => cellOfBlock b R P tab i c).sum = 0 := by
        apply List.sum_eq_zero
        intro v hv
        obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hv
        apply cellOfBlock_not y R P (hF y (List.mem_cons_of_mem _ hy))
        by_contra hh
        have hy' : laidHolds y i c = true := by simpa using hh
        have := List.all_eq_true.1 hn1 y hy
        rw [meet_of_holds b y i c h hy'] at this
        cases this
      rw [hz, add_zero]
      rfl
    · have h' : laidHolds b i c = false := by simpa using h
      rw [h', cellOfBlock_not b R P (hF b List.mem_cons_self) tab i c h', zero_add]
      exact ih

/-- **(P2) THE DATA's CELL IS THE TABLE's ENTRY AT THE PLACE THAT THE LAYOUT GIVES IT**, under the
programs' own test on one array's layout. -/
theorem dataOf_cell (Rr : ReqRows) (f : ReqFrame) (S : Statement)
    (tab : ℕ → OnBytes.Part → ℕ → K) (born : ℕ) (name : String) (i c : ℕ) {a : ReqArray} {o : ℕ}
    (ha : reqArray Rr.layout born name = some a) (ho : f.whereIs born a.message = some o)
    (hok : laidMatrixOk a (S.rowBits o .main) (S.placeBits o .main) = true) :
    (dataOf Rr f S tab).cell born name i c =
      match laidPlace a.blocks i c with
      | some rp => tab o .main (tableIndex (S.rowBits o .main) rp)
      | none => 0 := by
  unfold laidMatrixOk at hok
  obtain ⟨hok1, _⟩ := Eq.mp (Bool.and_eq_true _ _) hok
  obtain ⟨hall, hno⟩ := Eq.mp (Bool.and_eq_true _ _) hok1
  show (match reqArray Rr.layout born name with
    | none => (0 : K)
    | some a =>
      match f.whereIs born a.message with
      | none => (0 : K)
      | some o => (a.blocks.map fun b =>
          cellOfBlock b (S.rowBits o .main) (S.placeBits o .main) (tab o .main) i c).sum) = _
  rw [ha]
  show (match f.whereIs born a.message with
      | none => (0 : K)
      | some o => (a.blocks.map fun b =>
          cellOfBlock b (S.rowBits o .main) (S.placeBits o .main) (tab o .main) i c).sum) = _
  rw [ho]
  refine blocks_sum _ _ (tab o .main) i c a.blocks (fun b hb => ?_) hno
  have h1 := List.all_eq_true.1 hall b hb
  obtain ⟨h2, _⟩ := Eq.mp (Bool.and_eq_true _ _) h1
  obtain ⟨h3, _⟩ := Eq.mp (Bool.and_eq_true _ _) h2
  exact blockFacts b _ _ h3

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.laidPlace_one
#print axioms VerifiableInference.Desc.First.Att.P.digits_at
#print axioms VerifiableInference.Desc.First.Att.P.digits_one
#print axioms VerifiableInference.Desc.First.Att.P.numIn_lt
#print axioms VerifiableInference.Desc.First.Att.P.num_of_halves
#print axioms VerifiableInference.Desc.First.Att.P.cellOfBlock_holds
#print axioms VerifiableInference.Desc.First.Att.P.laidIn_row_lt
#print axioms VerifiableInference.Desc.First.Att.P.tableIndex_parts
#print axioms VerifiableInference.Desc.First.Att.P.cellOfBlock_not
#print axioms VerifiableInference.Desc.First.Att.P.meet_of_holds
#print axioms VerifiableInference.Desc.First.Att.P.blocks_sum
#print axioms VerifiableInference.Desc.First.Att.P.dataOf_cell
