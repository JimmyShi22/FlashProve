-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/StretchLaws.lean: row weights that are written out on a stretch of rows, as the
verifier spells them in vectors of product form.

stretchInTheCube (OnBytes/Iop/Lin.lean) cuts a stretch of rows into aligned blocks of 2^d rows and
makes one vector for each block. This file shows what the vectors' entries read as: at each row of
the cube they add up to the value written for that row, and to 0 outside the stretch. That is the
statement StretchMeans of Johnson/Road/Rows/PendingPort.lean, which is a theorem with this file.

Main theorems.
 - denseIndex_run: the index within the written-out factor, for dense variables a, .., a + n - 1.
 - one_entry, block_entry: an entry of the vector of a block of one row, of 2^d rows.
 - blockBits_spec: the block is aligned, ends inside the stretch and has at most 2^kRow rows.
 - blocks_sum: the vectors of the blocks from a row on, as far as the fuel lasts.
 - stretchMeans: StretchMeans, for every reading. pending_port_free: pending_port without it.

What is not claimed. Every equation is between readings, not between the program's words. Nothing on
how the test on the matrix reads the vectors. The program does not import this file.


-/
import Johnson.Road.Rows.PendingPort
import OnBytes.Iop.TensorLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.Rows

open Finset
open OnBytes.Model (Reading WsLay WsClaim WsForkOut WsPending wsEpsT wsRowPart wsPending)

variable {K : Type} [Field K] (ρ : Reading K)

/-! ## The parts of a block's vector -/

/-- Pairs (1, 1) read as 1. -/
theorem pairsVal_ones (n j : ℕ) : pairsVal ρ (List.replicate n (oneE, oneE)) j = 1 := by
  induction n generalizing j with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, pairsVal, ih, mul_one]
    split <;> exact ρ.one

omit [Field K] in
/-- The index within the written-out factor, for the dense variables a, .., a + n - 1. -/
theorem denseIndex_run (n a i j : ℕ) :
    denseIndex (List.range' a n) i j = j / 2 ^ a % 2 ^ n * 2 ^ i := by
  induction n generalizing a i with
  | zero => simp [denseIndex, Nat.mod_one]
  | succ n ih =>
    rw [List.range'_succ, denseIndex, ih, Nat.pow_succ' (n := n), mod_two_mul,
      Nat.div_div_eq_div_mul, ← Nat.pow_succ]
    simp only [Nat.succ_eq_add_one]
    ring

omit [Field K] in
/-- The dense variables that pushDense gives the empty vector. -/
theorem dense_empty (d : ℕ) : (({} : Tensor).pushDense d).denseVars = List.range' 0 d := by
  show [] ++ (List.range d).map (· + 0) = _
  rw [List.nil_append, List.range_eq_range']
  simp

/-- An entry of the vector of a block of one row. -/
theorem one_entry (kRow start J : ℕ) (x : E) (hs : start < 2 ^ kRow) (hJ : J < 2 ^ kRow) :
    ρ.val ((({ scalar := x } : Tensor).insertChoice 0 kRow start).entry J) =
      if J = start then ρ.val x else 0 := by
  rw [Tensor.entry_insertChoice ρ _ 0 kRow start J (Nat.zero_le _), pow_zero, Nat.div_one,
    Nat.mod_eq_of_lt hJ, Nat.mod_eq_of_lt hs]
  have e : ρ.val (({ scalar := x } : Tensor).entry (unshift 0 kRow J)) = ρ.val x := rfl
  rw [e]
  split <;> simp

/-- An entry of the vector of an aligned block of 2^d rows, d above 0. -/
theorem block_entry (kRow d start off J : ℕ) (values : Array E) (hd0 : 0 < d) (hd : d ≤ kRow)
    (hal : 2 ^ d ∣ start) (hs : start < 2 ^ kRow) (hJ : J < 2 ^ kRow) :
    ρ.val (((((({} : Tensor).pushDense d).insertChoice d (kRow - d) (start / 2 ^ d)).setValues
        values off)).entry J) =
      if start ≤ J ∧ J < start + 2 ^ d then ρ.val (values.getD (off + (J - start)) zeroE)
      else 0 := by
  have e0 : ((({} : Tensor).pushDense d).insertChoice d (kRow - d) (start / 2 ^ d)).setValues
      values off =
      ((({} : Tensor).pushDense d).setValues values off).insertChoice d (kRow - d)
        (start / 2 ^ d) := rfl
  have hv : ((({} : Tensor).pushDense d).setValues values off).vars = d := by
    show ([] ++ List.replicate d (oneE, oneE)).length = d
    simp
  have hp : (2 : ℕ) ^ kRow = 2 ^ d * 2 ^ (kRow - d) := by
    rw [← pow_add]
    congr 1
    omega
  have h1 : J / 2 ^ d < 2 ^ (kRow - d) := Nat.div_lt_of_lt_mul (by rw [← hp]; exact hJ)
  have h2 : start / 2 ^ d < 2 ^ (kRow - d) := Nat.div_lt_of_lt_mul (by rw [← hp]; exact hs)
  rw [e0, Tensor.entry_insertChoice ρ _ d (kRow - d) (start / 2 ^ d) J (le_of_eq hv.symm),
    Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2, Tensor.entry_val]
  have hs1 : ρ.val ((({} : Tensor).pushDense d).setValues values off).scalar = 1 := ρ.one
  have hs2 : pairsVal ρ ((({} : Tensor).pushDense d).setValues values off).pairs
      (unshift d (kRow - d) J) = 1 := by
    show pairsVal ρ ([] ++ List.replicate d (oneE, oneE)) _ = 1
    rw [List.nil_append, pairsVal_ones]
  have hne : ((({} : Tensor).pushDense d).setValues values off).denseVars.isEmpty = false := by
    show (({} : Tensor).pushDense d).denseVars.isEmpty = false
    rw [dense_empty]
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    rfl
  have hs3 : ((({} : Tensor).pushDense d).setValues values off).denseVal ρ
      (unshift d (kRow - d) J) = ρ.val (values.getD (off + J % 2 ^ d) zeroE) := by
    unfold Tensor.denseVal
    rw [hne]
    show ρ.val (values.getD (off + denseIndex (({} : Tensor).pushDense d).denseVars 0
      (unshift d (kRow - d) J)) zeroE) = _
    rw [dense_empty, denseIndex_run, pow_zero, Nat.div_one, Nat.mul_one, unshift_mod]
  rw [hs1, hs2, hs3, one_mul, one_mul]
  obtain ⟨q, rfl⟩ := hal
  have hq : 2 ^ d * q / 2 ^ d = q := Nat.mul_div_cancel_left _ (Nat.two_pow_pos d)
  have hdm := Nat.div_add_mod J (2 ^ d)
  have hml := Nat.mod_lt J (Nat.two_pow_pos d)
  rw [hq]
  by_cases hc : J / 2 ^ d = q
  · rw [if_pos hc, one_mul]
    rw [hc] at hdm
    rw [if_pos ⟨by omega, by omega⟩]
    congr 3
    omega
  · rw [if_neg hc, zero_mul, if_neg]
    rintro ⟨c1, c2⟩
    apply hc
    have a1 : q ≤ J / 2 ^ d := (Nat.le_div_iff_mul_le (Nat.two_pow_pos d)).mpr (by
      rw [Nat.mul_comm]
      exact c1)
    have a2 : J / 2 ^ d < q + 1 := Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_add, Nat.mul_one]
      exact c2)
    omega

/-! ## The blocks -/

omit [Field K] in
/-- The block that blockBits finds: aligned, inside the stretch, of at most 2^kRow rows. -/
theorem blockBits_spec (kRow start stop : ℕ) : ∀ (fuel d : ℕ), d ≤ kRow → 2 ^ d ∣ start →
    start + 2 ^ d ≤ stop →
    blockBits kRow start stop fuel d ≤ kRow ∧ 2 ^ blockBits kRow start stop fuel d ∣ start ∧
      start + 2 ^ blockBits kRow start stop fuel d ≤ stop
  | 0, d, h1, h2, h3 => ⟨h1, h2, h3⟩
  | fuel + 1, d, h1, h2, h3 => by
    unfold blockBits
    split
    · rename_i hc
      have hc' : (d < kRow ∧ start % 2 ^ (d + 1) = 0) ∧ start + 2 ^ (d + 1) ≤ stop := by
        simpa using hc
      exact blockBits_spec kRow start stop fuel (d + 1) hc'.1.1
        (Nat.dvd_of_mod_eq_zero hc'.1.2) hc'.2
    · exact ⟨h1, h2, h3⟩

/-- The vector of the block of 2^d rows from the row start on, as stretchBlocks makes it. -/
def blockOf (kRow firstRow : ℕ) (values : Array E) (start d : ℕ) : Tensor :=
  if d == 0 then
    ({ scalar := values.getD (start - firstRow) zeroE } : Tensor).insertChoice 0 kRow start
  else
    ((({} : Tensor).pushDense d).insertChoice d (kRow - d) (start / 2 ^ d)).setValues values
      (start - firstRow)

omit [Field K] in
/-- It has d dense variables. -/
theorem blockOf_dense (kRow firstRow : ℕ) (values : Array E) (start d : ℕ) :
    (blockOf kRow firstRow values start d).denseVars.length = d := by
  unfold blockOf
  by_cases h : d = 0
  · subst h
    rfl
  · rw [if_neg (by simpa using h)]
    show ((({} : Tensor).pushDense d).denseVars.map _).length = d
    rw [List.length_map, dense_empty, List.length_range']

/-- An entry of a block's vector. -/
theorem blockOf_entry (kRow firstRow : ℕ) (values : Array E) (start d J : ℕ) (hf : firstRow ≤ start)
    (hd : d ≤ kRow) (hal : 2 ^ d ∣ start) (hs : start < 2 ^ kRow) (hJ : J < 2 ^ kRow) :
    ρ.val ((blockOf kRow firstRow values start d).entry J) =
      if start ≤ J ∧ J < start + 2 ^ d then ρ.val (values.getD (J - firstRow) zeroE) else 0 := by
  unfold blockOf
  by_cases h : d = 0
  · subst h
    rw [if_pos (show ((0 : ℕ) == 0) = true from rfl), one_entry ρ kRow start J _ hs hJ, pow_zero]
    by_cases hc : J = start
    · rw [if_pos hc, if_pos ⟨by omega, by omega⟩, hc]
    · rw [if_neg hc, if_neg (by omega)]
  · rw [if_neg (by simpa using h),
      block_entry ρ kRow d start (start - firstRow) J values (by omega) hd hal hs hJ]
    by_cases hc : start ≤ J ∧ J < start + 2 ^ d
    · rw [if_pos hc, if_pos hc]
      congr 3
      omega
    · rw [if_neg hc, if_neg hc]

omit [Field K] in
/-- One step of stretchBlocks. -/
theorem stretchBlocks_succ (kRow firstRow : ℕ) (values : Array E) (fuel start : ℕ) :
    stretchBlocks kRow firstRow values (fuel + 1) start =
      if firstRow + values.size ≤ start then []
      else blockOf kRow firstRow values start
          (blockBits kRow start (firstRow + values.size) kRow 0) ::
        stretchBlocks kRow firstRow values fuel
          (start + 2 ^ blockBits kRow start (firstRow + values.size) kRow 0) := rfl

/-- The vectors of the blocks from the row start on, as far as the fuel lasts: they cover a run of
rows that begins at start and ends inside the stretch, and at each row of the cube their entries add
up to the value written for the row if the row is in that run, and to 0 otherwise. -/
theorem blocks_sum (kRow firstRow : ℕ) (values : Array E)
    (hN : firstRow + values.size ≤ 2 ^ kRow) : ∀ (fuel start : ℕ), firstRow ≤ start →
    start ≤ firstRow + values.size →
    start + ((stretchBlocks kRow firstRow values fuel start).map
        fun t => 2 ^ t.denseVars.length).sum ≤ firstRow + values.size ∧
    ∀ J, J < 2 ^ kRow → pendWeight ρ (stretchBlocks kRow firstRow values fuel start) J =
      if start ≤ J ∧ J < start + ((stretchBlocks kRow firstRow values fuel start).map
          fun t => 2 ^ t.denseVars.length).sum
      then ρ.val (values.getD (J - firstRow) zeroE) else 0
  | 0, start, _, h2 => by
    refine ⟨by simpa [stretchBlocks] using h2, fun J _ => ?_⟩
    have e : stretchBlocks kRow firstRow values 0 start = [] := rfl
    rw [e, if_neg (by simp)]
    rfl
  | fuel + 1, start, h1, h2 => by
    rw [stretchBlocks_succ]
    by_cases hc : firstRow + values.size ≤ start
    · rw [if_pos hc]
      refine ⟨by simpa using h2, fun J _ => ?_⟩
      rw [if_neg (by simp)]
      rfl
    · rw [if_neg hc]
      obtain ⟨b1, b2, b3⟩ := blockBits_spec kRow start (firstRow + values.size) kRow 0
        (Nat.zero_le _) (by simp) (by rw [pow_zero]; omega)
      generalize blockBits kRow start (firstRow + values.size) kRow 0 = d at b1 b2 b3 ⊢
      obtain ⟨i1, i2⟩ := blocks_sum kRow firstRow values hN fuel (start + 2 ^ d) (by omega) b3
      generalize stretchBlocks kRow firstRow values fuel (start + 2 ^ d) = rest at i1 i2 ⊢
      rw [List.map_cons, List.sum_cons, blockOf_dense]
      generalize (rest.map fun t => 2 ^ t.denseVars.length).sum = cov at i1 i2 ⊢
      refine ⟨by omega, fun J hJ => ?_⟩
      have e : pendWeight ρ (blockOf kRow firstRow values start d :: rest) J =
          ρ.val ((blockOf kRow firstRow values start d).entry J) + pendWeight ρ rest J := by
        unfold pendWeight
        rw [List.map_cons, List.sum_cons]
      have hp := Nat.two_pow_pos d
      rw [e, blockOf_entry ρ kRow firstRow values start d J h1 b1 b2 (by omega) hJ, i2 J hJ]
      by_cases c1 : start ≤ J ∧ J < start + 2 ^ d
      · rw [if_pos c1, if_neg (by omega), add_zero, if_pos ⟨c1.1, by omega⟩]
      · rw [if_neg c1, zero_add]
        by_cases c2 : start + 2 ^ d ≤ J ∧ J < start + 2 ^ d + cov
        · rw [if_pos c2, if_pos ⟨by omega, by omega⟩]
        · rw [if_neg c2, if_neg (by omega)]

/-- StretchMeans holds for every reading. -/
theorem stretchMeans : StretchMeans ρ := by
  intro kRow first values g hg J hJ
  unfold stretchInTheCube at hg
  split at hg
  · rename_i hc
    have hc' : kRow < 63 ∧ first + values.size ≤ 2 ^ kRow := by simpa using hc
    try dsimp only at hg
    split at hg
    · rename_i hs
      have hs' : ((stretchBlocks kRow first values (2 * kRow + 2) first).map
          fun t => 2 ^ t.denseVars.length).sum = values.size := by simpa using hs
      have e : stretchBlocks kRow first values (2 * kRow + 2) first = g := Option.some.inj hg
      have h := (blocks_sum ρ kRow first values hc'.2 (2 * kRow + 2) first (le_refl _)
        (Nat.le_add_right _ _)).2 J hJ
      rw [hs', e] at h
      exact h
    · cases hg
  · cases hg

/-- What wsPending returns, against the merge's function at its point, with no hypothesis on the
spelling of the stretch. -/
theorem pending_port_free (hρ : Numerals ρ) (lay : WsLay) (M : Wm K) (o : WsForkOut) (claims : ℕ)
    (S : Params.LinShape) (cr : List (WsClaim × E))
    (ho : o.recs = cr.map fun y => wsRowPart lay y.1 (mulE y.2 (wsEpsT lay y.1 o.rm)))
    {w : WsPending} (h : wsPending lay o claims S = .ok w) :
    w.psi = o.rm.toList.reverse ∧ w.beta = o.beta ∧ w.target = o.fvp ∧
      ∑ j ∈ range (2 ^ S.kRow), pendWeight ρ w.g j * rowAt ρ lay.lk o.rm M j =
        fmAt ρ lay M cr o.rm :=
  pending_port hρ (stretchMeans ρ) lay M o claims S cr ho h

end OnBytes.Road.Rows
