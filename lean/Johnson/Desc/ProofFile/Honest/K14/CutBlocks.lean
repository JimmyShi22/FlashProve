-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K14/CutBlocks.lean: kind K14: EACH BLOCK OF A STRETCH OF ROWS THAT
ENDS BELOW A LENGTH COMES BACK UNCUT FROM THE LIBRARY's tensorBelow (OnBytes/Iop/Tensor.lean),
WHATEVER ITS VALUES. Statements with their proofs. No definition: the one that they take is
BlockForm (Honest/K14/BlockForm.lean). The library's tensorBelow, stretchBlocks, choicePairs and
linDotRow are called, not written anew.

Why. "K14, second part" (the place ⟨3, none, 0, .K14⟩) asks that each of the weights can be cut
below the matrix's rows (the fourth of the five tests of secondRest5, Honest/K14/OmegaJoin.lean),
and makes the row (Dot) of what the cuts return.

  foldPow_all, foldPow_mono, foldPow_le, choiceSum_le   on the sum of powers of two in tensorBelow's
                  first short cut
  cut_whole       where the length is 2 ^ count, or that short cut answers, tensorBelow returns the
                  vector as it is
  form_vars, form_uncut   **a vector of a block's form that ends below the length comes back
                  uncut**: no value is read: not its scalar, not its written-out values
  blockOf_form, stretch_form   **THE LAW THAT TIES BlockForm TO THE LIBRARY's MAKER**: each vector
                  that stretchBlocks returns has the form, and does not reach beyond the stretch's
                  end (nothing is said on where it begins)
  form_scale      a vector times an element keeps the form
  varsTest_blocks, cuts_blocks, cutTest_blocks, dot_blocks   at weights that each have a block's
                  form and do not reach beyond the matrix's rows: **the third test's Bool is true
                  (each weight has kRow variables); what the cuts return: each weight as it is; the
                  fourth test's Bool is true; the row (Dot) is made of the weights as they are**
  blocks_scaled, varsTest_stretches, cutTest_stretches, dot_stretches   **the same at the library's
                  own blocks, each times an element**: the weights are vectors that stretchBlocks
                  returns of stretches whose last row is below the matrix's rows, each times an
                  element

The two Bools are written here as they stand in secondRest5. This file does not import that file;
rest5_of_three (Honest/K14/SecondBlocks.lean) lays these statements where secondRest5 asks the two.

THE PREMISES CAN BE MET. An example calls form_uncut at a block of two rows among eight. Five #guard
commands evaluate the library's stretchBlocks at a stretch of three rows: it returns two blocks;
each comes back as one vector where the stretch ends below the length, also times an element; the
first cannot be cut where it crosses the length; and the second, where it lies wholly at or beyond
the length, comes back as NO vector, without a rejection.

What stays a premise. THAT THE WEIGHTS OF A RUN ARE SUCH BLOCKS, EACH TIMES AN ELEMENT: no maker of
the weights of a run is named in a statement of this file. In dot_blocks and dot_stretches: the
shared point's length.

THE CONVERSE DOES NOT HOLD. The fourth test's Bool is also true at a block that lies wholly at or
beyond the matrix's rows: tensorBelow's second short cut drops it (the library says so at
memberWeightsOnRows, OnBytes/Iop/Lin.lean); and at a vector all of whose variables are written out:
it comes back cut. So a true test does not show that the weights do not reach beyond the rows.

What is not claimed. The fifth test of secondRest5 ("the terms fit their places"): dot_blocks says
which row linDotRow returns, not that the row's terms fit; and in secondRest5 that test stands
behind the return of takeOver, of which nothing is said here. The first two tests of secondRest5.
That the sub-protocol accepts. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K14.BlockForm
import Johnson.Road.Rows.StretchLaws
import OnBytes.Iop.TensorLaws
import OnBytes.Slice.ProgCodes

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K14
open OnBytes OnBytes.Params
open OnBytes.Road.Rows (blockOf stretchBlocks_succ blockBits_spec dense_empty)

/-! ## Sums of powers of two -/

/-- A sum of powers of two over the variables at which a test is true, where it is true at each: all
powers below 2 ^ n. -/
theorem foldPow_all (c : Nat → Bool) (n a : Nat) (h : ∀ t < n, c t = true) :
    (List.range n).foldl (fun s t => if c t then s + 2 ^ t else s) a = a + (2 ^ n - 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, ih fun t ht => h t (Nat.lt_succ_of_lt ht)]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    simp only [List.foldl_cons, List.foldl_nil, h n (Nat.lt_succ_self n), if_true, Nat.pow_succ]
    omega

/-- The same sum at two tests of which the first is true only where the second is: the first sum is
at most the second. -/
theorem foldPow_mono (c c' : Nat → Bool) (n a a' : Nat) (ha : a ≤ a')
    (h : ∀ t < n, c t = true → c' t = true) :
    (List.range n).foldl (fun s t => if c t then s + 2 ^ t else s) a ≤
      (List.range n).foldl (fun s t => if c' t then s + 2 ^ t else s) a' := by
  induction n with
  | zero => exact ha
  | succ n ih =>
    have ih' := ih fun t ht => h t (Nat.lt_succ_of_lt ht)
    rw [List.range_succ, List.foldl_append, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil]
    cases hc : c n
    · cases hc' : c' n
      · simpa using ih'
      · simp only [Bool.false_eq_true, if_false, if_true]
        exact Nat.le_trans ih' (Nat.le_add_right _ _)
    · rw [h n (Nat.lt_succ_self n) hc]
      simp only [if_true]
      exact Nat.add_le_add_right ih' _

/-- So at any test the sum is at most all powers below 2 ^ n. -/
theorem foldPow_le (c : Nat → Bool) (n a : Nat) :
    (List.range n).foldl (fun s t => if c t then s + 2 ^ t else s) a ≤ a + (2 ^ n - 1) :=
  Nat.le_trans (foldPow_mono c (fun _ => true) n a a (Nat.le_refl a) fun _ _ _ => rfl)
    (Nat.le_of_eq (foldPow_all (fun _ => true) n a fun _ _ => rfl))

/-- Of the pairs that pick the number q, those with an upper half other than 0: the sum of their
powers of two, counted from 2 ^ off on, is at most 2 ^ off * q. -/
theorem choiceSum_le : ∀ (m q off a : Nat),
    (List.range m).foldl (fun s j =>
      if !isZeroE ((choicePairs m q).getD j (zeroE, zeroE)).2 then s + 2 ^ (off + j) else s) a ≤
      a + 2 ^ off * q
  | 0, _, _, a => Nat.le_add_right a _
  | m + 1, q, off, a => by
    have h1 : isZeroE oneE = false := by decide
    have h0 : isZeroE zeroE = true := by decide
    have hP : 2 ^ (off + 1) * (q / 2) + 2 ^ off * (q % 2) = 2 ^ off * q := by
      rw [Nat.pow_succ, Nat.mul_assoc, ← Nat.mul_add, Nat.div_add_mod]
    have hfun : (fun (s j : Nat) =>
        if !isZeroE ((choicePairs (m + 1) q).getD (j + 1) (zeroE, zeroE)).2 then
          s + 2 ^ (off + (j + 1)) else s) =
        fun s j => if !isZeroE ((choicePairs m (q / 2)).getD j (zeroE, zeroE)).2 then
          s + 2 ^ (off + 1 + j) else s := by
      funext s j
      rw [show off + (j + 1) = off + 1 + j by omega]
      rfl
    have hhead : (choicePairs (m + 1) q).getD 0 (zeroE, zeroE) =
        if q % 2 == 1 then (zeroE, oneE) else (oneE, zeroE) := rfl
    rw [List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    show (List.range m).foldl (fun s j =>
        if !isZeroE ((choicePairs (m + 1) q).getD (j + 1) (zeroE, zeroE)).2 then
          s + 2 ^ (off + (j + 1)) else s)
      (if !isZeroE ((choicePairs (m + 1) q).getD 0 (zeroE, zeroE)).2 then a + 2 ^ off
        else a) ≤ a + 2 ^ off * q
    rw [hfun, hhead]
    by_cases hq : q % 2 = 1
    · have ih := choiceSum_le m (q / 2) (off + 1) (a + 2 ^ off)
      rw [hq, Nat.mul_one] at hP
      have hh : (if q % 2 == 1 then (zeroE, oneE) else (oneE, zeroE) : E × E) = (zeroE, oneE) := by
        rw [hq]
        rfl
      have hc : (!isZeroE ((zeroE, oneE) : E × E).2) = true := by
        show (!isZeroE oneE) = true
        rw [h1]
        rfl
      rw [hh, if_pos hc]
      omega
    · have ih := choiceSum_le m (q / 2) (off + 1) a
      have hq0 : q % 2 = 0 := by omega
      rw [hq0, Nat.mul_zero, Nat.add_zero] at hP
      have hh : (if q % 2 == 1 then (zeroE, oneE) else (oneE, zeroE) : E × E) = (oneE, zeroE) := by
        rw [hq0]
        rfl
      have hc : ¬ (!isZeroE ((oneE, zeroE) : E × E).2) = true := by
        show ¬ (!isZeroE zeroE) = true
        rw [h0]
        decide
      rw [hh, if_neg hc]
      omega

/-! ## A vector that comes back as it is -/

/-- **Where the length is 2 ^ count, or the first short cut answers, the vector comes back as it
is.** The long term is the library's own: the greatest number that the index of an entry other than
0 can give. -/
theorem cut_whole (v : Tensor) (start count len : Nat) (hv : start + count ≤ v.vars)
    (hl : len ≤ 2 ^ count)
    (h : len = 2 ^ count ∨
      (List.range count).foldl (fun s t => if v.denseVars.contains (start + t) ||
        !isZeroE (v.pairs.getD (start + t) (zeroE, zeroE)).2 then s + 2 ^ t else s) 0 < len) :
    tensorBelow v start count len = some [v] := by
  unfold tensorBelow
  dsimp only
  split
  · rename_i h1
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h1
    omega
  · split
    · rfl
    · rename_i h2
      split
      · rfl
      · rename_i h3
        rcases h with h | h
        · exact absurd (beq_iff_eq.2 h) h2
        · exact absurd h h3

/-- A vector of a block's form has kRow variables. -/
theorem form_vars {kRow d q : Nat} {w : Tensor} (hw : BlockForm kRow d q w) (hd : d ≤ kRow) :
    w.vars = kRow := by
  unfold Tensor.vars
  rw [hw.1, List.length_append, List.length_replicate, choicePairs_length]
  omega

/-- **A vector of a block's form that ends below the length comes back uncut**, whatever its scalar
and its written-out values. -/
theorem form_uncut (kRow d q len : Nat) (w : Tensor) (hw : BlockForm kRow d q w) (hd : d ≤ kRow)
    (hq : 2 ^ d * q + 2 ^ d ≤ len) (hl : len ≤ 2 ^ kRow) :
    tensorBelow w 0 kRow len = some [w] := by
  refine cut_whole w 0 kRow len (by rw [form_vars hw hd]; omega) hl (Or.inr ?_)
  rw [hw.1, hw.2]
  obtain ⟨m, rfl⟩ : ∃ m, kRow = d + m := ⟨kRow - d, by omega⟩
  rw [Nat.add_sub_cancel_left, List.range_add, List.foldl_append, List.foldl_map]
  have hf : (fun (s j : Nat) => if (List.range' 0 d).contains (0 + (d + j)) ||
        !isZeroE ((List.replicate d (oneE, oneE) ++ choicePairs m q).getD (0 + (d + j))
          (zeroE, zeroE)).2 then s + 2 ^ (d + j) else s) =
      fun s j => if !isZeroE ((choicePairs m q).getD j (zeroE, zeroE)).2 then s + 2 ^ (d + j)
        else s := by
    funext s j
    have hc : (List.range' 0 d).contains (0 + (d + j)) = false := by
      simp [List.mem_range'_1]
    have hg : (List.replicate d (oneE, oneE) ++ choicePairs m q).getD (0 + (d + j))
        (zeroE, zeroE) = (choicePairs m q).getD j (zeroE, zeroE) := by
      rw [List.getD_append_right _ _ _ _ (by rw [List.length_replicate]; omega),
        List.length_replicate]
      congr 1
      omega
    rw [hc, hg, Bool.false_or]
  rw [hf]
  have h1 := foldPow_le (fun t => (List.range' 0 d).contains (0 + t) ||
    !isZeroE ((List.replicate d (oneE, oneE) ++ choicePairs m q).getD (0 + t) (zeroE, zeroE)).2) d 0
  have h2 := choiceSum_le m q d ((List.range d).foldl (fun s t =>
    if (List.range' 0 d).contains (0 + t) ||
      !isZeroE ((List.replicate d (oneE, oneE) ++ choicePairs m q).getD (0 + t) (zeroE, zeroE)).2
    then s + 2 ^ t else s) 0)
  have h3 : 1 ≤ 2 ^ d := Nat.one_le_two_pow
  omega

/-! ## The library's blocks have that form -/

/-- The library's vector of one block has the form. -/
theorem blockOf_form (kRow firstRow : Nat) (values : Array E) (start d : Nat) :
    BlockForm kRow d (start / 2 ^ d) (blockOf kRow firstRow values start d) := by
  unfold blockOf
  by_cases h : d = 0
  · subst h
    rw [if_pos (show ((0 : Nat) == 0) = true from rfl)]
    refine ⟨?_, rfl⟩
    simp [Tensor.insertChoice]
  · rw [if_neg (by simpa using h)]
    refine ⟨?_, ?_⟩
    · simp [Tensor.setValues, Tensor.insertChoice, Tensor.pushDense]
    · show ((({} : Tensor).pushDense d).denseVars.map fun x =>
        if d ≤ x then x + (kRow - d) else x) = List.range' 0 d
      rw [dense_empty]
      conv_rhs => rw [← List.map_id (List.range' 0 d)]
      apply List.map_congr_left
      intro x hx
      have := List.mem_range'_1.1 hx
      rw [if_neg (by omega)]
      rfl

/-- **Each vector that the library's maker of a stretch's blocks returns has the form, and does not
reach beyond the stretch's end.** -/
theorem stretch_form (kRow firstRow : Nat) (values : Array E) : ∀ (fuel start : Nat),
    ∀ t ∈ stretchBlocks kRow firstRow values fuel start,
      ∃ d q, d ≤ kRow ∧ BlockForm kRow d q t ∧ 2 ^ d * q + 2 ^ d ≤ firstRow + values.size
  | 0, _, _, ht => by cases ht
  | fuel + 1, start, t, ht => by
    rw [stretchBlocks_succ] at ht
    split at ht
    · cases ht
    · rename_i hs
      rcases List.mem_cons.1 ht with rfl | ht'
      · obtain ⟨h1, _, h3⟩ := blockBits_spec kRow start (firstRow + values.size) kRow 0
          (Nat.zero_le _) (by simp) (by simp; omega)
        refine ⟨_, _, h1, blockOf_form kRow firstRow values start _, ?_⟩
        have := Nat.mul_div_le start (2 ^ blockBits kRow start (firstRow + values.size) kRow 0)
        omega
      · exact stretch_form kRow firstRow values fuel _ t ht'

/-- A vector times an element keeps the form. -/
theorem form_scale {kRow d q : Nat} {w : Tensor} (h : BlockForm kRow d q w) (x : E) :
    BlockForm kRow d q (w.scale x) := by
  have h1 : (w.scale x).pairs = w.pairs := by unfold Tensor.scale; rfl
  have h2 : (w.scale x).denseVars = w.denseVars := by unfold Tensor.scale; rfl
  exact ⟨h1.trans h.1, h2.trans h.2⟩

/-! ## The test, and the row (Dot) -/

/-- **The third test's Bool** ("the weights have as many variables as a row's number has bits") **is
true** at weights that each have a block's form. -/
theorem varsTest_blocks (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ d q, d ≤ S.kRow ∧ BlockForm S.kRow d q w ∧
      2 ^ d * q + 2 ^ d ≤ S.matrixRows) :
    g.all (·.vars == S.kRow) = true := by
  simp only [beq_iff_eq, List.all_eq_true]
  intro x hx
  obtain ⟨d, q, hd, hf, _⟩ := h x hx
  exact form_vars hf hd

/-- **What the cuts return**: at weights that each have a block's form and do not reach beyond the
matrix's rows: each weight as it is. -/
theorem cuts_blocks (S : LinShape) : ∀ (g : List Tensor),
    (∀ w ∈ g, ∃ d q, d ≤ S.kRow ∧ BlockForm S.kRow d q w ∧ 2 ^ d * q + 2 ^ d ≤ S.matrixRows) →
    (g.mapM fun w => tensorBelow w 0 S.kRow S.matrixRows) = some (g.map fun w => [w])
  | [], _ => rfl
  | w :: g, h => by
    obtain ⟨d, q, hd, hw, hq⟩ := h w List.mem_cons_self
    have h1 := form_uncut S.kRow d q S.matrixRows w hw hd hq (OnBytes.Slice.le_two_pow_ceilLog2 _)
    have h2 := cuts_blocks S g fun x hx => h x (List.mem_cons_of_mem _ hx)
    simp [List.mapM_cons, h1, h2]

/-- **The fourth test's Bool** ("each of the weights can be cut below the matrix's rows") **is
true** at such weights. -/
theorem cutTest_blocks (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ d q, d ≤ S.kRow ∧ BlockForm S.kRow d q w ∧
      2 ^ d * q + 2 ^ d ≤ S.matrixRows) :
    (g.all fun w => (tensorBelow w 0 S.kRow S.matrixRows).isSome) = true := by
  rw [List.all_eq_true]
  intro w hw
  obtain ⟨d, q, hd, hf, hq⟩ := h w hw
  rw [form_uncut S.kRow d q S.matrixRows w hf hd hq (OnBytes.Slice.le_two_pow_ceilLog2 _)]
  rfl

/-- **So the row (Dot) is made, of the weights as they are.** -/
theorem dot_blocks (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ d q, d ≤ S.kRow ∧ BlockForm S.kRow d q w ∧
      2 ^ d * q + 2 ^ d ≤ S.matrixRows)
    (psi : List E) (hp : psi.length = S.kCol) (omega : Nat) (omegaLay : VectorLay) (w : Nat)
    (wLay : VectorLay) :
    linDotRow S g psi omega omegaLay w wLay =
      some (addLaid (addLaid {} omega omegaLay g) w wLay [Tensor.eq psi (negE oneE)]) := by
  have hg : (psi.length == S.kCol && g.all (·.vars == S.kRow)) = true := by
    rw [varsTest_blocks S g h, Bool.and_true, beq_iff_eq]
    exact hp
  have hfl : (g.map fun w => [w]).flatten = g := by
    rw [← List.flatMap_def]
    exact List.flatMap_singleton' g
  unfold linDotRow
  simp [guard, hg, cuts_blocks S g h, hfl]

/-- **At the library's own blocks, each times an element**: each weight is a vector that
stretchBlocks returns of a stretch that does not reach beyond the matrix's rows, times an element:
the premise of the statements at BlockForm holds. -/
theorem blocks_scaled (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (x : E),
      firstRow + values.size ≤ S.matrixRows ∧
        ∃ t ∈ stretchBlocks S.kRow firstRow values fuel start, w = t.scale x) :
    ∀ w ∈ g, ∃ d q, d ≤ S.kRow ∧ BlockForm S.kRow d q w ∧ 2 ^ d * q + 2 ^ d ≤ S.matrixRows := by
  intro w hw
  obtain ⟨firstRow, values, fuel, start, x, hm, t, ht, rfl⟩ := h w hw
  obtain ⟨d, q, hd, hf, hq⟩ := stretch_form S.kRow firstRow values fuel start t ht
  exact ⟨d, q, hd, form_scale hf x, Nat.le_trans hq hm⟩

/-- **The third test's Bool is true at the library's own blocks, each times an element.** -/
theorem varsTest_stretches (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (x : E),
      firstRow + values.size ≤ S.matrixRows ∧
        ∃ t ∈ stretchBlocks S.kRow firstRow values fuel start, w = t.scale x) :
    g.all (·.vars == S.kRow) = true :=
  varsTest_blocks S g (blocks_scaled S g h)

/-- **The fourth test's Bool is true at the library's own blocks, each times an element.** -/
theorem cutTest_stretches (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (x : E),
      firstRow + values.size ≤ S.matrixRows ∧
        ∃ t ∈ stretchBlocks S.kRow firstRow values fuel start, w = t.scale x) :
    (g.all fun w => (tensorBelow w 0 S.kRow S.matrixRows).isSome) = true :=
  cutTest_blocks S g (blocks_scaled S g h)

/-- **The row (Dot) at the library's own blocks, each times an element.** -/
theorem dot_stretches (S : LinShape) (g : List Tensor)
    (h : ∀ w ∈ g, ∃ (firstRow : Nat) (values : Array E) (fuel start : Nat) (x : E),
      firstRow + values.size ≤ S.matrixRows ∧
        ∃ t ∈ stretchBlocks S.kRow firstRow values fuel start, w = t.scale x)
    (psi : List E) (hp : psi.length = S.kCol) (omega : Nat) (omegaLay : VectorLay) (w : Nat)
    (wLay : VectorLay) :
    linDotRow S g psi omega omegaLay w wLay =
      some (addLaid (addLaid {} omega omegaLay g) w wLay [Tensor.eq psi (negE oneE)]) :=
  dot_blocks S g (blocks_scaled S g h) psi hp omega omegaLay w wLay

/-! ## The premises can be met -/

-- a block of two rows from the row 2 on, among eight rows; the length 5
example :
    tensorBelow
      { pairs := [(oneE, oneE), (zeroE, oneE), (oneE, zeroE)]
        denseVars := [0], values := #[oneE, oneE] }
      0 3 5 =
    some [{ pairs := [(oneE, oneE), (zeroE, oneE), (oneE, zeroE)]
            denseVars := [0], values := #[oneE, oneE] }] :=
  form_uncut 3 1 1 5 _ ⟨rfl, rfl⟩ (by decide) (by decide) (by decide)

-- the library's maker at the rows 2, 3, 4 of eight: two blocks
#guard (stretchBlocks 3 2 #[oneE, oneE, oneE] 8 2).length == 2
-- the length 5: each block comes back as one vector
#guard (stretchBlocks 3 2 #[oneE, oneE, oneE] 8 2).all fun t =>
  (tensorBelow t 0 3 5).map (·.length) == some 1
-- so too with each block times an element
#guard (stretchBlocks 3 2 #[oneE, oneE, oneE] 8 2).all fun t =>
  (tensorBelow (t.scale (addE oneE oneE)) 0 3 5).map (·.length) == some 1
-- the length 3: the first block crosses it and cannot be cut
#guard ((stretchBlocks 3 2 #[oneE, oneE, oneE] 8 2).head?.map fun t =>
  (tensorBelow t 0 3 3).isNone) == some true
-- the length 4: the second block lies wholly at or beyond it: it comes back as no vector
#guard ((stretchBlocks 3 2 #[oneE, oneE, oneE] 8 2).getLast?.map fun t =>
  (tensorBelow t 0 3 4).map (·.length)) == some (some 0)

end ProofFile.Honest.K14

#print axioms ProofFile.Honest.K14.foldPow_all
#print axioms ProofFile.Honest.K14.foldPow_mono
#print axioms ProofFile.Honest.K14.foldPow_le
#print axioms ProofFile.Honest.K14.choiceSum_le
#print axioms ProofFile.Honest.K14.cut_whole
#print axioms ProofFile.Honest.K14.form_vars
#print axioms ProofFile.Honest.K14.form_uncut
#print axioms ProofFile.Honest.K14.blockOf_form
#print axioms ProofFile.Honest.K14.stretch_form
#print axioms ProofFile.Honest.K14.form_scale
#print axioms ProofFile.Honest.K14.varsTest_blocks
#print axioms ProofFile.Honest.K14.cuts_blocks
#print axioms ProofFile.Honest.K14.cutTest_blocks
#print axioms ProofFile.Honest.K14.dot_blocks
#print axioms ProofFile.Honest.K14.blocks_scaled
#print axioms ProofFile.Honest.K14.varsTest_stretches
#print axioms ProofFile.Honest.K14.cutTest_stretches
#print axioms ProofFile.Honest.K14.dot_stretches
