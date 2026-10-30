-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/UnitsRead.lean.

What is here. What the loops of `fbFree` (Johnson/Desc/K4/Honest/Units.lean: the unit's weights
under a claim's factors, with some groups left open) leave in an entry of the table: the sum, over
the unit's cells whose row's number plus column's number is the entry's number, of the row's weight
times the column's weight times the cell's word.

  `getD_modify`, `foldl_gather`, `foldl_skip`   a loop of `Array.modify`: an entry gathers the steps
     that hit it
  `sum_filter`, `sum_zipIdx_at`   sums over lists
  `bucket_at`, `bucket_read`   the columns, gathered by their numbers
  `row_step`, `rows_read`, `sum_buckets`   one row's step; the rows' loop; the two numbers joined
  `fbFree_read`   **the entry**

Limits. At the reading `Reading.gl`. On the loops alone: the rows' and columns' weights and numbers
stay the letters of that file (`rowWeights`, `rowNumbers`, `colWeight`, `colNumber`): what they are
worth is not said here. For an entry's number below the number of entries.

No property is claimed.
-/
import Johnson.Desc.K4.Honest.Units
import Johnson.Road.K4.C.StackEnds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E F zeroE ofF maddE maddS isZeroE)
open OnBytes.Model (Reading WsLay WsUnit WsGrp WsFac WsClaim)
open OnBytes.Road.K4.C (gl_maddE gl_foldl_maddE gl_foldl_maddS range_sum)
open OnBytes.Desc.First.K4.Honest

/-! ## 1 Loops of `Array.modify` -/

/-- An entry behind one step. -/
theorem getD_modify {β : Type} (a : Array β) (i n : ℕ) (f : β → β) (d : β) (hn : n < a.size) :
    (a.modify i f).getD n d = if i = n then f (a.getD n d) else a.getD n d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_modify]
  by_cases h : i = n
  · rw [if_pos h, if_pos h, Array.getElem?_eq_getElem hn]
    rfl
  · rw [if_neg h, if_neg h]

/-- The size behind a loop of such steps. -/
theorem size_foldl_modify {α β : Type} (ix : α → ℕ) (g : α → β → β) : ∀ (l : List α)
    (out : Array β), (l.foldl (fun o a => o.modify (ix a) (g a)) out).size = out.size
  | [], _ => rfl
  | a :: l, out => by
    rw [List.foldl_cons, size_foldl_modify ix g l, Array.size_modify]

/-- **An entry gathers the steps that hit it**, in their order. -/
theorem foldl_gather {α β : Type} (ix : α → ℕ) (g : α → β → β) (d : β) (n : ℕ) : ∀ (l : List α)
    (out : Array β), n < out.size →
    (l.foldl (fun o a => o.modify (ix a) (g a)) out).getD n d =
      (l.filter fun a => ix a == n).foldl (fun s a => g a s) (out.getD n d)
  | [], _, _ => rfl
  | a :: l, out, hn => by
    rw [List.foldl_cons, foldl_gather ix g d n l _ (by rw [Array.size_modify]; exact hn),
      getD_modify out _ n _ d hn, List.filter_cons]
    by_cases h : ix a = n
    · rw [if_pos h, if_pos (by rw [h]; exact beq_self_eq_true n), List.foldl_cons]
    · rw [if_neg h, if_neg (by simpa using h)]

/-- A loop that leaves some members out is the loop over the others. -/
theorem foldl_skip {α β : Type} (p : α → Bool) (f : β → α → β) : ∀ (l : List α) (s : β),
    l.foldl (fun s a => if p a = true then s else f s a) s =
      (l.filter fun a => !p a).foldl f s
  | [], _ => rfl
  | a :: l, s => by
    rw [List.foldl_cons, List.filter_cons]
    by_cases h : p a = true
    · rw [if_pos h, if_neg (by simp [h]), foldl_skip p f l]
    · rw [if_neg h, if_pos (by simpa using h), List.foldl_cons, foldl_skip p f l]

/-! ## 2 Sums over lists -/

/-- A sum over the members that pass a test. -/
theorem sum_filter {α : Type} (p : α → Bool) (f : α → Cb.Gl.E) : ∀ l : List α,
    ((l.filter p).map f).sum = (l.map fun a => if p a = true then f a else 0).sum
  | [] => rfl
  | a :: l => by
    rw [List.filter_cons, List.map_cons, List.sum_cons, ← sum_filter p f l]
    by_cases h : p a = true
    · rw [if_pos h, if_pos h, List.map_cons, List.sum_cons]
    · rw [if_neg h, if_neg h, zero_add]

/-- A sum over an array's members with their numbers. -/
theorem sum_zipIdx_at {β : Type} (d : β) (f : β → ℕ → Cb.Gl.E) : ∀ (l : List β) (k : ℕ),
    ((l.zipIdx k).map fun x => f x.1 x.2).sum =
      ∑ m ∈ Finset.range l.length, f (l.getD m d) (k + m)
  | [], _ => by simp
  | a :: l, k => by
    rw [List.zipIdx_cons, List.map_cons, List.sum_cons, sum_zipIdx_at d f l (k + 1),
      List.length_cons, Finset.sum_range_succ', add_comm]
    refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun m _ => ?_) rfl
    rw [List.getD_cons_succ, show k + 1 + m = k + (m + 1) by omega]

/-! ## 3 The columns, gathered by their numbers -/

/-- The columns' loop, with free letters: cw: a column's weight; cn: its number. -/
def bucketsOf (cw : ℕ → E) (cn : ℕ → ℕ) (N M : ℕ) : Array (Array (ℕ × E)) :=
  (List.range N).foldl
    (fun b col => if isZeroE (cw col) = true then b else b.modify (cn col) (·.push (col, cw col)))
    (Array.replicate M #[])

theorem bucketsOf_size (cw : ℕ → E) (cn : ℕ → ℕ) (N M : ℕ) : (bucketsOf cw cn N M).size = M := by
  unfold bucketsOf
  rw [foldl_skip (fun col => isZeroE (cw col))
    (fun (b : Array (Array (ℕ × E))) col => b.modify (cn col) (·.push (col, cw col))),
    size_foldl_modify cn (fun col (a : Array (ℕ × E)) => a.push (col, cw col)),
    Array.size_replicate]

/-- Pushing the members of a list. -/
theorem foldl_push {α γ : Type} (h : α → γ) : ∀ (l : List α) (a : Array γ),
    (l.foldl (fun s x => s.push (h x)) a).toList = a.toList ++ l.map h
  | [], a => by simp
  | x :: l, a => by
    rw [List.foldl_cons, foldl_push h l, Array.toList_push, List.map_cons, List.append_assoc]
    rfl

/-- **Bucket number m**: the columns with a weight whose number is m, each with its weight. -/
theorem bucket_at (cw : ℕ → E) (cn : ℕ → ℕ) (N M m : ℕ) (hm : m < M) :
    ((bucketsOf cw cn N M).getD m #[]).toList =
      (((List.range N).filter fun col => !isZeroE (cw col)).filter fun col => cn col == m).map
        fun col => (col, cw col) := by
  unfold bucketsOf
  rw [foldl_skip (fun col => isZeroE (cw col))
    (fun (b : Array (Array (ℕ × E))) col => b.modify (cn col) (·.push (col, cw col))),
    foldl_gather cn (fun col (a : Array (ℕ × E)) => a.push (col, cw col)) #[] m _ _
      (by rw [Array.size_replicate]; exact hm),
    foldl_push (fun col => (col, cw col))]
  have e : (Array.replicate M (#[] : Array (ℕ × E))).getD m #[] = #[] := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
    split <;> rfl
  rw [e]
  rfl

/-- **What a row's loop over a bucket adds up.** X: the row's words by the column. -/
theorem bucket_read (cw : ℕ → E) (cn : ℕ → ℕ) (N M m : ℕ) (hm : m < M) (X : ℕ → F) :
    Reading.gl.val (((bucketsOf cw cn N M).getD m #[]).foldl
      (fun t x => maddS t (X x.1) x.2) zeroE) =
      ∑ col ∈ Finset.range N, if cn col = m then
        Reading.gl.val (ofF (X col)) * Reading.gl.val (cw col) else 0 := by
  rw [← Array.foldl_toList, bucket_at cw cn N M m hm, List.foldl_map,
    gl_foldl_maddS (fun col => X col) (fun col => cw col), Reading.gl.zero, zero_add, sum_filter,
    sum_filter, range_sum]
  refine Finset.sum_congr rfl fun col _ => ?_
  by_cases hz : isZeroE (cw col) = true
  · have e0 : Reading.gl.val (cw col) = 0 := by
      rw [(OnBytes.Slice.isZeroE_eq _).mp hz]
      exact Reading.gl.zero
    rw [if_neg (by simp [hz]), e0, mul_zero, ite_self]
  · rw [if_pos (by simpa using hz)]
    by_cases hc : cn col = m
    · rw [if_pos (by rw [hc]; exact beq_self_eq_true m), if_pos hc]
    · rw [if_neg (by simpa using hc), if_neg hc]

/-! ## 4 The rows -/

/-- **One row's step**, with free letters. k: the row's weight; r: its number; B: the buckets. -/
theorem row_step (B : Array (Array (ℕ × E))) (k : E) (r : ℕ) (X : ℕ → F) (out : Array E) (n : ℕ)
    (hn : n < out.size) :
    Reading.gl.val (((B.toList.zipIdx.filter fun b => !b.1.isEmpty).foldl
      (fun out b => out.modify (r + b.2) fun s =>
        maddE s k (b.1.foldl (fun t x => maddS t (X x.1) x.2) zeroE)) out).getD n zeroE) =
      Reading.gl.val (out.getD n zeroE) + ∑ m ∈ Finset.range B.size, if r + m = n then
        Reading.gl.val k * Reading.gl.val ((B.getD m #[]).foldl
          (fun t x => maddS t (X x.1) x.2) zeroE) else 0 := by
  rw [foldl_gather (fun b : Array (ℕ × E) × ℕ => r + b.2)
    (fun b s => maddE s k (b.1.foldl (fun t x => maddS t (X x.1) x.2) zeroE)) zeroE n _ out hn,
    gl_foldl_maddE (fun _ => k)
      (fun b : Array (ℕ × E) × ℕ => b.1.foldl (fun t x => maddS t (X x.1) x.2) zeroE),
    sum_filter, sum_filter]
  congr 1
  have e := sum_zipIdx_at (#[] : Array (ℕ × E)) (fun (a : Array (ℕ × E)) m =>
    if (!a.isEmpty) = true then (if (r + m == n) = true then
      Reading.gl.val k * Reading.gl.val (a.foldl (fun t x => maddS t (X x.1) x.2) zeroE) else 0)
    else 0) B.toList 0
  refine e.trans ?_
  rw [Array.length_toList]
  refine Finset.sum_congr rfl fun m _ => ?_
  have eB : B.toList.getD m #[] = B.getD m #[] := by
    rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, Array.getD_eq_getD_getElem?]
  rw [Nat.zero_add, eB]
  by_cases he : (B.getD m #[]).isEmpty = true
  · have e0 : B.getD m #[] = #[] := Array.isEmpty_iff.mp he
    rw [if_neg (by rw [he]; decide), e0]
    show (0 : Cb.Gl.E) = if r + m = n then Reading.gl.val k * Reading.gl.val zeroE else 0
    rw [Reading.gl.zero, mul_zero, ite_self]
  · rw [if_pos (by simpa using he)]
    by_cases hc : r + m = n
    · rw [if_pos (by rw [hc]; exact beq_self_eq_true n), if_pos hc]
    · rw [if_neg (by simpa using hc), if_neg hc]

/-- **The rows' loop**, with free letters. rw, rn: the rows' weights and numbers; X: the words by
row and column. -/
theorem rows_read (B : Array (Array (ℕ × E))) (rw : Array E) (rn : Array ℕ) (X : ℕ → ℕ → F)
    (n : ℕ) : ∀ (l : List ℕ) (out : Array E), n < out.size →
    Reading.gl.val ((l.foldl (fun out y =>
      if isZeroE (rw.getD y zeroE) = true then out
      else (B.toList.zipIdx.filter fun b => !b.1.isEmpty).foldl
        (fun out b => out.modify (rn.getD y 0 + b.2) fun s =>
          maddE s (rw.getD y zeroE) (b.1.foldl (fun t x => maddS t (X y x.1) x.2) zeroE))
        out) out).getD n zeroE) =
      Reading.gl.val (out.getD n zeroE) + (l.map fun y => ∑ m ∈ Finset.range B.size,
        if rn.getD y 0 + m = n then Reading.gl.val (rw.getD y zeroE) *
          Reading.gl.val ((B.getD m #[]).foldl (fun t x => maddS t (X y x.1) x.2) zeroE)
        else 0).sum
  | [], _, _ => by simp
  | y :: l, out, hn => by
    rw [List.foldl_cons, List.map_cons, List.sum_cons, ← add_assoc]
    by_cases hz : isZeroE (rw.getD y zeroE) = true
    · have e0 : Reading.gl.val (rw.getD y zeroE) = 0 := by
        rw [(OnBytes.Slice.isZeroE_eq _).mp hz]
        exact Reading.gl.zero
      rw [if_pos hz, rows_read B rw rn X n l out hn, e0]
      simp only [zero_mul, ite_self, Finset.sum_const_zero, add_zero]
    · rw [if_neg hz, rows_read B rw rn X n l _ (by
        rw [size_foldl_modify (fun b : Array (ℕ × E) × ℕ => rn.getD y 0 + b.2)
          (fun b s => maddE s (rw.getD y zeroE)
            (b.1.foldl (fun t x => maddS t (X y x.1) x.2) zeroE))]
        exact hn), row_step B _ _ (X y) out n hn]

/-- The two numbers, joined: a sum over the buckets of a sum over a bucket's columns is a sum over
the columns. -/
theorem sum_buckets (M N r n : ℕ) (hn : n < M) (cn : ℕ → ℕ) (k : Cb.Gl.E) (a : ℕ → Cb.Gl.E) :
    (∑ m ∈ Finset.range M, if r + m = n then
      k * ∑ col ∈ Finset.range N, (if cn col = m then a col else 0) else 0) =
      ∑ col ∈ Finset.range N, if r + cn col = n then k * a col else 0 := by
  have e1 : ∀ m, (if r + m = n then
      k * ∑ col ∈ Finset.range N, (if cn col = m then a col else 0) else 0) =
      ∑ col ∈ Finset.range N, if r + m = n then (if cn col = m then k * a col else 0) else 0 := by
    intro m
    by_cases h : r + m = n
    · simp only [if_pos h, Finset.mul_sum, mul_ite, mul_zero]
    · simp only [if_neg h, Finset.sum_const_zero]
  simp only [e1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun col _ => ?_
  by_cases hc : r + cn col = n
  · rw [if_pos hc, Finset.sum_eq_single (cn col)]
    · rw [if_pos hc, if_pos rfl]
    · intro m _ hm
      by_cases h : r + m = n
      · rw [if_pos h, if_neg fun e => hm e.symm]
      · rw [if_neg h]
    · intro hm
      exact absurd (Finset.mem_range.mpr (by omega)) hm
  · rw [if_neg hc]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases h : r + m = n
    · rw [if_pos h, if_neg fun e => hc (by rw [e]; exact h)]
    · rw [if_neg h]

/-! ## 5 The entry -/

/-- **AN ENTRY OF THE TABLE**: the sum, over the unit's cells whose row's number plus column's
number is the entry's, of the row's weight times the cell's word times the column's weight. -/
theorem fbFree_read {lay : WsLay} {c : WsClaim} {u : WsUnit} (w : ℕ → ℕ → F)
    (free : List String) (hu : lay.U[c.ui]? = some u) {tab : Array E}
    (h : fbFree lay w c free = some tab) (n : ℕ) (hn : n < (stridesOf u free).2) :
    Reading.gl.val (tab.getD n zeroE) = ∑ y ∈ Finset.range u.rows,
      ∑ col ∈ Finset.range (2 ^ u.ncb),
        if (rowNumbers u (c.f.zip u.g) (stridesOf u free).1).getD y 0 +
            colNumber (c.f.zip u.g) (stridesOf u free).1 col = n then
          Reading.gl.val ((rowWeights u (c.f.zip u.g) (stridesOf u free).1).getD y zeroE) *
            (Reading.gl.val (ofF (w (u.off + y) col)) *
              Reading.gl.val (colWeight u (c.f.zip u.g) (stridesOf u free).1 col))
        else 0 := by
  unfold fbFree at h
  rw [hu] at h
  dsimp only at h
  split at h
  · cases h
  · obtain rfl := Option.some.inj h
    have key := rows_read
      (bucketsOf (colWeight u (c.f.zip u.g) (stridesOf u free).1)
        (colNumber (c.f.zip u.g) (stridesOf u free).1) (2 ^ u.ncb) (stridesOf u free).2)
      (rowWeights u (c.f.zip u.g) (stridesOf u free).1)
      (rowNumbers u (c.f.zip u.g) (stridesOf u free).1) (fun y col => w (u.off + y) col) n
      (List.range u.rows) (Array.replicate (stridesOf u free).2 zeroE)
      (by rw [Array.size_replicate]; exact hn)
    refine key.trans ?_
    have e0 : (Array.replicate (stridesOf u free).2 zeroE).getD n zeroE = zeroE := by
      rw [Array.getD_eq_getD_getElem?, Array.getElem?_replicate]
      split <;> rfl
    rw [e0, Reading.gl.zero, zero_add, range_sum, bucketsOf_size]
    refine Finset.sum_congr rfl fun y _ => ?_
    refine Eq.trans ?_ (sum_buckets (stridesOf u free).2 (2 ^ u.ncb)
      ((rowNumbers u (c.f.zip u.g) (stridesOf u free).1).getD y 0) n hn
      (colNumber (c.f.zip u.g) (stridesOf u free).1)
      (Reading.gl.val ((rowWeights u (c.f.zip u.g) (stridesOf u free).1).getD y zeroE))
      fun col => Reading.gl.val (ofF (w (u.off + y) col)) *
        Reading.gl.val (colWeight u (c.f.zip u.g) (stridesOf u free).1 col))
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [bucket_read _ _ _ _ m (Finset.mem_range.mp hm)]

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.getD_modify
#print axioms ProofFile.Honest.K4.size_foldl_modify
#print axioms ProofFile.Honest.K4.foldl_gather
#print axioms ProofFile.Honest.K4.foldl_skip
#print axioms ProofFile.Honest.K4.sum_filter
#print axioms ProofFile.Honest.K4.sum_zipIdx_at
#print axioms ProofFile.Honest.K4.bucketsOf_size
#print axioms ProofFile.Honest.K4.foldl_push
#print axioms ProofFile.Honest.K4.bucket_at
#print axioms ProofFile.Honest.K4.bucket_read
#print axioms ProofFile.Honest.K4.row_step
#print axioms ProofFile.Honest.K4.rows_read
#print axioms ProofFile.Honest.K4.sum_buckets
#print axioms ProofFile.Honest.K4.fbFree_read
