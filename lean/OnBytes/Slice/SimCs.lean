-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SimCs.lean: what the format's code switch computes, in the field.

A fold leaves one claim on three folded rows. The code switch (Fmt/M1Cs.lean) moves that claim to
one row on the two tables of the next oracle message, the main table and the mask table. It makes a
list of rows on these tables: the carried claim, the sample's row, and three rows for each drawn
position. Then it adds them up, row number k under the power theta^k of one drawn element theta.
This file reads the folded symbols, each row and the sum in the field `GE`, as closed forms.

How the statements are shaped. Each holds at every index, without a condition on sizes: an entry
beyond a table's end is 0. The opened columns are a function cl from positions to columns, and the
format's function col gives `some (cl x)` at each drawn position x. Draw number i is `xs.getD i 0`.

The mask table. From place 0 on it holds the carried mask row, the fresh mask row, the main row's
tail, the carried mask's tail and the fresh mask's tail, and then free room. `vec_cs_d` has all of
it in one formula. The theorems `cs_at_mask` to `cs_at_free` give the formula that is left on each
stretch, if the five stretches fit into the table.

Main definitions: `cut`, `moved` (a vector cut at a place, moved up by some places), `wM`, `wT` (the
weights of a message's and of a tail's entries in a symbol of a code), `allRows`.
Main theorems.
 `toE_yOf_main`, `toE_yOf_mask`, `toE_yOf_fresh`: the three folded symbols of a column.
 `csRows_some`, `csRows_none`, `csStep_some`: which rows there are, and that the fast form of the
   code switch gives their sum.
 `csRows_congr`, `csStep_congr`: the columns are read at the drawn positions alone.
 `vec_carried_c` to `draw_t`: each row, entry by entry.
 `toE_cs_t`, `vec_cs_c`, `vec_cs_d`: the new target, and the new row on both tables.
 `cs_at_main`, `cs_at_mask`, `cs_at_fresh`, `cs_at_tail`, `cs_at_maskTail`, `cs_at_freshTail`,
   `cs_at_free`: the new row, stretch by stretch.

Not claimed. Nothing on a protocol, and nothing on whether a row holds of any message. Nothing on
the other field of the format.
-/
import Fmt.M1CsEq
import OnBytes.Slice.SimBasic

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1

/-! ## Vectors on the natural numbers: cut, moved, and the weights of a code's symbol -/

/-- The vector F before place n, and 0 from there on. -/
def cut (n : ℕ) (F : ℕ → GE) (j : ℕ) : GE := if j < n then F j else 0

/-- The vector F moved up by o places: 0 before place o. -/
def moved (o : ℕ) (F : ℕ → GE) (j : ℕ) : GE := if o ≤ j then F (j - o) else 0

/-- The weight of entry j of the message in the symbol at the position x: z^(r + j) at the point z;
0 from the message's length on. -/
def wM (C : Code) (x j : ℕ) : GE :=
  if j < C.l then algebraMap GF GE (toF (point C.a x) ^ (C.r + j)) else 0

/-- The weight of entry j of the tail in the symbol at the position x: z^j at the point z; 0 from
the tail's length on. -/
def wT (C : Code) (x j : ℕ) : GE :=
  if j < C.r then algebraMap GF GE (toF (point C.a x) ^ j) else 0

/-- Moving by no place changes nothing. -/
theorem moved_zero (F : ℕ → GE) : moved 0 F = F := by
  funext j
  simp [moved]

/-- The sum of two vectors cut at one place is the cut of their sum. -/
theorem cut_add (n : ℕ) (F G : ℕ → GE) (j : ℕ) :
    cut n F j + cut n G j = cut n (fun i => F i + G i) j := by
  unfold cut
  split
  · rfl
  · exact add_zero 0

/-- Before the place of the cut the vector is as it was. -/
theorem cut_of_lt {n j : ℕ} (h : j < n) (F : ℕ → GE) : cut n F j = F j := if_pos h

/-- From the place of the cut on the vector is 0. -/
theorem cut_of_le {n j : ℕ} (h : n ≤ j) (F : ℕ → GE) : cut n F j = 0 := if_neg (by omega)

/-- A vector moved up by o places is 0 before place o. -/
theorem moved_of_lt {o j : ℕ} (h : j < o) (F : ℕ → GE) : moved o F j = 0 := if_neg (by omega)

/-- From place o on, a vector moved up by o places has the entry that was o places lower. -/
theorem moved_of_le {o j : ℕ} (h : o ≤ j) (F : ℕ → GE) : moved o F j = F (j - o) := if_pos h

/-- Entry j of a vector is entry o + j of the vector moved up by o places. -/
theorem moved_add (o : ℕ) (F : ℕ → GE) (j : ℕ) : moved o F (o + j) = F j := by
  rw [moved_of_le (Nat.le_add_right o j), Nat.add_sub_cancel_left]

/-- From the message's length on the weight is 0. -/
theorem wM_of_le {C : Code} {j : ℕ} (h : C.l ≤ j) (x : ℕ) : wM C x j = 0 := if_neg (by omega)

/-- From the tail's length on the weight is 0. -/
theorem wT_of_le {C : Code} {j : ℕ} (h : C.r ≤ j) (x : ℕ) : wT C x j = 0 := if_neg (by omega)

/-- The generator's row on the message, as a list of triples. -/
theorem lst_genM (C : Code) (x : ℕ) : lst ((genM C x).map Fmt.Fld.ofF) = wM C x := by
  funext j
  rw [← vec_toArray]
  exact vec_genME C x j

/-- The generator's row on the tail, as a list of triples. -/
theorem lst_genT (C : Code) (x : ℕ) : lst ((genT C x).map Fmt.Fld.ofF) = wT C x := by
  funext j
  rw [← vec_toArray]
  exact vec_genTE C x j

/-- An array read as a list has the same entries in the field. -/
theorem lst_toList (v : Array E) : lst v.toList = vec v := by
  funext i
  rw [← vec_toArray]

/-- A list cut or filled to n entries. -/
theorem lst_fitL (n : ℕ) (l : List E) : lst (fitL Fmt.Fld.zeroE n l) = cut n (lst l) := by
  funext i
  by_cases h : i < n
  · rw [cut_of_lt h]
    unfold lst
    rw [getD_fitL _ _ _ _ h]
  · rw [cut_of_le (by omega), lst_of_le _ _ (by rw [length_fitL]; omega)]

/-- The vector that `layAt` makes has n entries. -/
theorem size_layAt (n o : ℕ) (w : List E) : (layAt n o w).size = n := by
  simp [layAt]

/-- A vector of n entries with w from place o on. -/
theorem vec_layAt (n o : ℕ) (w : List E) : vec (layAt n o w) = cut n (moved o (lst w)) := by
  funext i
  by_cases h : i < n
  · have e : ent (layAt n o w) i
        = if o ≤ i then w.getD (i - o) Fmt.Fld.zeroE else Fmt.Fld.zeroE := by
      simp [ent, layAt, Array.getD, h]
    unfold vec cut moved lst
    rw [e, if_pos h]
    split
    · rfl
    · exact toE_zeroE
  · rw [vec_of_le _ _ (by rw [size_layAt]; omega)]
    unfold cut
    rw [if_neg h]

/-! ## The three folded symbols of a column -/

/-- The main rows' symbols, folded at the whole point. -/
theorem toE_yOf_main (h : ℕ) (s : SRow) (c : Col) :
    toE (yOf .two h s c).1
      = ∑ b ∈ Finset.range (2 ^ s.g.length), eqW s.g.length (lst s.g) b * vec c.main b :=
  toE_foldV s.g c.main

/-- A vector folded at the first h coordinates of a point. -/
theorem toE_foldV_take (h : ℕ) (g : List E) (v : Array E) :
    toE (foldV .two (g.take h) v)
      = ∑ b ∈ Finset.range (2 ^ min h g.length), eqW (min h g.length) (lst g) b * vec v b := by
  rw [toE_foldV, List.length_take]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [eqW_congr _ (lst (g.take h)) (lst g) b fun t ht =>
    lst_take h g t (lt_of_lt_of_le ht (Nat.min_le_left _ _))]

/-- The carried mask rows' symbols, folded at the point's first h coordinates. -/
theorem toE_yOf_mask (h : ℕ) (s : SRow) (c : Col) :
    toE (yOf .two h s c).2.1
      = ∑ b ∈ Finset.range (2 ^ min h s.g.length),
          eqW (min h s.g.length) (lst s.g) b * vec c.mask b :=
  toE_foldV_take h s.g c.mask

/-- The fresh mask rows' symbols, folded at the point's first h coordinates. -/
theorem toE_yOf_fresh (h : ℕ) (s : SRow) (c : Col) :
    toE (yOf .two h s c).2.2
      = ∑ b ∈ Finset.range (2 ^ min h s.g.length),
          eqW (min h s.g.length) (lst s.g) b * vec c.fresh b :=
  toE_foldV_take h s.g c.fresh

/-! ## The rows -/

/-- All rows of a code switch, in the order of batching, if the column at the position x is
cl x: the carried claim, the sample's row, three rows for each draw. -/
def allRows (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (cl : ℕ → Col) : List GRow :=
  CsEq.carriedR f old new s :: CsEq.smpR new sample ::
    xs.flatMap fun x => drawRows f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s x (cl x)

/-- If every drawn position has a column, the format's list of rows is `allRows`. -/
theorem csRows_some (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (col : ℕ → Option Col) (cl : ℕ → Col) (h : ∀ x ∈ xs, col x = some (cl x)) :
    csRows f old new s sample xs col = some (allRows f old new s sample xs cl) := by
  have hr : ∀ ys : List ℕ, (∀ x ∈ ys, col x = some (cl x)) →
      CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys
        = some (ys.flatMap fun x =>
            drawRows f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s x (cl x)) := by
    intro ys
    induction ys with
    | nil => intro _; rfl
    | cons y ys ih =>
      intro hy
      show (match CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys, col y with
        | some rs, some c =>
          some (drawRows f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s y c ++ rs)
        | _, _ => none) = _
      rw [ih fun x hx => hy x (List.mem_cons_of_mem _ hx), hy y List.mem_cons_self,
        List.flatMap_cons]
  rw [CsEq.csRows_eq, hr xs h]
  rfl

/-- If a drawn position has no column, there is no list of rows. -/
theorem csRows_none (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (col : ℕ → Option Col) (x : ℕ) (hx : x ∈ xs) (h : col x = none) :
    csRows f old new s sample xs col = none := by
  have hr : ∀ ys : List ℕ, x ∈ ys →
      CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys = none := by
    intro ys
    induction ys with
    | nil => intro hy; cases hy
    | cons y ys ih =>
      intro hy
      show (match CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys, col y with
        | some rs, some c =>
          some (drawRows f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s y c ++ rs)
        | _, _ => none) = none
      rcases List.mem_cons.1 hy with e | hy'
      · rw [← e, h]
        cases CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys <;> rfl
      · rw [ih hy']
  rw [CsEq.csRows_eq, hr xs hx]
  rfl

/-- The list of rows reads the columns at the drawn positions alone. -/
theorem csRows_congr (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (col col' : ℕ → Option Col) (h : ∀ x ∈ xs, col x = col' x) :
    csRows f old new s sample xs col = csRows f old new s sample xs col' := by
  have hr : ∀ ys : List ℕ, (∀ x ∈ ys, col x = col' x) →
      CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys
        = CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col' ys := by
    intro ys
    induction ys with
    | nil => intro _; rfl
    | cons y ys ih =>
      intro hy
      show (match CsEq.rowsOf f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s col ys, col y with
        | some rs, some c =>
          some (drawRows f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s y c ++ rs)
        | _, _ => none) = _
      rw [ih fun x hx => hy x (List.mem_cons_of_mem _ hx), hy y List.mem_cons_self]
      rfl
  rw [CsEq.csRows_eq, CsEq.csRows_eq, hr xs h]

/-- The code switch reads the columns at the drawn positions alone. -/
theorem csStep_congr (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (theta : E) (col col' : ℕ → Option Col) (h : ∀ x ∈ xs, col x = col' x) :
    csStep f old new s sample xs theta col = csStep f old new s sample xs theta col' := by
  rw [CsEq.csStep_eq, CsEq.csStep_eq]
  unfold csStepLit
  rw [csRows_congr f old new s sample xs col col' h]

/-- There are two rows and three for each draw. -/
theorem length_allRows (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (cl : ℕ → Col) : (allRows f old new s sample xs cl).length = nRows xs.length := by
  have hr : ∀ ys : List ℕ, (ys.flatMap fun x =>
      drawRows f old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s x (cl x)).length
        = 3 * ys.length := by
    intro ys
    induction ys with
    | nil => rfl
    | cons y ys ih =>
      rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
      show 3 + 3 * ys.length = 3 * (ys.length + 1)
      omega
  unfold allRows nRows
  rw [List.length_cons, List.length_cons, hr xs]
  omega

/-- The code switch in its fast form gives the sum of all rows under the powers of theta. -/
theorem csStep_some (f : Fmt.Fld) (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ)
    (theta : E) (col : ℕ → Option Col) (cl : ℕ → Col) (h : ∀ x ∈ xs, col x = some (cl x)) :
    csStep f old new s sample xs theta col
      = some (sumRows f theta (allRows f old new s sample xs cl)) := by
  rw [CsEq.csStep_eq]
  unfold csStepLit
  rw [csRows_some f old new s sample xs col cl h]
  rfl

/-! ### Each row, entry by entry -/

/-- The carried claim on the main table. -/
theorem vec_carried_c (old new : Stage) (s : SRow) :
    vec (CsEq.carriedR .two old new s).c
      = cut (2 ^ new.k * new.C.l) (cut old.C.l (vec s.c)) := by
  show vec (layAt (2 ^ new.k * new.C.l) 0 (fitL Fmt.Fld.zeroE old.C.l s.c.toList)) = _
  rw [vec_layAt, moved_zero, lst_fitL, lst_toList]

/-- The carried claim on the mask table: the carried mask's part, then the fresh mask's. -/
theorem vec_carried_d (old new : Stage) (s : SRow) (j : ℕ) :
    vec (CsEq.carriedR .two old new s).d j
      = cut (2 ^ new.h * new.Z.l)
          (fun i => cut old.Z.l (vec s.d0) i + moved old.Z.l (cut old.Z.l (vec s.d1)) i) j := by
  show vec (addV .two
      (layAt (2 ^ new.h * new.Z.l) 0 (fitL Fmt.Fld.zeroE old.Z.l s.d0.toList))
      (layAt (2 ^ new.h * new.Z.l) old.Z.l (fitL Fmt.Fld.zeroE old.Z.l s.d1.toList))) j = _
  rw [vec_addV, vec_layAt, vec_layAt, moved_zero, lst_fitL, lst_fitL, lst_toList, lst_toList,
    cut_add]

/-- The sample's row on the main table. -/
theorem vec_smp_c (new : Stage) (sample : GRow) :
    vec (CsEq.smpR new sample).c = cut (2 ^ new.k * new.C.l) (vec sample.c) := by
  show vec (layAt (2 ^ new.k * new.C.l) 0 sample.c.toList) = _
  rw [vec_layAt, moved_zero, lst_toList]

/-- The sample's row on the mask table. -/
theorem vec_smp_d (new : Stage) (sample : GRow) :
    vec (CsEq.smpR new sample).d = cut (2 ^ new.h * new.Z.l) (vec sample.d) := by
  show vec (layAt (2 ^ new.h * new.Z.l) 0 sample.d.toList) = _
  rw [vec_layAt, moved_zero, lst_toList]

/-- One draw's three rows on the main table. -/
theorem draw_c (old : Stage) (nM nD : ℕ) (s : SRow) (x : ℕ) (c : Col) (j : ℕ) :
    (drawRows .two old nM nD s x c).map (fun R => vec R.c j) = [cut nM (wM old.C x) j, 0, 0] := by
  show [vec (layAt nM 0 ((genM old.C x).map Fmt.Fld.ofF)) j, vec #[] j, vec #[] j] = _
  rw [vec_layAt, moved_zero, lst_genM, vec_of_le #[] j (Nat.zero_le j)]

/-- One draw's three rows on the mask table. -/
theorem draw_d (old : Stage) (nM nD : ℕ) (s : SRow) (x : ℕ) (c : Col) (j : ℕ) :
    (drawRows .two old nM nD s x c).map (fun R => vec R.d j)
      = [cut nD (moved (2 * old.Z.l) (wT old.C x)) j,
         cut nD (fun i => wM old.Z (cp old.Z x) i
           + moved (2 * old.Z.l + old.C.r) (wT old.Z (cp old.Z x)) i) j,
         cut nD (fun i => moved old.Z.l (wM old.Z (cp old.Z x)) i
           + moved (2 * old.Z.l + old.C.r + old.Z.r) (wT old.Z (cp old.Z x)) i) j] := by
  show [vec (layAt nD (2 * old.Z.l) ((genT old.C x).map Fmt.Fld.ofF)) j,
      vec (addV .two (layAt nD 0 ((genM old.Z (cp old.Z x)).map Fmt.Fld.ofF))
        (layAt nD (2 * old.Z.l + old.C.r) ((genT old.Z (cp old.Z x)).map Fmt.Fld.ofF))) j,
      vec (addV .two (layAt nD old.Z.l ((genM old.Z (cp old.Z x)).map Fmt.Fld.ofF))
        (layAt nD (2 * old.Z.l + old.C.r + old.Z.r)
          ((genT old.Z (cp old.Z x)).map Fmt.Fld.ofF))) j] = _
  simp only [vec_addV, vec_layAt, moved_zero, lst_genM, lst_genT, cut_add]

/-- One draw's three targets: the folded symbols of the column. -/
theorem draw_t (old : Stage) (nM nD : ℕ) (s : SRow) (x : ℕ) (c : Col) :
    (drawRows .two old nM nD s x c).map (fun R => toE R.t)
      = [toE (yOf .two old.h s c).1, toE (yOf .two old.h s c).2.1,
         toE (yOf .two old.h s c).2.2] :=
  rfl

/-! ## The sum under the powers of theta -/

/-- The sum of a_k θ^k over a list a, from the inside out: a_0 plus θ times the same sum for the
rest of the list. -/
def horner (θ : GE) : List GE → GE
  | [] => 0
  | a :: l => a + θ * horner θ l

/-- A sum over a list of rows under the powers of θ, from the inside out. -/
theorem sum_eq_horner (θ : GE) (F : GRow → GE) : ∀ rows : List GRow,
    ∑ k ∈ Finset.range rows.length, θ ^ k * F (rows.getD k noRow) = horner θ (rows.map F)
  | [] => rfl
  | r :: rows => by
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons]
    show _ = F r + θ * horner θ (rows.map F)
    rw [← sum_eq_horner θ F rows, Finset.mul_sum, pow_zero, one_mul, List.getD_cons_zero,
      add_comm]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [List.getD_cons_succ, pow_succ]
    ring

/-- Three entries for each draw, sorted by draws. -/
theorem horner_draws (θ : GE) (A B C : ℕ → GE) : ∀ xs : List ℕ,
    horner θ (xs.flatMap fun x => [A x, B x, C x])
      = ∑ i ∈ Finset.range xs.length,
          θ ^ (3 * i) * (A (xs.getD i 0) + θ * B (xs.getD i 0) + θ ^ 2 * C (xs.getD i 0))
  | [] => rfl
  | x :: xs => by
    have e : ∑ k ∈ Finset.range xs.length, θ ^ (3 * (k + 1)) * (A ((x :: xs).getD (k + 1) 0)
          + θ * B ((x :: xs).getD (k + 1) 0) + θ ^ 2 * C ((x :: xs).getD (k + 1) 0))
        = θ ^ 3 * ∑ k ∈ Finset.range xs.length,
            θ ^ (3 * k) * (A (xs.getD k 0) + θ * B (xs.getD k 0) + θ ^ 2 * C (xs.getD k 0)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [List.getD_cons_succ]
      ring
    rw [List.flatMap_cons, List.length_cons, Finset.sum_range_succ', e,
      ← horner_draws θ A B C xs, List.getD_cons_zero]
    show A x + θ * (B x + θ * (C x + θ * horner θ (xs.flatMap fun x => [A x, B x, C x]))) = _
    ring

/-- A sum of two rows and three rows for each draw, under the powers of θ, sorted by draws. -/
theorem sum_by_draws (θ : GE) (F : GRow → GE) (a b : GRow) (xs : List ℕ) (D : ℕ → List GRow)
    (A B C : ℕ → GE) (hD : ∀ x, (D x).map F = [A x, B x, C x]) :
    ∑ k ∈ Finset.range (a :: b :: xs.flatMap D).length,
        θ ^ k * F ((a :: b :: xs.flatMap D).getD k noRow)
      = F a + θ * F b + ∑ i ∈ Finset.range xs.length,
          θ ^ (2 + 3 * i) * (A (xs.getD i 0) + θ * B (xs.getD i 0) + θ ^ 2 * C (xs.getD i 0)) := by
  have e : ∑ i ∈ Finset.range xs.length,
        θ ^ (2 + 3 * i) * (A (xs.getD i 0) + θ * B (xs.getD i 0) + θ ^ 2 * C (xs.getD i 0))
      = θ ^ 2 * horner θ (xs.flatMap fun x => [A x, B x, C x]) := by
    rw [horner_draws, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hm : (xs.flatMap D).map F = xs.flatMap fun x => [A x, B x, C x] := by
    rw [List.map_flatMap]
    exact congrArg (fun g => xs.flatMap g) (funext hD)
  rw [sum_eq_horner, e, List.map_cons, List.map_cons, hm]
  show F a + θ * (F b + θ * horner θ (xs.flatMap fun x => [A x, B x, C x])) = _
  ring

/-- The new target: the carried target, theta times the sample's answer, and for draw number i
the three folded symbols under the powers 2 + 3 i, 3 + 3 i, 4 + 3 i of theta. -/
theorem toE_cs_t (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ) (theta : E)
    (cl : ℕ → Col) :
    toE (sumRows .two theta (allRows .two old new s sample xs cl)).t
      = toE s.t + toE theta * toE sample.t + ∑ i ∈ Finset.range xs.length,
          toE theta ^ (2 + 3 * i) * (toE (yOf .two old.h s (cl (xs.getD i 0))).1
            + toE theta * toE (yOf .two old.h s (cl (xs.getD i 0))).2.1
            + toE theta ^ 2 * toE (yOf .two old.h s (cl (xs.getD i 0))).2.2) := by
  rw [toE_sumRows_t]
  exact sum_by_draws (toE theta) (fun R => toE R.t) _ _ xs _
    (fun x => toE (yOf .two old.h s (cl x)).1) (fun x => toE (yOf .two old.h s (cl x)).2.1)
    (fun x => toE (yOf .two old.h s (cl x)).2.2) fun x => draw_t old _ _ s x (cl x)

/-- The new row on the main table. -/
theorem vec_cs_c (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ) (theta : E)
    (cl : ℕ → Col) (j : ℕ) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).c j
      = cut (2 ^ new.k * new.C.l) (fun j => cut old.C.l (vec s.c) j + toE theta * vec sample.c j
          + ∑ i ∈ Finset.range xs.length,
              toE theta ^ (2 + 3 * i) * wM old.C (xs.getD i 0) j) j := by
  have h := sum_by_draws (toE theta) (fun R => vec R.c j) (CsEq.carriedR .two old new s)
    (CsEq.smpR new sample) xs _ (fun x => cut (2 ^ new.k * new.C.l) (wM old.C x) j) (fun _ => 0)
    (fun _ => 0) fun x => draw_c old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s x (cl x) j
  rw [vec_sumRows_c]
  refine h.trans ?_
  simp only [vec_carried_c, vec_smp_c]
  by_cases hj : j < 2 ^ new.k * new.C.l
  · simp only [cut, if_pos hj, mul_zero, add_zero]
  · simp only [cut, if_neg hj, mul_zero, add_zero, Finset.sum_const_zero]

/-- The new row on the mask table. -/
theorem vec_cs_d (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ) (theta : E)
    (cl : ℕ → Col) (j : ℕ) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d j
      = cut (2 ^ new.h * new.Z.l) (fun j =>
          cut old.Z.l (vec s.d0) j + moved old.Z.l (cut old.Z.l (vec s.d1)) j
          + toE theta * vec sample.d j
          + ∑ i ∈ Finset.range xs.length, toE theta ^ (2 + 3 * i) *
              (moved (2 * old.Z.l) (wT old.C (xs.getD i 0)) j
              + toE theta * (wM old.Z (cp old.Z (xs.getD i 0)) j
                + moved (2 * old.Z.l + old.C.r) (wT old.Z (cp old.Z (xs.getD i 0))) j)
              + toE theta ^ 2 * (moved old.Z.l (wM old.Z (cp old.Z (xs.getD i 0))) j
                + moved (2 * old.Z.l + old.C.r + old.Z.r)
                    (wT old.Z (cp old.Z (xs.getD i 0))) j))) j := by
  have h := sum_by_draws (toE theta) (fun R => vec R.d j) (CsEq.carriedR .two old new s)
    (CsEq.smpR new sample) xs _ _ _ _
    fun x => draw_d old (2 ^ new.k * new.C.l) (2 ^ new.h * new.Z.l) s x (cl x) j
  rw [vec_sumRows_d]
  refine h.trans ?_
  simp only [vec_carried_d, vec_smp_d]
  by_cases hj : j < 2 ^ new.h * new.Z.l
  · simp only [cut, if_pos hj]
  · simp only [cut, if_neg hj, mul_zero, add_zero, Finset.sum_const_zero]

/-! ## The new row, stretch by stretch

The main table holds the folded main row. The mask table holds five stretches and then free room.
On each stretch one formula of few terms is left of `vec_cs_c` and `vec_cs_d`. The row of draw
number i on the main row has the power 2 + 3 i of theta, the row on the carried mask 3 + 3 i, the
row on the fresh mask 4 + 3 i. -/

section
variable (old new : Stage) (s : SRow) (sample : GRow) (xs : List ℕ) (theta : E) (cl : ℕ → Col)

/-- The main table, at entry j of the folded main row. -/
theorem cs_at_main (j : ℕ) (hj : j < old.C.l) (hn : j < 2 ^ new.k * new.C.l) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).c j
      = vec s.c j + toE theta * vec sample.c j + ∑ i ∈ Finset.range xs.length,
          toE theta ^ (2 + 3 * i) * wM old.C (xs.getD i 0) j := by
  rw [vec_cs_c, cut_of_lt hn, cut_of_lt hj]

variable (hfit : 2 * old.Z.l + old.C.r + 2 * old.Z.r ≤ 2 ^ new.h * new.Z.l)
include hfit

/-- The mask table, at entry j of the folded carried mask row. -/
theorem cs_at_mask (j : ℕ) (hj : j < old.Z.l) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d j
      = vec s.d0 j + toE theta * vec sample.d j + ∑ i ∈ Finset.range xs.length,
          toE theta ^ (3 + 3 * i) * wM old.Z (cp old.Z (xs.getD i 0)) j := by
  rw [vec_cs_d, cut_of_lt (by omega)]
  simp only [cut_of_lt hj, moved_of_lt hj, moved_of_lt (show j < 2 * old.Z.l by omega),
    moved_of_lt (show j < 2 * old.Z.l + old.C.r by omega),
    moved_of_lt (show j < 2 * old.Z.l + old.C.r + old.Z.r by omega), zero_add, add_zero, mul_zero]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- The mask table, at entry j of the folded fresh mask row. -/
theorem cs_at_fresh (j : ℕ) (hj : j < old.Z.l) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d (old.Z.l + j)
      = vec s.d1 j + toE theta * vec sample.d (old.Z.l + j) + ∑ i ∈ Finset.range xs.length,
          toE theta ^ (4 + 3 * i) * wM old.Z (cp old.Z (xs.getD i 0)) j := by
  rw [vec_cs_d, cut_of_lt (by omega)]
  simp only [cut_of_le (Nat.le_add_right old.Z.l j), moved_add, cut_of_lt hj,
    wM_of_le (Nat.le_add_right old.Z.l j),
    moved_of_lt (show old.Z.l + j < 2 * old.Z.l by omega),
    moved_of_lt (show old.Z.l + j < 2 * old.Z.l + old.C.r by omega),
    moved_of_lt (show old.Z.l + j < 2 * old.Z.l + old.C.r + old.Z.r by omega), zero_add, add_zero,
    mul_zero]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- The mask table, at entry q of the folded main row's tail. -/
theorem cs_at_tail (q : ℕ) (hq : q < old.C.r) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d (2 * old.Z.l + q)
      = toE theta * vec sample.d (2 * old.Z.l + q) + ∑ i ∈ Finset.range xs.length,
          toE theta ^ (2 + 3 * i) * wT old.C (xs.getD i 0) q := by
  rw [vec_cs_d, cut_of_lt (by omega)]
  simp only [cut_of_le (show old.Z.l ≤ 2 * old.Z.l + q by omega), moved_add,
    moved_of_le (show old.Z.l ≤ 2 * old.Z.l + q by omega),
    cut_of_le (show old.Z.l ≤ 2 * old.Z.l + q - old.Z.l by omega),
    wM_of_le (show old.Z.l ≤ 2 * old.Z.l + q by omega),
    wM_of_le (show old.Z.l ≤ 2 * old.Z.l + q - old.Z.l by omega),
    moved_of_lt (show 2 * old.Z.l + q < 2 * old.Z.l + old.C.r by omega),
    moved_of_lt (show 2 * old.Z.l + q < 2 * old.Z.l + old.C.r + old.Z.r by omega), zero_add,
    add_zero, mul_zero]

/-- The mask table, at entry q of the folded carried mask row's tail. -/
theorem cs_at_maskTail (q : ℕ) (hq : q < old.Z.r) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d (2 * old.Z.l + old.C.r + q)
      = toE theta * vec sample.d (2 * old.Z.l + old.C.r + q) + ∑ i ∈ Finset.range xs.length,
          toE theta ^ (3 + 3 * i) * wT old.Z (cp old.Z (xs.getD i 0)) q := by
  rw [vec_cs_d, cut_of_lt (by omega)]
  simp only [cut_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + q by omega), moved_add,
    moved_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + q by omega),
    moved_of_le (show 2 * old.Z.l ≤ 2 * old.Z.l + old.C.r + q by omega),
    cut_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + q - old.Z.l by omega),
    wT_of_le (show old.C.r ≤ 2 * old.Z.l + old.C.r + q - 2 * old.Z.l by omega),
    wM_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + q by omega),
    wM_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + q - old.Z.l by omega),
    moved_of_lt (show 2 * old.Z.l + old.C.r + q < 2 * old.Z.l + old.C.r + old.Z.r by omega),
    zero_add, add_zero, mul_zero]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

/-- The mask table, at entry q of the folded fresh mask row's tail. -/
theorem cs_at_freshTail (q : ℕ) (hq : q < old.Z.r) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d
        (2 * old.Z.l + old.C.r + old.Z.r + q)
      = toE theta * vec sample.d (2 * old.Z.l + old.C.r + old.Z.r + q)
        + ∑ i ∈ Finset.range xs.length,
            toE theta ^ (4 + 3 * i) * wT old.Z (cp old.Z (xs.getD i 0)) q := by
  rw [vec_cs_d, cut_of_lt (by omega)]
  simp only [cut_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + old.Z.r + q by omega), moved_add,
    moved_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + old.Z.r + q by omega),
    moved_of_le (show 2 * old.Z.l ≤ 2 * old.Z.l + old.C.r + old.Z.r + q by omega),
    moved_of_le (show 2 * old.Z.l + old.C.r ≤ 2 * old.Z.l + old.C.r + old.Z.r + q by omega),
    cut_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + old.Z.r + q - old.Z.l by omega),
    wT_of_le (show old.C.r ≤ 2 * old.Z.l + old.C.r + old.Z.r + q - 2 * old.Z.l by omega),
    wT_of_le
      (show old.Z.r ≤ 2 * old.Z.l + old.C.r + old.Z.r + q - (2 * old.Z.l + old.C.r) by omega),
    wM_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + old.Z.r + q by omega),
    wM_of_le (show old.Z.l ≤ 2 * old.Z.l + old.C.r + old.Z.r + q - old.Z.l by omega),
    zero_add, add_zero, mul_zero]
  refine congrArg (_ + ·) (Finset.sum_congr rfl fun i _ => ?_)
  ring

omit hfit in
/-- The mask table after the five stretches: the sample's row alone. -/
theorem cs_at_free (j : ℕ) (hj : 2 * old.Z.l + old.C.r + 2 * old.Z.r ≤ j) :
    vec (sumRows .two theta (allRows .two old new s sample xs cl)).d j
      = cut (2 ^ new.h * new.Z.l) (fun j => toE theta * vec sample.d j) j := by
  rw [vec_cs_d]
  unfold cut
  split
  · simp only [if_neg (show ¬ j < old.Z.l by omega),
      moved_of_le (show old.Z.l ≤ j by omega), moved_of_le (show 2 * old.Z.l ≤ j by omega),
      moved_of_le (show 2 * old.Z.l + old.C.r ≤ j by omega),
      moved_of_le (show 2 * old.Z.l + old.C.r + old.Z.r ≤ j by omega),
      if_neg (show ¬ j - old.Z.l < old.Z.l by omega),
      wT_of_le (show old.C.r ≤ j - 2 * old.Z.l by omega),
      wT_of_le (show old.Z.r ≤ j - (2 * old.Z.l + old.C.r) by omega),
      wT_of_le (show old.Z.r ≤ j - (2 * old.Z.l + old.C.r + old.Z.r) by omega),
      wM_of_le (show old.Z.l ≤ j by omega), wM_of_le (show old.Z.l ≤ j - old.Z.l by omega),
      zero_add, add_zero, mul_zero, Finset.sum_const_zero]
  · rfl

end

end OnBytes.Slice

#print axioms OnBytes.Slice.moved_zero
#print axioms OnBytes.Slice.cut_add
#print axioms OnBytes.Slice.cut_of_lt
#print axioms OnBytes.Slice.cut_of_le
#print axioms OnBytes.Slice.moved_of_lt
#print axioms OnBytes.Slice.moved_of_le
#print axioms OnBytes.Slice.moved_add
#print axioms OnBytes.Slice.wM_of_le
#print axioms OnBytes.Slice.wT_of_le
#print axioms OnBytes.Slice.lst_genM
#print axioms OnBytes.Slice.lst_genT
#print axioms OnBytes.Slice.lst_toList
#print axioms OnBytes.Slice.lst_fitL
#print axioms OnBytes.Slice.size_layAt
#print axioms OnBytes.Slice.vec_layAt
#print axioms OnBytes.Slice.toE_yOf_main
#print axioms OnBytes.Slice.toE_foldV_take
#print axioms OnBytes.Slice.toE_yOf_mask
#print axioms OnBytes.Slice.toE_yOf_fresh
#print axioms OnBytes.Slice.csRows_some
#print axioms OnBytes.Slice.csRows_none
#print axioms OnBytes.Slice.csRows_congr
#print axioms OnBytes.Slice.csStep_congr
#print axioms OnBytes.Slice.length_allRows
#print axioms OnBytes.Slice.csStep_some
#print axioms OnBytes.Slice.vec_carried_c
#print axioms OnBytes.Slice.vec_carried_d
#print axioms OnBytes.Slice.vec_smp_c
#print axioms OnBytes.Slice.vec_smp_d
#print axioms OnBytes.Slice.draw_c
#print axioms OnBytes.Slice.draw_d
#print axioms OnBytes.Slice.draw_t
#print axioms OnBytes.Slice.sum_eq_horner
#print axioms OnBytes.Slice.horner_draws
#print axioms OnBytes.Slice.sum_by_draws
#print axioms OnBytes.Slice.toE_cs_t
#print axioms OnBytes.Slice.vec_cs_c
#print axioms OnBytes.Slice.vec_cs_d
#print axioms OnBytes.Slice.cs_at_main
#print axioms OnBytes.Slice.cs_at_mask
#print axioms OnBytes.Slice.cs_at_fresh
#print axioms OnBytes.Slice.cs_at_tail
#print axioms OnBytes.Slice.cs_at_maskTail
#print axioms OnBytes.Slice.cs_at_freshTail
#print axioms OnBytes.Slice.cs_at_free
