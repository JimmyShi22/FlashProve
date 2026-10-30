-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Slice/SimSample.lean: what the format's sample rows compute, in the field.

A sample of an oracle message is one element: the prover's answer to a point z and a factor beta
that the verifier draws after the message. The answer is a linear form of the message's entries. The
format's arithmetic writes the coefficients of that form out as arrays: `Fmt.M1.sampleRow` for a
message with mask rows, `Fmt.M2.sampleOf` for all three kinds of message. This file reads these
arrays in the field `GE` and gives every entry as a closed form.

The closed form. An entry that is no pad has the weight eqW of a vertex of a cube at the point z.
A pad has the factor beta and no weight of the point.
 - With mask rows the cube has a = max Am Az + 1 coordinates. Entry j of the main table is at the
   vertex j. Entry i of the mask table is at the vertex 2^(a - 1) + i. The pad is the last entry of
   the mask table.
 - Without mask rows the cube has the Am coordinates of the main table's own index. The pad is the
   last place of the last real row, for rows over the extension field. For rows over the base field
   it is the last three places of that row, under beta, beta X and beta X^2.

The library's sample row with a pad (Cb.Ood.Sample.pad) has the coefficient Alg.eqk z (pl j) at an
entry j and b beta * w i at a pad entry i. padRow is that row with one pad entry, w = 1, and the
factors other than 0. padRow3 is that row with three pad entries, w = (1, X, X^2). The last theorems
say that the format's arrays hold the coefficients of these rows.

Main definitions: mainBits, padRow, basis3, padRow3.
Main theorems. Tools: vec_setIfInBounds, toE_frontE, eqW_add, eqW_top, padAt_inj, padAt_lt. Closed
forms: vec_sampleRow_c, vec_sampleRow_d, sampleRow_t, sampleOf_masks, sampleOf_snd,
vec_sampleOf_overE, vec_sampleOf_overF. Against the library's row: padRow_entry, padRow_pad,
sampleRow_c_entry, sampleRow_d_entry, sampleRow_d_pad, sampleOf_overE_entry, sampleOf_overE_pad,
padRow3_entry, padRow3_pad, sampleOf_overF_entry, sampleOf_overF_pad.

Not claimed. Nothing on a protocol, and nothing on the other field of the format. The point must
have all the coordinates that a table's index needs; nothing is said of a shorter point.
-/
import OnBytes.Slice.SimBasic
import OnBytes.Slice.Corners
import Fmt.M2Send
import Cb.Gen.OodDecPad
noncomputable section -- Lean tags what it cannot compile

set_option autoImplicit false

namespace OnBytes.Slice
open Fmt.M1 Fmt.M2

/-! ## Small tools -/

/-- An array with one entry replaced, read in the field. Nothing is replaced beyond the end. -/
theorem vec_setIfInBounds (v : Array E) (k : ℕ) (x : E) (i : ℕ) :
    vec (v.setIfInBounds k x) i = if i = k ∧ k < v.size then toE x else vec v i := by
  unfold vec ent
  by_cases hik : i = k
  · subst hik
    by_cases hs : i < v.size
    · simp [hs]
    · simp [hs]
  · have hki : ¬ k = i := fun h => hik h.symm
    simp [hik, Array.getD_eq_getD_getElem?, hki]

/-- A coordinate of a point, read in the field. -/
theorem toE_coE (z : List E) (t : ℕ) : toE (coE z t) = lst z t := rfl

/-- A product that is built up from the left, read in the field. -/
theorem toE_foldl_mulE (g : ℕ → E) (a : E) (n : ℕ) :
    toE ((List.range n).foldl (fun acc t => Fmt.Fld.two.mulE acc (g t)) a) =
      toE a * ∏ t ∈ Finset.range n, toE (g t) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, toE_mulE, ih,
      Finset.prod_range_succ, mul_assoc]

/-- `frontE`, read in the field: one factor 1 - z_t for each t from lo up to hi - 1. -/
theorem toE_frontE (z : List E) (lo hi : ℕ) :
    toE (frontE .two z lo hi) = ∏ t ∈ Finset.range (hi - lo), (1 - lst z (lo + t)) := by
  unfold frontE
  rw [toE_foldl_mulE (fun t => Fmt.Fld.two.subE Fmt.Fld.oneE (coE z (lo + t))), toE_oneE, one_mul]
  refine Finset.prod_congr rfl fun t _ => ?_
  rw [toE_subE, toE_oneE, toE_coE]

/-! ## The weight on a larger cube -/

/-- A vertex below 2^n on a cube with k more coordinates: each of these gives the factor 1 - z_t. -/
theorem eqW_add (n k : ℕ) (z : ℕ → GE) (i : ℕ) (hi : i < 2 ^ n) :
    eqW (n + k) z i = eqW n z i * ∏ t ∈ Finset.range k, (1 - z (n + t)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hlt : i < 2 ^ (n + k) := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))
    rw [← Nat.add_assoc, eqW_succ, ih, Nat.testBit_lt_two_pow hlt, Finset.prod_range_succ]
    simp [mul_assoc]

/-- The vertex 2^n + i with i below 2^n, on the cube with n + 1 coordinates. -/
theorem eqW_top (n : ℕ) (z : ℕ → GE) (i : ℕ) (hi : i < 2 ^ n) :
    eqW (n + 1) z (2 ^ n + i) = eqW n z i * z n := by
  have hbit : (2 ^ n + i).testBit n = true := by
    rw [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hi]; rfl
  have hmod : (2 ^ n + i) % 2 ^ n = i := by
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt hi]
  rw [eqW_succ, hbit, ← eqW_mod n z (2 ^ n + i), hmod]
  simp

/-! ## The sample row of a message with mask rows -/

/-- The form on the main table: entry j has the weight of the vertex j. -/
theorem vec_sampleRow_c (Am Az : ℕ) (z : List E) (beta y : E) (j : ℕ) (hz : Am ≤ z.length) :
    vec (sampleRow .two Am Az z beta y).c j =
      if j < 2 ^ Am then eqW (nCoord Am Az) (lst z) j else 0 := by
  have hlen : (z.take Am).length = Am := by simp [hz]
  show vec (pv .two _ (z.take Am)) j = _
  rw [vec_pv, hlen]
  by_cases hj : j < 2 ^ Am
  · rw [if_pos hj, if_pos hj]
    obtain ⟨k, hk⟩ : ∃ k, max Am Az = Am + k := ⟨max Am Az - Am, by omega⟩
    have hn : nCoord Am Az = Am + (k + 1) := by unfold nCoord; omega
    have hn1 : nCoord Am Az - 1 = Am + k := by omega
    rw [hn1, hn, eqW_add Am (k + 1) (lst z) j hj, Finset.prod_range_succ, toE_mulE, toE_subE,
      toE_oneE, toE_coE, toE_frontE, Nat.add_sub_cancel_left,
      eqW_congr Am (lst (z.take Am)) (lst z) j fun t ht => lst_take Am z t ht]
    ring
  · rw [if_neg hj, if_neg hj]

/-- The form on the mask table: entry i has the weight of the vertex 2^(a - 1) + i, but the last
entry, the pad, has the factor beta. -/
theorem vec_sampleRow_d (Am Az : ℕ) (z : List E) (beta y : E) (i : ℕ) (hz : Az ≤ z.length) :
    vec (sampleRow .two Am Az z beta y).d i =
      if i + 1 < 2 ^ Az then eqW (nCoord Am Az) (lst z) (2 ^ (nCoord Am Az - 1) + i)
      else if i + 1 = 2 ^ Az then toE beta else 0 := by
  have hlen : (z.take Az).length = Az := by simp [hz]
  have hpos : 0 < 2 ^ Az := Nat.pos_of_ne_zero (by positivity)
  show vec ((pv .two _ (z.take Az)).setIfInBounds (2 ^ Az - 1) beta) i = _
  rw [vec_setIfInBounds, size_pv, hlen, vec_pv, hlen]
  by_cases h1 : i + 1 < 2 ^ Az
  · have hne : ¬ (i = 2 ^ Az - 1 ∧ 2 ^ Az - 1 < 2 ^ Az) := by omega
    have hi : i < 2 ^ Az := by omega
    rw [if_neg hne, if_pos hi, if_pos h1]
    obtain ⟨k, hk⟩ : ∃ k, max Am Az = Az + k := ⟨max Am Az - Az, by omega⟩
    have hn : nCoord Am Az = Az + k + 1 := by unfold nCoord; omega
    have hn1 : nCoord Am Az - 1 = Az + k := by omega
    have hik : i < 2 ^ (Az + k) := lt_of_lt_of_le hi (Nat.pow_le_pow_right (by omega) (by omega))
    rw [hn1, hn, eqW_top (Az + k) (lst z) i hik, eqW_add Az k (lst z) i hi, toE_mulE, toE_coE,
      toE_frontE, Nat.add_sub_cancel_left,
      eqW_congr Az (lst (z.take Az)) (lst z) i fun t ht => lst_take Az z t ht]
    ring
  · rw [if_neg h1]
    by_cases h2 : i + 1 = 2 ^ Az
    · have hy : i = 2 ^ Az - 1 ∧ 2 ^ Az - 1 < 2 ^ Az := by omega
      rw [if_pos hy, if_pos h2]
    · have hne : ¬ (i = 2 ^ Az - 1 ∧ 2 ^ Az - 1 < 2 ^ Az) := by omega
      have hi : ¬ i < 2 ^ Az := by omega
      rw [if_neg hne, if_neg hi, if_neg h2]

/-- The target of the row is the answer. -/
theorem sampleRow_t (f : Fmt.Fld) (Am Az : ℕ) (z : List E) (beta y : E) :
    (sampleRow f Am Az z beta y).t = y := rfl

/-- The main table's form has 2^Am entries. -/
theorem size_sampleRow_c (f : Fmt.Fld) (Am Az : ℕ) (z : List E) (beta y : E)
    (hz : Am ≤ z.length) : (sampleRow f Am Az z beta y).c.size = 2 ^ Am := by
  show (pv f _ (z.take Am)).size = _
  rw [size_pv]; simp [hz]

/-- The mask table's form has 2^Az entries. -/
theorem size_sampleRow_d (f : Fmt.Fld) (Am Az : ℕ) (z : List E) (beta y : E)
    (hz : Az ≤ z.length) : (sampleRow f Am Az z beta y).d.size = 2 ^ Az := by
  show ((pv f _ (z.take Az)).setIfInBounds _ _).size = _
  rw [Array.size_setIfInBounds, size_pv]; simp [hz]

/-! ## The sample row of a message of any kind -/

/-- The index bits of a message's own main table: those of its rows, then those of a row's l
places. -/
def mainBits (l : ℕ) (m : Mem) : ℕ := clog m.rows + Nat.log2 l

/-- Different places of the last real row have different indices. -/
theorem padAt_inj (m : Mem) (p q : ℕ) : padAt m p = padAt m q ↔ p = q := by
  unfold padAt
  have hpos : 0 < 2 ^ clog m.rows := Nat.pos_of_ne_zero (by positivity)
  constructor
  · intro h
    exact Nat.eq_of_mul_eq_mul_left hpos (Nat.add_left_cancel h)
  · intro h
    rw [h]

/-- If a row has 2^k places, every place of the last real row lies in the table. -/
theorem padAt_lt (m : Mem) (k p : ℕ) (hr : 1 ≤ m.rows) (hp : p < 2 ^ k) :
    padAt m p < 2 ^ mainBits (2 ^ k) m := by
  have hlog : Nat.log2 (2 ^ k) = k := by simp
  have hrows := le_two_pow_clog m.rows
  unfold padAt mainBits
  rw [hlog, Nat.pow_add]
  calc m.rows - 1 + 2 ^ clog m.rows * p < 2 ^ clog m.rows + 2 ^ clog m.rows * p := by omega
    _ = 2 ^ clog m.rows * (p + 1) := by ring
    _ ≤ 2 ^ clog m.rows * 2 ^ k := Nat.mul_le_mul_left _ hp

/-- With mask rows: the row of the first part of this file. -/
theorem sampleOf_masks (f : Fmt.Fld) (l lz : ℕ) (m : Mem) (z : List E) (beta y : E)
    (h : m.masks ≠ 0) :
    sampleOf f l lz m z beta y =
      ((sampleRow f (mainBits l m) (clog m.masks + Nat.log2 lz) z beta y).c,
        (sampleRow f (mainBits l m) (clog m.masks + Nat.log2 lz) z beta y).d) := by
  unfold sampleOf mainBits
  simp [h]

/-- Without mask rows there is no form on a mask table. -/
theorem sampleOf_snd (f : Fmt.Fld) (l lz : ℕ) (m : Mem) (z : List E) (beta y : E)
    (h : m.masks = 0) : (sampleOf f l lz m z beta y).2 = #[] := by
  unfold sampleOf
  cases m.overE <;> simp [h]

/-- Without mask rows, rows over the extension field: entry i has the weight of the vertex i, but
the pad has the factor beta. -/
theorem vec_sampleOf_overE (l lz : ℕ) (m : Mem) (z : List E) (beta y : E) (i : ℕ)
    (h : m.masks = 0) (hE : m.overE = true) (hz : mainBits l m ≤ z.length)
    (hp : padAt m (l - 1) < 2 ^ mainBits l m) :
    vec (sampleOf .two l lz m z beta y).1 i =
      if i = padAt m (l - 1) then toE beta
      else if i < 2 ^ mainBits l m then eqW (mainBits l m) (lst z) i else 0 := by
  have hlen : (z.take (mainBits l m)).length = mainBits l m := by simp [hz]
  have hw : (sampleOf .two l lz m z beta y).1 =
      (pv .two Fmt.Fld.oneE (z.take (mainBits l m))).setIfInBounds (padAt m (l - 1)) beta := by
    unfold sampleOf mainBits
    simp [h, hE]
  rw [hw, vec_setIfInBounds, size_pv, hlen, vec_pv, hlen, toE_oneE, one_mul,
    eqW_congr (mainBits l m) (lst (z.take (mainBits l m))) (lst z) i fun t ht =>
      lst_take (mainBits l m) z t ht]
  by_cases hi : i = padAt m (l - 1)
  · rw [if_pos ⟨hi, hp⟩, if_pos hi]
  · rw [if_neg (fun hh => hi hh.1), if_neg hi]

/-- Without mask rows, rows over the base field: entry i has the weight of the vertex i, but the
three pads have the factors beta, beta X and beta X^2. -/
theorem vec_sampleOf_overF (l lz : ℕ) (m : Mem) (z : List E) (beta y : E) (i : ℕ)
    (h : m.masks = 0) (hE : m.overE = false) (hz : mainBits l m ≤ z.length)
    (hp : padAt m (l - 1) < 2 ^ mainBits l m) :
    vec (sampleOf .two l lz m z beta y).1 i =
      if i = padAt m (l - 1) then toE beta * toE (0, 0, 1)
      else if i = padAt m (l - 2) then toE beta * toE (0, 1, 0)
      else if i = padAt m (l - 3) then toE beta
      else if i < 2 ^ mainBits l m then eqW (mainBits l m) (lst z) i else 0 := by
  have hlen : (z.take (mainBits l m)).length = mainBits l m := by simp [hz]
  have hmono : ∀ p q, p ≤ q → padAt m p ≤ padAt m q := fun p q hpq => by
    unfold padAt
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hpq) _
  have hp2 : padAt m (l - 2) < 2 ^ mainBits l m := lt_of_le_of_lt (hmono _ _ (by omega)) hp
  have hp3 : padAt m (l - 3) < 2 ^ mainBits l m := lt_of_le_of_lt (hmono _ _ (by omega)) hp
  have hw : (sampleOf .two l lz m z beta y).1 =
      (((pv .two Fmt.Fld.oneE (z.take (mainBits l m))).setIfInBounds (padAt m (l - 3))
        beta).setIfInBounds (padAt m (l - 2)) (Fmt.Fld.two.mulE beta (0, 1, 0))).setIfInBounds
        (padAt m (l - 1)) (Fmt.Fld.two.mulE beta (0, 0, 1)) := by
    unfold sampleOf mainBits
    simp [h, hE]
  rw [hw, vec_setIfInBounds, vec_setIfInBounds, vec_setIfInBounds, Array.size_setIfInBounds,
    Array.size_setIfInBounds, size_pv, hlen, vec_pv, hlen, toE_oneE, one_mul, toE_mulE, toE_mulE,
    eqW_congr (mainBits l m) (lst (z.take (mainBits l m))) (lst z) i fun t ht =>
      lst_take (mainBits l m) z t ht]
  simp only [hp, hp2, hp3, and_true]

/-! ## The library's sample row with a pad -/

/-- The library's sample row with one pad entry, at a point of a coordinates. Entry j is at the
vertex of the binary digits of idx j, the lowest first. The factor on the pad is not 0. -/
@[reducible] def padRow (a : ℕ) {J : Type} (idx : J → ℕ) :
    Cb.Ood.Sample GE (J ⊕ Unit) :=
  Cb.Ood.Sample.pad GE (Fin a) J Unit GEˣ (fun j t => (idx j).testBit t.val) (fun _ => 1) Units.val

/-- Its coefficient at an entry. -/
theorem padRow_entry (a : ℕ) {J : Type} (idx : J → ℕ) (z : ℕ → GE) (β : GEˣ) (j : J) :
    (padRow a idx).mat (fun t => z t.val, β) () (Sum.inl j) = eqW a z (idx j) := rfl

/-- Its coefficient at the pad. -/
theorem padRow_pad (a : ℕ) {J : Type} (idx : J → ℕ) (z : ℕ → GE) (β : GEˣ) :
    (padRow a idx).mat (fun t => z t.val, β) () (Sum.inr ()) = β.val := by
  show β.val * 1 = β.val
  rw [mul_one]

/-- With mask rows: an entry of the main table whose vertex is its own index. -/
theorem sampleRow_c_entry (Am Az : ℕ) (z : List E) (beta y : E) (β : GEˣ) {J : Type}
    (idx : J → ℕ) (j : J) (hz : Am ≤ z.length) (hj : idx j < 2 ^ Am) :
    vec (sampleRow .two Am Az z beta y).c (idx j) =
      (padRow (nCoord Am Az) idx).mat (fun t => lst z t.val, β) () (Sum.inl j) := by
  rw [vec_sampleRow_c Am Az z beta y (idx j) hz, if_pos hj, padRow_entry]

/-- With mask rows: entry i of the mask table, which is no pad, whose vertex is 2^(a - 1) + i. -/
theorem sampleRow_d_entry (Am Az : ℕ) (z : List E) (beta y : E) (β : GEˣ) {J : Type}
    (idx : J → ℕ) (j : J) (i : ℕ) (hz : Az ≤ z.length) (hi : i + 1 < 2 ^ Az)
    (hj : idx j = 2 ^ (nCoord Am Az - 1) + i) :
    vec (sampleRow .two Am Az z beta y).d i =
      (padRow (nCoord Am Az) idx).mat (fun t => lst z t.val, β) () (Sum.inl j) := by
  rw [vec_sampleRow_d Am Az z beta y i hz, if_pos hi, padRow_entry, hj]

/-- With mask rows: the pad, if beta is read as the library's factor. -/
theorem sampleRow_d_pad (Am Az : ℕ) (z : List E) (beta y : E) (β : GEˣ) {J : Type}
    (idx : J → ℕ) (hz : Az ≤ z.length) (hβ : toE beta = β.val) :
    vec (sampleRow .two Am Az z beta y).d (2 ^ Az - 1) =
      (padRow (nCoord Am Az) idx).mat (fun t => lst z t.val, β) () (Sum.inr ()) := by
  have hpos : 0 < 2 ^ Az := Nat.pos_of_ne_zero (by positivity)
  have h1 : ¬ (2 ^ Az - 1 + 1 < 2 ^ Az) := by omega
  have h2 : 2 ^ Az - 1 + 1 = 2 ^ Az := by omega
  rw [vec_sampleRow_d Am Az z beta y _ hz, if_neg h1, if_pos h2, padRow_pad, hβ]

/-- Without mask rows, rows over the extension field: at an entry that is no pad the format's array
holds the coefficient of the library's row. -/
theorem sampleOf_overE_entry (l lz : ℕ) (m : Mem) (z : List E) (beta y : E) (β : GEˣ)
    {J : Type} (idx : J → ℕ) (j : J)
    (h : m.masks = 0) (hE : m.overE = true) (hz : mainBits l m ≤ z.length)
    (hp : padAt m (l - 1) < 2 ^ mainBits l m)
    (hj : idx j < 2 ^ mainBits l m) (hne : idx j ≠ padAt m (l - 1)) :
    vec (sampleOf .two l lz m z beta y).1 (idx j) =
      (padRow (mainBits l m) idx).mat (fun t => lst z t.val, β) () (Sum.inl j) := by
  rw [vec_sampleOf_overE l lz m z beta y (idx j) h hE hz hp, if_neg hne, if_pos hj, padRow_entry]

/-- And at the pad, if beta is read as the library's factor. -/
theorem sampleOf_overE_pad (l lz : ℕ) (m : Mem) (z : List E) (beta y : E) (β : GEˣ)
    {J : Type} (idx : J → ℕ)
    (h : m.masks = 0) (hE : m.overE = true) (hz : mainBits l m ≤ z.length)
    (hp : padAt m (l - 1) < 2 ^ mainBits l m) (hβ : toE beta = β.val) :
    vec (sampleOf .two l lz m z beta y).1 (padAt m (l - 1)) =
      (padRow (mainBits l m) idx).mat (fun t => lst z t.val, β) () (Sum.inr ()) := by
  rw [vec_sampleOf_overE l lz m z beta y _ h hE hz hp, if_pos rfl, padRow_pad, hβ]

/-! ## Three pad entries over the base field -/

/-- 1, X, X^2: the elements under which three entries of the base field make one element of the
extension field. -/
def basis3 (i : Fin 3) : GE :=
  if i.val = 0 then 1 else if i.val = 1 then toE (0, 1, 0) else toE (0, 0, 1)

/-- The library's sample row with three pad entries under 1, X, X^2. -/
@[reducible] def padRow3 (a : ℕ) {J : Type} (idx : J → ℕ) :
    Cb.Ood.Sample GE (J ⊕ Fin 3) :=
  Cb.Ood.Sample.pad GE (Fin a) J (Fin 3) GEˣ (fun j t => (idx j).testBit t.val) basis3 Units.val

/-- Its coefficient at an entry. -/
theorem padRow3_entry (a : ℕ) {J : Type} (idx : J → ℕ) (z : ℕ → GE) (β : GEˣ) (j : J) :
    (padRow3 a idx).mat (fun t => z t.val, β) () (Sum.inl j) = eqW a z (idx j) := rfl

/-- Its coefficient at a pad entry. -/
theorem padRow3_pad (a : ℕ) {J : Type} (idx : J → ℕ) (z : ℕ → GE) (β : GEˣ) (i : Fin 3) :
    (padRow3 a idx).mat (fun t => z t.val, β) () (Sum.inr i) = β.val * basis3 i := rfl

/-- Without mask rows, rows over the base field: at an entry that is no pad the format's array holds
the coefficient of the library's row. -/
theorem sampleOf_overF_entry (l lz : ℕ) (m : Mem) (z : List E) (beta y : E) (β : GEˣ)
    {J : Type} (idx : J → ℕ) (j : J)
    (h : m.masks = 0) (hE : m.overE = false) (hz : mainBits l m ≤ z.length)
    (hp : padAt m (l - 1) < 2 ^ mainBits l m) (hj : idx j < 2 ^ mainBits l m)
    (h1 : idx j ≠ padAt m (l - 1)) (h2 : idx j ≠ padAt m (l - 2))
    (h3 : idx j ≠ padAt m (l - 3)) :
    vec (sampleOf .two l lz m z beta y).1 (idx j) =
      (padRow3 (mainBits l m) idx).mat (fun t => lst z t.val, β) () (Sum.inl j) := by
  rw [vec_sampleOf_overF l lz m z beta y (idx j) h hE hz hp, if_neg h1, if_neg h2, if_neg h3,
    if_pos hj, padRow3_entry]

/-- And at the three pads, the places l - 3, l - 2, l - 1 of the last real row, if beta is read as
the library's factor. -/
theorem sampleOf_overF_pad (l lz : ℕ) (m : Mem) (z : List E) (beta y : E) (β : GEˣ)
    {J : Type} (idx : J → ℕ) (i : Fin 3)
    (h : m.masks = 0) (hE : m.overE = false) (hz : mainBits l m ≤ z.length)
    (hp : padAt m (l - 1) < 2 ^ mainBits l m) (hl : 3 ≤ l) (hβ : toE beta = β.val) :
    vec (sampleOf .two l lz m z beta y).1 (padAt m (l - 3 + i.val)) =
      (padRow3 (mainBits l m) idx).mat (fun t => lst z t.val, β) () (Sum.inr i) := by
  have hi := i.isLt
  rw [vec_sampleOf_overF l lz m z beta y _ h hE hz hp, padRow3_pad, hβ]
  simp only [padAt_inj]
  unfold basis3
  by_cases h0 : i.val = 0
  · have a1 : ¬ (l - 3 + i.val = l - 1) := by omega
    have a2 : ¬ (l - 3 + i.val = l - 2) := by omega
    have a3 : l - 3 + i.val = l - 3 := by omega
    rw [if_neg a1, if_neg a2, if_pos a3, if_pos h0, mul_one]
  · by_cases h1 : i.val = 1
    · have a1 : ¬ (l - 3 + i.val = l - 1) := by omega
      have a2 : l - 3 + i.val = l - 2 := by omega
      rw [if_neg a1, if_pos a2, if_neg h0, if_pos h1]
    · have a1 : l - 3 + i.val = l - 1 := by omega
      rw [if_pos a1, if_neg h0, if_neg h1]

end OnBytes.Slice

#print axioms OnBytes.Slice.vec_sampleRow_c
#print axioms OnBytes.Slice.vec_sampleRow_d
#print axioms OnBytes.Slice.vec_sampleOf_overE
#print axioms OnBytes.Slice.vec_sampleOf_overF
#print axioms OnBytes.Slice.sampleOf_overE_entry
#print axioms OnBytes.Slice.sampleOf_overE_pad
#print axioms OnBytes.Slice.sampleRow_c_entry
#print axioms OnBytes.Slice.sampleRow_d_entry
#print axioms OnBytes.Slice.sampleRow_d_pad
#print axioms OnBytes.Slice.sampleOf_overF_entry
#print axioms OnBytes.Slice.sampleOf_overF_pad
#print axioms OnBytes.Slice.padAt_lt
