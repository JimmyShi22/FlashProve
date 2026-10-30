-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/Counts.lean

The multiplicities of a lookup, as natural numbers: "count", the number of places of a call's key
vector that are not padding places and have a given row of the call's table as their chosen row;
"bit", the 32 bits of each count; and "plane", a matrix of these bits. If 5 ≤ lm ≤ kT + 5, the bit
(t, c, j) with t < 2^kT and j < 32 is the cell of plane at the address FoNums.cellRC h lm (t, c, j)
(plane_cellRC).

The setting. One lookup handles all calls of a list of calls (OnBytes/Model/Forest.lean). Call c has
a key vector of 2^(n_c) places and a table of 2^(k_c) rows. Some places are padding places. The byte
format's page docs/format/11-1-machinery.md ("Where the multiplicities are") says: each key that is
not padding is counted once, at one row whose value it equals; padding keys are not counted; bit j
of the count of row t of call c is a cell of a committed matrix of 2^lm rows. This file writes that
count down for any value h of Forest.Shape, the type in which the Lean verifier under OnBytes/Model/
keeps a lookup's public numbers. h is an arbitrary argument; five theorems assume FoNums.ok h = true
(OnBytes/Tie/Pv/Lookup/Port/FoNums.lean), and nothing else is assumed of it.

Notation. NC, kT, dT, NT, rK, cK are fields of h: the number of calls; the largest table has 2^kT
rows; a tree has 2^dT places; the number of trees; the bits of a tree's number and of a call's
number. v = dT + rK and d = kT + cK. n_c, k_c are FoNums.nOf h c and FoNums.kOf h c. lm is the
caller's number: the matrix has 2^lm rows.

By the same page a segment has two lookups: one for the calls of its list, and one for the two calls
of the smallness test. "Hits", "count", "bit" and the theorems on them read h and H and not lm, so
they speak of either lookup. "plane", "tOf", "cOf" and the theorems on them follow the format's
layout of the first lookup's bits: the page places the bits of the second (the array BZ) by another
rule.

Which places are padding places, and which row is chosen for a place, are arguments: a value H of
"Hits". "hitsOf" makes one from tables, key vectors and padding places.

Main definitions:
* "Hits": padding places and chosen rows. "count": the multiplicity of a row of a call.
  "bit": one bit of it. "plane": the matrix of the bits, by row and column; "tOf", "cOf": the table
  row and the call of a cell of that matrix.
* "firstRow": the first row below 2^k of a table that holds a value, 0 if none does. "hitsOf": the
  Hits whose chosen row is the call's padding row at a padding place and firstRow of the key
  elsewhere.
* "PubFits": the public numbers h.pub count the padding places, tree by tree. "Fits": four
  conditions on tables, key vectors and Hits: the chosen row lies in the call's own table; every
  place holds the chosen row's value; a padding place's chosen row is the padding row; PubFits.

Main theorems, each with its premises in its docstring:
* on the matrix and its address: "plane_01", "plane_cellRC", "cellRC_back", "cellRC_flat",
  "plane_outside".
* on counts and bits: "count_le", "count_lt", "count_repeat", "sum_bits", "sum_count_call",
  "sum_plane".
* on Hits that agree: "count_congr", "bit_congr", "plane_congr".
* on firstRow and hitsOf: "firstRow_spec", "firstRow_inj", "firstRow_map", "hitsOf_map".

Limits. These are specifications, not programs to run: "count" filters all 2^(n_c) places for each
row, and "firstRow" searches up to 2^k rows for each key. The file speaks of numbers, and of tables
and key vectors that are arbitrary functions. No key vector, table or padding place of a sub-proof
of the protocol occurs in it. "count" reads no key and no table: that a place's key is the value of
its chosen row is a field of "Fits", and no theorem of this file has "Fits" or "PubFits" as a
premise or a conclusion. For a number c that is no call's, FoNums.nOf reads 0, so "count" speaks of
one place; "bit" is false there if c is not below h.NC. "tOf", "cOf" and FoNums.cellRC subtract on
natural numbers: lm - 5 and kT + 5 - lm are the differences only if 5 ≤ lm ≤ kT + 5, which
"plane_cellRC", "cellRC_flat", "cellRC_back" and "sum_plane" have as premises and "plane_outside"
has not. FoNums.cellRC is that file's own description of the text of OnBytes/Model/Look.lean; no
theorem of this file compares it with a function of OnBytes/Model/ (the library's statements on it
begin at OnBytes/Tie/Pv/Lookup/Forest/FoPlane.lean). The right side of "cellRC_flat" was typed from
the format's page by hand. Where a value is in several rows of a table the format leaves the row
open; "firstRow" is one choice. Where a key is the value of no row, "firstRow" is 0, and at "hitsOf"
the place is counted at row 0: that number means nothing, and it is no test of whether the key is in
the table.

Not claimed: that a prover's committed cells are this matrix; that the C++ prover counts at
these rows; that a verifier accepts a proof made with them; that "PubFits" or "Fits" holds of any
sub-proof; any equation of the lookup argument.

-/
import OnBytes.Tie.Pv.Lookup.Port.FoNums
import Alg.Lookup
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace OnBytes.HonestTrace

open Finset
open OnBytes.Model

/-! ## The count, call by call; its bits; the planes' matrix -/

/-- For each call and each place of its key vector: whether the place is a padding place, and the
row of the call's table that is chosen for it. Booleans and natural numbers alone: no key, no table
and no element of a finite field occurs. -/
structure Hits where
  /-- pad c i: place i of call c's key vector is a padding place. -/
  pad : ℕ → ℕ → Bool
  /-- row c i: the row of call c's table that is chosen for place i of call c's key vector. -/
  row : ℕ → ℕ → ℕ

/-- The number of places of call c's key vector that are not padding places and whose chosen row
is t. For a number c that is no call's, FoNums.nOf reads 0, so one place is looked at and the value
can be 1; bit is false there if c is not below h.NC. -/
def count (h : Forest.Shape) (H : Hits) (c t : ℕ) : ℕ :=
  ((range (2 ^ FoNums.nOf h c)).filter fun i => H.pad c i = false ∧ H.row c i = t).card

/-- Bit j of count h H c t; false if c is not below h.NC, and false if j is not below 32. -/
def bit (h : Forest.Shape) (H : Hits) (t c j : ℕ) : Bool :=
  decide (c < h.NC) && decide (j < 32) && (count h H c t).testBit j

/-- The table row that the cell (r, col) of a planes' matrix of 2^lm rows belongs to. -/
def tOf (h : Forest.Shape) (lm r col : ℕ) : ℕ :=
  col % 2 ^ (h.kT + 5 - lm) * 2 ^ (lm - 5) + r / 32

/-- The call that column col of a planes' matrix of 2^lm rows belongs to. -/
def cOf (h : Forest.Shape) (lm col : ℕ) : ℕ := col / 2 ^ (h.kT + 5 - lm)

/-- The planes' matrix of 2^lm rows as a function of row and column, with values 0 and 1. It is 0
from row 2^lm on. -/
def plane (h : Forest.Shape) (lm : ℕ) (H : Hits) (r col : ℕ) : ℕ :=
  if r < 2 ^ lm ∧ bit h H (tOf h lm r col) (cOf h lm col) (r % 32) = true then 1 else 0

/-! ## The row by a formula: the first row that holds the key -/

/-- The first row below 2^k of the table T that holds x; 0 if none does. -/
def firstRow {K : Type} [DecidableEq K] (T : ℕ → K) (k : ℕ) (x : K) : ℕ :=
  ((List.range (2 ^ k)).find? fun u => decide (T u = x)).getD 0

/-- Hits from tables T, key vectors Kv and padding places pad: the chosen row of a padding place is
the call's padding row; that of every other place is firstRow of its key in the call's table. -/
def hitsOf {K : Type} [DecidableEq K] (h : Forest.Shape) (T Kv : ℕ → ℕ → K)
    (pad : ℕ → ℕ → Bool) : Hits where
  pad := pad
  row := fun c i =>
    if pad c i = true then FoNums.t0Of h c else firstRow (T c) (FoNums.kOf h c) (Kv c i)

/-! ## What is asked of a sub-proof's tables, key vectors and padding places -/

/-- For every tree y below h.NT, the public number h.pub.getD y 0 (0 beyond the array) is the number
of padding places among the 2^dT places of tree y. -/
def PubFits (h : Forest.Shape) (pad : ℕ → ℕ → Bool) : Prop :=
  ∀ y < h.NT, h.pub.getD y 0 =
    ((range (2 ^ h.dT)).filter fun x =>
      pad (FoNums.co h y) (x + 2 ^ h.dT * (y % 2 ^ FoNums.io h (FoNums.co h y))) = true).card

/-- Four conditions on tables T, key vectors K and H, for the calls below h.NC and the places below
2^(n_c): see the fields. T c t is row t of call c's table; K c i is place i of call c's key vector,
padding places included. -/
structure Fits {E : Type} (h : Forest.Shape) (T K : ℕ → ℕ → E) (H : Hits) : Prop where
  /-- the chosen row is below the length of the call's own table -/
  lt : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.row c i < 2 ^ FoNums.kOf h c
  /-- the key vector holds the chosen row's value at every place, padding places too -/
  hit : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, K c i = T c (H.row c i)
  /-- at a padding place the chosen row is the call's padding row -/
  padRow : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c, H.pad c i = true → H.row c i = FoNums.t0Of h c
  /-- the public numbers count the padding places -/
  pub : PubFits h H.pad

/-! ## Laws on counts, bits and the planes' matrix -/

/-- Every value of plane is 0 or 1. -/
theorem plane_01 (h : Forest.Shape) (lm : ℕ) (H : Hits) (r col : ℕ) :
    plane h lm H r col = 0 ∨ plane h lm H r col = 1 := by
  unfold plane
  split_ifs
  · exact Or.inr rfl
  · exact Or.inl rfl

/-- If 5 ≤ lm ≤ kT + 5, t < 2^kT and j < 32, then for every c the value of plane at the row and
column FoNums.cellRC h lm (t, c, j) is 1 if bit h H t c j is true, and 0 otherwise. (For c not
below h.NC the bit is false.) -/
theorem plane_cellRC (h : Forest.Shape) (lm : ℕ) (H : Hits) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    {t c j : ℕ} (ht : t < 2 ^ h.kT) (hj : j < 32) :
    plane h lm H (FoNums.cellRC h lm (t, c, j)).1 (FoNums.cellRC h lm (t, c, j)).2 =
      if bit h H t c j = true then 1 else 0 := by
  obtain ⟨a, rfl⟩ : ∃ a, lm = a + 5 := ⟨lm - 5, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, h.kT = a + b := ⟨h.kT - a, by omega⟩
  have e1 : a + 5 - 5 = a := by omega
  have e2 : h.kT + 5 - (a + 5) = b := by omega
  have hpa : 0 < 2 ^ a := by positivity
  have hpb : 0 < 2 ^ b := by positivity
  have hm : t % 2 ^ a < 2 ^ a := Nat.mod_lt _ hpa
  have hq : t / 2 ^ a < 2 ^ b := by
    apply Nat.div_lt_of_lt_mul
    rw [← pow_add, ← hb]
    exact ht
  have hR : (FoNums.cellRC h (a + 5) (t, c, j)).1 = t % 2 ^ a * 32 + j := by
    show t % 2 ^ (a + 5 - 5) * 32 + j = _
    rw [e1]
  have hC : (FoNums.cellRC h (a + 5) (t, c, j)).2 = c * 2 ^ b + t / 2 ^ a := by
    show c * 2 ^ (h.kT + 5 - (a + 5)) + t / 2 ^ (a + 5 - 5) = _
    rw [e1, e2]
  rw [hR, hC]
  have r1 : t % 2 ^ a * 32 + j < 2 ^ (a + 5) := by
    rw [pow_add]
    norm_num
    omega
  have r2 : (t % 2 ^ a * 32 + j) / 32 = t % 2 ^ a := by omega
  have r3 : (t % 2 ^ a * 32 + j) % 32 = j := by omega
  have c1 : (c * 2 ^ b + t / 2 ^ a) % 2 ^ b = t / 2 ^ a := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hq]
  have c2 : (c * 2 ^ b + t / 2 ^ a) / 2 ^ b = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpb, Nat.div_eq_of_lt hq, Nat.zero_add]
  have hT : tOf h (a + 5) (t % 2 ^ a * 32 + j) (c * 2 ^ b + t / 2 ^ a) = t := by
    unfold tOf
    rw [e1, e2, r2, c1]
    exact Nat.div_add_mod' t (2 ^ a)
  have hCc : cOf h (a + 5) (c * 2 ^ b + t / 2 ^ a) = c := by
    unfold cOf
    rw [e2, c2]
  unfold plane
  rw [hT, hCc, r3]
  simp only [r1, true_and]

/-- If 5 ≤ lm ≤ kT + 5 and j < 32, then for all t and c, with S = (c 2^kT + t) 32 + j, the pair
FoNums.cellRC h lm (t, c, j) is (S % 2^lm, S / 2^lm): row first, then column. -/
theorem cellRC_flat (h : Forest.Shape) (lm : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5)
    (t c : ℕ) {j : ℕ} (hj : j < 32) :
    FoNums.cellRC h lm (t, c, j) =
      (((c * 2 ^ h.kT + t) * 32 + j) % 2 ^ lm, ((c * 2 ^ h.kT + t) * 32 + j) / 2 ^ lm) := by
  obtain ⟨a, rfl⟩ : ∃ a, lm = a + 5 := ⟨lm - 5, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, h.kT = a + b := ⟨h.kT - a, by omega⟩
  have e1 : a + 5 - 5 = a := by omega
  have e2 : h.kT + 5 - (a + 5) = b := by omega
  have hpa : 0 < 2 ^ a := by positivity
  have hm : t % 2 ^ a < 2 ^ a := Nat.mod_lt _ hpa
  have hL : FoNums.cellRC h (a + 5) (t, c, j) =
      (t % 2 ^ a * 32 + j, c * 2 ^ b + t / 2 ^ a) := by
    show (t % 2 ^ (a + 5 - 5) * 32 + j, c * 2 ^ (h.kT + 5 - (a + 5)) + t / 2 ^ (a + 5 - 5)) = _
    rw [e1, e2]
  have r1 : t % 2 ^ a * 32 + j < 2 ^ (a + 5) := by
    rw [pow_add]
    norm_num
    omega
  have hS : (c * 2 ^ h.kT + t) * 32 + j =
      (t % 2 ^ a * 32 + j) + (c * 2 ^ b + t / 2 ^ a) * 2 ^ (a + 5) := by
    have hd := Nat.div_add_mod' t (2 ^ a)
    rw [hb]
    generalize t / 2 ^ a = q at hd ⊢
    generalize t % 2 ^ a = m at hd ⊢
    rw [← hd]
    ring
  rw [hL, hS, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r1,
    Nat.add_mul_div_right _ _ (by positivity), Nat.div_eq_of_lt r1, Nat.zero_add]

/-- The inverse of the address. If 5 ≤ lm ≤ kT + 5, r < 2^lm and col < h.NC * 2^(kT + 5 - lm), then
tOf h lm r col is below 2^kT, cOf h lm col is below h.NC, and FoNums.cellRC h lm at
(tOf h lm r col, cOf h lm col, r % 32) is (r, col). -/
theorem cellRC_back (h : Forest.Shape) (lm : ℕ) (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) {r col : ℕ}
    (hr : r < 2 ^ lm) (hcol : col < h.NC * 2 ^ (h.kT + 5 - lm)) :
    tOf h lm r col < 2 ^ h.kT ∧ cOf h lm col < h.NC ∧
      FoNums.cellRC h lm (tOf h lm r col, cOf h lm col, r % 32) = (r, col) := by
  obtain ⟨a, rfl⟩ : ∃ a, lm = a + 5 := ⟨lm - 5, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, h.kT = a + b := ⟨h.kT - a, by omega⟩
  have e1 : a + 5 - 5 = a := by omega
  have e2 : h.kT + 5 - (a + 5) = b := by omega
  rw [e2] at hcol
  have hpa : 0 < 2 ^ a := by positivity
  have hpb : 0 < 2 ^ b := by positivity
  have hs : r / 32 < 2 ^ a := by
    rw [pow_add] at hr
    norm_num at hr
    omega
  have hm : col % 2 ^ b < 2 ^ b := Nat.mod_lt _ hpb
  have hT : tOf h (a + 5) r col = col % 2 ^ b * 2 ^ a + r / 32 := by
    unfold tOf
    rw [e1, e2]
  have hC : cOf h (a + 5) col = col / 2 ^ b := by
    unfold cOf
    rw [e2]
  have d1 : (col % 2 ^ b * 2 ^ a + r / 32) % 2 ^ a = r / 32 := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs]
  have d2 : (col % 2 ^ b * 2 ^ a + r / 32) / 2 ^ a = col % 2 ^ b := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpa, Nat.div_eq_of_lt hs, Nat.zero_add]
  rw [hT, hC]
  refine ⟨?_, Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact hcol), ?_⟩
  · calc col % 2 ^ b * 2 ^ a + r / 32 < col % 2 ^ b * 2 ^ a + 2 ^ a := by omega
      _ = (col % 2 ^ b + 1) * 2 ^ a := by ring
      _ ≤ 2 ^ b * 2 ^ a := Nat.mul_le_mul_right _ hm
      _ = 2 ^ h.kT := by rw [hb, pow_add, Nat.mul_comm]
  · show ((col % 2 ^ b * 2 ^ a + r / 32) % 2 ^ (a + 5 - 5) * 32 + r % 32,
      col / 2 ^ b * 2 ^ (h.kT + 5 - (a + 5)) +
        (col % 2 ^ b * 2 ^ a + r / 32) / 2 ^ (a + 5 - 5)) = (r, col)
    rw [e1, e2, d1, d2, Nat.div_add_mod' col (2 ^ b)]
    congr 1
    omega

/-- From row 2^lm on, and from column h.NC * 2^(kT + 5 - lm) on, plane is 0. The exponent is a
subtraction on natural numbers: it is 0 if lm is above kT + 5. -/
theorem plane_outside (h : Forest.Shape) (lm : ℕ) (H : Hits) {r col : ℕ}
    (ho : 2 ^ lm ≤ r ∨ h.NC * 2 ^ (h.kT + 5 - lm) ≤ col) : plane h lm H r col = 0 := by
  unfold plane
  rw [if_neg]
  rintro ⟨h1, h2⟩
  rcases ho with ho | ho
  · omega
  · have h3 : h.NC ≤ cOf h lm col := (Nat.le_div_iff_mul_le (by positivity)).2 ho
    unfold bit at h2
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h2
    omega

/-- If every place of call c that is not a padding place has its chosen row below 2^(k_c), then
every row t from 2^(k_c) on has the count 0. -/
theorem count_repeat (h : Forest.Shape) (H : Hits) {c t : ℕ}
    (hr : ∀ i < 2 ^ FoNums.nOf h c, H.pad c i = false → H.row c i < 2 ^ FoNums.kOf h c)
    (ht : 2 ^ FoNums.kOf h c ≤ t) : count h H c t = 0 := by
  unfold count
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro i hi ⟨h1, h2⟩
  have h3 := hr i (mem_range.1 hi) h1
  omega

/-- A count of call c is at most 2^(n_c), the number of places of the call's key vector. -/
theorem count_le (h : Forest.Shape) (H : Hits) (c t : ℕ) :
    count h H c t ≤ 2 ^ FoNums.nOf h c := by
  unfold count
  exact (card_filter_le _ _).trans (le_of_eq (card_range _))

/-- Under FoNums.ok h, for c below h.NC: n_c is at most h.v, and h.v is below 32. -/
theorem nOf_le_v {h : Forest.Shape} (hok : FoNums.ok h = true) {c : ℕ} (hc : c < h.NC) :
    FoNums.nOf h c ≤ h.v ∧ h.v < 32 := by
  simp only [FoNums.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, a4⟩, a5⟩, _⟩, _⟩, _⟩, cc⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hok
  have hn : FoNums.nOf h c = FoNums.io h c + h.dT := (cc c hc).1.2
  have hpos : 0 < 2 ^ FoNums.io h c := by positivity
  have hb := ((cc c hc).2 (2 ^ FoNums.io h c - 1) (by omega)).1.1
  have hle : 2 ^ FoNums.io h c ≤ 2 ^ h.rK := by omega
  have hio : FoNums.io h c ≤ h.rK := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 hle
  have hv : h.v = h.dT + h.rK := rfl
  exact ⟨by omega, a5⟩

/-- Under FoNums.ok h, for c below h.NC: the padding row of call c is below 2^(k_c). -/
theorem t0Of_lt {h : Forest.Shape} (hok : FoNums.ok h = true) {c : ℕ} (hc : c < h.NC) :
    FoNums.t0Of h c < 2 ^ FoNums.kOf h c := by
  simp only [FoNums.ok, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, cc⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hok
  exact (cc c hc).1.1.1

/-- Under FoNums.ok h, for c below h.NC, every count of call c is below 2^32. -/
theorem count_lt (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true) {c : ℕ}
    (hc : c < h.NC) (t : ℕ) : count h H c t < 2 ^ 32 := by
  obtain ⟨h1, h2⟩ := nOf_le_v hok hc
  exact lt_of_le_of_lt (count_le h H c t) (Nat.pow_lt_pow_right (by norm_num) (by omega))

/-- Under FoNums.ok h, for c below h.NC: the sum of 2^j over the j below 32 at which
bit h H t c j is true is count h H c t. -/
theorem sum_bits (h : Forest.Shape) (H : Hits) (hok : FoNums.ok h = true) {c : ℕ}
    (hc : c < h.NC) (t : ℕ) :
    ∑ j ∈ range 32, (if bit h H t c j = true then 2 ^ j else 0) = count h H c t := by
  have hlt := count_lt h H hok hc t
  have hcg : ∀ j ∈ range 32, (if bit h H t c j = true then 2 ^ j else 0) =
      if (count h H c t).testBit j = true then 2 ^ j else 0 := by
    intro j hj
    have hj' := mem_range.1 hj
    simp [bit, hc, hj']
  rw [sum_congr rfl hcg, Alg.Lookup.sum_testBit, Nat.mod_eq_of_lt hlt]

/-- If every place of call c that is not a padding place has its chosen row below 2^kT, then the
counts of the rows below 2^kT and the number of padding places of call c add up to 2^(n_c). -/
theorem sum_count_call (h : Forest.Shape) (H : Hits) (c : ℕ)
    (hr : ∀ i < 2 ^ FoNums.nOf h c, H.pad c i = false → H.row c i < 2 ^ h.kT) :
    ∑ t ∈ range (2 ^ h.kT), count h H c t +
      ((range (2 ^ FoNums.nOf h c)).filter fun i => H.pad c i = true).card =
        2 ^ FoNums.nOf h c := by
  have h1 : ∑ t ∈ range (2 ^ h.kT), count h H c t =
      ((range (2 ^ FoNums.nOf h c)).filter fun i => H.pad c i = false).card := by
    rw [card_eq_sum_card_fiberwise (f := fun i => H.row c i) (t := range (2 ^ h.kT))]
    · refine sum_congr rfl fun t _ => ?_
      unfold count
      rw [filter_filter]
    · intro i hi
      have hi' := mem_filter.1 (mem_coe.1 hi)
      exact mem_coe.2 (mem_range.2 (hr i (mem_range.1 hi'.1) hi'.2))
  have h2 := card_filter_add_card_filter_not (s := range (2 ^ FoNums.nOf h c))
    (fun i => H.pad c i = false)
  simp only [Bool.not_eq_false, card_range] at h2
  rw [h1]
  exact h2

/-- The sum of f over the numbers below A * M is the sum over u below A of the sums over v below M
of f (u * M + v). -/
theorem sum_range_blocks (A M : ℕ) (f : ℕ → ℕ) :
    ∑ x ∈ range (A * M), f x = ∑ u ∈ range A, ∑ v ∈ range M, f (u * M + v) := by
  induction A with
  | zero => simp
  | succ A ih => rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- Under FoNums.ok h, if 5 ≤ lm ≤ kT + 5: the cells of plane in the rows below 2^lm and the columns
below h.NC * 2^(kT + 5 - lm), each weighted by 2^(r % 32), add up to the sum of the counts of the
rows below 2^kT of the calls below h.NC. -/
theorem sum_plane (h : Forest.Shape) (lm : ℕ) (H : Hits) (hok : FoNums.ok h = true)
    (h5 : 5 ≤ lm) (hlm : lm ≤ h.kT + 5) :
    ∑ col ∈ range (h.NC * 2 ^ (h.kT + 5 - lm)), ∑ r ∈ range (2 ^ lm),
        2 ^ (r % 32) * plane h lm H r col =
      ∑ c ∈ range h.NC, ∑ t ∈ range (2 ^ h.kT), count h H c t := by
  obtain ⟨a, rfl⟩ : ∃ a, lm = a + 5 := ⟨lm - 5, by omega⟩
  obtain ⟨b, hb⟩ : ∃ b, h.kT = a + b := ⟨h.kT - a, by omega⟩
  have e1 : a + 5 - 5 = a := by omega
  have e2 : h.kT + 5 - (a + 5) = b := by omega
  have e3 : 2 ^ h.kT = 2 ^ b * 2 ^ a := by rw [hb, pow_add, Nat.mul_comm]
  have e4 : 2 ^ (a + 5) = 2 ^ a * 32 := by
    rw [pow_add]
    norm_num
  have hpa : 0 < 2 ^ a := by positivity
  rw [e2, sum_range_blocks]
  refine sum_congr rfl fun c hc => ?_
  rw [e3, sum_range_blocks]
  refine sum_congr rfl fun m hm => ?_
  rw [e4, sum_range_blocks]
  refine sum_congr rfl fun s hs => ?_
  rw [← sum_bits h H hok (mem_range.1 hc) (m * 2 ^ a + s)]
  refine sum_congr rfl fun j hj => ?_
  have hj' := mem_range.1 hj
  have hs' := mem_range.1 hs
  have hm' := mem_range.1 hm
  have r3 : (s * 32 + j) % 32 = j := by omega
  have d1 : (m * 2 ^ a + s) % 2 ^ a = s := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hs']
  have d2 : (m * 2 ^ a + s) / 2 ^ a = m := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hpa, Nat.div_eq_of_lt hs', Nat.zero_add]
  have ht : m * 2 ^ a + s < 2 ^ h.kT := by
    calc m * 2 ^ a + s < m * 2 ^ a + 2 ^ a := by omega
      _ = (m + 1) * 2 ^ a := by ring
      _ ≤ 2 ^ b * 2 ^ a := Nat.mul_le_mul_right _ hm'
      _ = 2 ^ h.kT := e3.symm
  have hcell : FoNums.cellRC h (a + 5) (m * 2 ^ a + s, c, j) = (s * 32 + j, c * 2 ^ b + m) := by
    show ((m * 2 ^ a + s) % 2 ^ (a + 5 - 5) * 32 + j,
      c * 2 ^ (h.kT + 5 - (a + 5)) + (m * 2 ^ a + s) / 2 ^ (a + 5 - 5)) = _
    rw [e1, e2, d1, d2]
  have hp := plane_cellRC h (a + 5) H h5 hlm (c := c) ht hj'
  rw [hcell] at hp
  rw [r3, hp]
  split_ifs <;> simp

/-- If two Hits agree on padding places and chosen rows at all places of call c, they give call c
the same counts. -/
theorem count_congr (h : Forest.Shape) {H H' : Hits} {c : ℕ}
    (hH : ∀ i < 2 ^ FoNums.nOf h c, H'.pad c i = H.pad c i ∧ H'.row c i = H.row c i) (t : ℕ) :
    count h H' c t = count h H c t := by
  unfold count
  refine congrArg card (filter_congr fun i hi => ?_)
  obtain ⟨a, b⟩ := hH i (mem_range.1 hi)
  rw [a, b]

/-- If two Hits agree on padding places and chosen rows at all places of every call below h.NC,
they give the same bits. -/
theorem bit_congr (h : Forest.Shape) {H H' : Hits}
    (hH : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c,
      H'.pad c i = H.pad c i ∧ H'.row c i = H.row c i) (t c j : ℕ) :
    bit h H' t c j = bit h H t c j := by
  unfold bit
  by_cases hc : c < h.NC
  · rw [count_congr h (hH c hc)]
  · simp [hc]

/-- If two Hits agree on padding places and chosen rows at all places of every call below h.NC,
they give the same planes' matrix. -/
theorem plane_congr (h : Forest.Shape) (lm : ℕ) {H H' : Hits}
    (hH : ∀ c < h.NC, ∀ i < 2 ^ FoNums.nOf h c,
      H'.pad c i = H.pad c i ∧ H'.row c i = H.row c i) (r col : ℕ) :
    plane h lm H' r col = plane h lm H r col := by
  unfold plane
  rw [bit_congr h hH]

/-! ## Laws on the first row -/

/-- If x is the value of a row below 2^k, then firstRow T k x is below 2^k, its row's value is x,
and no earlier row's value is x. -/
theorem firstRow_spec {K : Type} [DecidableEq K] (T : ℕ → K) (k : ℕ) (x : K)
    (hx : ∃ u < 2 ^ k, x = T u) :
    firstRow T k x < 2 ^ k ∧ x = T (firstRow T k x) ∧ ∀ u < firstRow T k x, T u ≠ x := by
  obtain ⟨u, hu, hxu⟩ := hx
  unfold firstRow
  cases hf : (List.range (2 ^ k)).find? fun v => decide (T v = x) with
  | none =>
    have h1 := List.find?_eq_none.1 hf u (List.mem_range.2 hu)
    simp [hxu] at h1
  | some w =>
    obtain ⟨h1, h2, h3⟩ := List.find?_range_eq_some.1 hf
    simp only [Option.getD_some]
    refine ⟨List.mem_range.1 h2, (of_decide_eq_true h1).symm, fun v hv => ?_⟩
    have h4 := h3 v hv
    simpa using h4

/-- If no two rows below 2^k of T have the same value, then firstRow T k (T u) = u for every u
below 2^k. -/
theorem firstRow_inj {K : Type} [DecidableEq K] (T : ℕ → K) (k : ℕ)
    (hT : ∀ u < 2 ^ k, ∀ u' < 2 ^ k, T u = T u' → u = u') {u : ℕ} (hu : u < 2 ^ k) :
    firstRow T k (T u) = u := by
  obtain ⟨h1, h2, _⟩ := firstRow_spec T k (T u) ⟨u, hu, rfl⟩
  exact (hT u hu _ h1 h2).symm

/-- An injective map of the values does not move firstRow. -/
theorem firstRow_map {K K' : Type} [DecidableEq K] [DecidableEq K'] (f : K → K')
    (hf : Function.Injective f) (T : ℕ → K) (k : ℕ) (x : K) :
    firstRow (fun u => f (T u)) k (f x) = firstRow T k x := by
  unfold firstRow
  have e : (fun u => decide (f (T u) = f x)) = fun u => decide (T u = x) := by
    funext u
    exact decide_eq_decide.2 hf.eq_iff
  rw [e]

/-- An injective map of the values of tables and key vectors does not move hitsOf, so it moves no
count, bit or cell of plane at hitsOf. -/
theorem hitsOf_map {K K' : Type} [DecidableEq K] [DecidableEq K'] (f : K → K')
    (hf : Function.Injective f) (h : Forest.Shape) (T Kv : ℕ → ℕ → K) (pad : ℕ → ℕ → Bool) :
    hitsOf h (fun c t => f (T c t)) (fun c i => f (Kv c i)) pad = hitsOf h T Kv pad := by
  unfold hitsOf
  congr 1
  funext c i
  exact congrArg (fun r => if pad c i = true then FoNums.t0Of h c else r)
    (firstRow_map f hf (T c) _ (Kv c i))

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.plane_01
#print axioms OnBytes.HonestTrace.plane_cellRC
#print axioms OnBytes.HonestTrace.cellRC_flat
#print axioms OnBytes.HonestTrace.cellRC_back
#print axioms OnBytes.HonestTrace.plane_outside
#print axioms OnBytes.HonestTrace.count_repeat
#print axioms OnBytes.HonestTrace.count_le
#print axioms OnBytes.HonestTrace.nOf_le_v
#print axioms OnBytes.HonestTrace.t0Of_lt
#print axioms OnBytes.HonestTrace.count_lt
#print axioms OnBytes.HonestTrace.sum_bits
#print axioms OnBytes.HonestTrace.sum_count_call
#print axioms OnBytes.HonestTrace.sum_range_blocks
#print axioms OnBytes.HonestTrace.sum_plane
#print axioms OnBytes.HonestTrace.count_congr
#print axioms OnBytes.HonestTrace.bit_congr
#print axioms OnBytes.HonestTrace.plane_congr
#print axioms OnBytes.HonestTrace.firstRow_spec
#print axioms OnBytes.HonestTrace.firstRow_inj
#print axioms OnBytes.HonestTrace.firstRow_map
#print axioms OnBytes.HonestTrace.hitsOf_map
