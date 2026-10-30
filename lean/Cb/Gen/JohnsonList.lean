-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Gen/JohnsonList.lean: the Johnson bound on the size of a list.

Definitions and statements (the latter in `Cb.Spec`); the proofs are in
Cb/Gen/JohnsonListProofs.lean.
Once the radius is past half the distance, several codewords may lie within it of a single word.
The Johnson bound says how many at most, as long as the radius e stays below the Johnson radius.
Here n is the number of positions, d a lower bound on the distance of any two different codewords, e
the radius; all three count positions, and for interleaved words (tables) a position is a column.

Main names:
 1. A condition and a number.
    `InJohnson n d e`: the radius is below the Johnson radius, written without a
    square root as n (n - d) < (n - e)^2. (Cb/Gen/JohnsonListSqrt.lean shows that this is
    e < n - sqrt (n (n - d)).) `listMax n d e` = n (d - e) / ((n - e)^2 - n (n - d)), rounded down:
    the bound on the list.
 2. The bound, from the most abstract form to the one that a protocol uses; from
    `Spec.johnson_family` on under `InJohnson n d e`:
    `Spec.johnson_sets`, for sets of positions: if each of the sets T_i has at least t elements and
      any two of them share at most s, then (number of sets) (t^2 - n s) <= n (t - s);
    `Spec.johnson_agree`: the same for a family of words over any alphabet and a centre w; T_i is
      the set of positions where the i-th word agrees with w, and two different members agree
      with each other at s positions or fewer;
    `Spec.johnson_family`, in distances: a family of words with pairwise distance at least d has at
      most `listMax n d e` members within e of any word;
    `Spec.johnson_code`: the same for a set of words (no linearity, the alphabet may be infinite);
    `Spec.johnson_tables`, `Spec.johnson_tables_cnt`, for a generator matrix with distance d and
      tables of any number of rows (in the second: finitely many, over a finite field);
    `Spec.johnson_enc`: the second of these for a code with encoder (`Code.Enc`, Code/Iface.lean).

Why this form of the bound: the count of the classical proof gives n (d - e) in the numerator,
which is smaller than the n d that is often printed; `Spec.listMax_le_mul` gives the coarser form.

Limits: the subtractions are those of natural numbers (0 if the result would be negative).
`Spec.johnson_sets` and `Spec.johnson_agree` have no hypothesis that ties t to s, and say nothing if
t^2 <= n s (their left side is then 0). The other statements ask for `InJohnson`,
which fails if e >= n and if d = 0, so none of them speaks of a radius at or beyond the Johnson
radius. But `Spec.inJohnson_of_unique` and `Spec.listMax_le_of_gap` conclude `InJohnson` and do not
ask for it, and `Spec.listMax_le_mul` has no hypothesis. The bound is not tight: for 2 e < d the
list has at most one element (`Blocks.DecodesTo.unique`), while `listMax` may be larger. The
alphabet's size does not enter (the bound for a small alphabet is better; it is not here).
This file says nothing on proximity gaps or correlated agreement beyond half the distance, nothing
on how a list is computed, nothing on protocols or numerals.
`Code.Enc.Props` is not assumed in `Spec.johnson_enc`: it has 2 e < d for the code's own radius as
a field; only the distance of the generator is used.
The mathematics is classical (S. M. Johnson's bound; the count is also known as Corradi's lemma):
count the pairs (position, two members of the list that both agree with the centre there) and use
the Cauchy-Schwarz inequality over the positions.
That lists and this radius are wanted follows advice (lean/CREDITS.md).
Terms: lean/GLOSSARY.md.
-/
import Mathlib.Data.Set.Card
import Blocks.Decode

set_option autoImplicit false

namespace Cb
open Prob Blocks

/-- Below the Johnson radius: n positions, distance d, radius e. Without a square root. -/
def InJohnson (n d e : ℕ) : Prop := n * (n - d) < (n - e) ^ 2

/-- The bound on the list, rounded down. It has a meaning only under `InJohnson n d e` (else the
divisor is 0, and the value 0 by Lean's convention). -/
def listMax (n d e : ℕ) : ℕ := n * (d - e) / ((n - e) ^ 2 - n * (n - d))

namespace Spec

/-- The count, for sets of positions. Sets with at least t elements each, any two of which share at
most s. -/
def johnson_sets : Prop :=
  ∀ (I ι : Type) [Fintype ι] [DecidableEq ι] (L : Finset I) (T : I → Finset ι) (t s : ℕ),
    (∀ i ∈ L, t ≤ (T i).card) → (∀ i ∈ L, ∀ i' ∈ L, i ≠ i' → (T i ∩ T i').card ≤ s) →
    L.card * (t ^ 2 - Fintype.card ι * s) ≤ Fintype.card ι * (t - s)

/-- The count, for words: each member of the list agrees with the centre w at t positions or more,
two different members agree with each other at s positions or fewer. -/
def johnson_agree : Prop :=
  ∀ (I ι A : Type) [Fintype ι] (c : I → ι → A) (w : ι → A) (L : Finset I) (t s : ℕ),
    (∀ i ∈ L, t ≤ cnt fun j => c i j = w j) →
    (∀ i ∈ L, ∀ i' ∈ L, i ≠ i' → cnt (fun j => c i j = c i' j) ≤ s) →
    L.card * (t ^ 2 - Fintype.card ι * s) ≤ Fintype.card ι * (t - s)

/-- The Johnson bound for a family of words named by i : I, over any alphabet: different names have
words at distance d or more. (not all hypotheses are named here: see the statement below) -/
def johnson_family : Prop :=
  ∀ (I ι A : Type) [Fintype ι] (c : I → ι → A) (d e : ℕ),
    (∀ i i', i ≠ i' → d ≤ cnt fun j => c i j ≠ c i' j) → InJohnson (Fintype.card ι) d e →
    ∀ (w : ι → A) (L : Finset I),
      (∀ i ∈ L, cnt (fun j => c i j ≠ w j) ≤ e) → L.card ≤ listMax (Fintype.card ι) d e

/-- The Johnson bound for a set of words. "encard" is the number of elements, infinite for an
infinite set: the statement includes that the list is finite. -/
def johnson_code : Prop :=
  ∀ (ι A : Type) [Fintype ι] (Cd : Set (ι → A)) (d e : ℕ),
    (∀ c ∈ Cd, ∀ c' ∈ Cd, c ≠ c' → d ≤ cnt fun j => c j ≠ c' j) → InJohnson (Fintype.card ι) d e →
    ∀ w : ι → A, {c : ι → A | c ∈ Cd ∧ cnt (fun j => c j ≠ w j) ≤ e}.encard ≤
      ((listMax (Fintype.card ι) d e : ℕ) : ℕ∞)

/-- The Johnson bound for tables: the tables of messages to which a table decodes at the radius e.
Distance counts columns; the number of rows does not enter; the field may be infinite. -/
def johnson_tables : Prop :=
  ∀ (E ι κ : Type) [Field E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d e : ℕ), HasDist G d →
    InJohnson (Fintype.card ι) d e →
    ∀ (R : Type) (f : R → ι → E) (L : Finset (R → κ → E)),
      (∀ M ∈ L, DecodesTo G e f M) → L.card ≤ listMax (Fintype.card ι) d e

/-- The same as a count, for a finite field and finitely many rows: the form for a union bound over
the list. -/
def johnson_tables_cnt : Prop :=
  ∀ (E ι κ : Type) [Field E] [Finite E] [Fintype ι] [Fintype κ] (G : Matrix ι κ E) (d e : ℕ),
    HasDist G d → InJohnson (Fintype.card ι) d e →
    ∀ (R : Type) [Finite R] (f : R → ι → E),
      cnt (fun M : R → κ → E => DecodesTo G e f M) ≤ listMax (Fintype.card ι) d e

/-- The Johnson bound for a code with encoder, tables over the larger field, full messages (any
vectors of length k). The radius e is the caller's, not the field "e" of the code. -/
def johnson_enc : Prop :=
  ∀ (F E : Type) [Field F] [Field E] [Finite E] [Algebra F E] (C : Code.Enc F) (e : ℕ),
    HasDist C.G C.d → InJohnson C.n C.d e →
    ∀ (R : Type) [Finite R] (f : R → Fin C.n → E),
      cnt (fun M : R → Fin C.k → E => DecodesTo (C.GE E) e f M) ≤ listMax C.n C.d e

/-- A smaller radius is below the Johnson radius too. -/
def inJohnson_anti : Prop := ∀ n d e e' : ℕ, e' ≤ e → InJohnson n d e → InJohnson n d e'

/-- For d ≤ n, every radius of unique decoding (2 e < d) is below the Johnson radius. -/
def inJohnson_of_unique : Prop := ∀ n d e : ℕ, d ≤ n → 2 * e < d → InJohnson n d e

/-- With a slack g: if g > 0 and n (n - d) + g <= (n - e)^2, then `InJohnson n d e` holds and
`listMax n d e` <= n (d - e) / g. -/
def listMax_le_of_gap : Prop :=
  ∀ n d e g : ℕ,
    0 < g → n * (n - d) + g ≤ (n - e) ^ 2 → InJohnson n d e ∧ listMax n d e ≤ n * (d - e) / g

/-- The coarser form that is often printed, and one that needs no division. -/
def listMax_le_mul : Prop :=
  ∀ n d e : ℕ, listMax n d e ≤ n * d / ((n - e) ^ 2 - n * (n - d)) ∧ listMax n d e ≤ n * d

end Spec
end Cb
