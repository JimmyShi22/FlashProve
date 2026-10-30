-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Blocks/RngCallsPlan.lean: one call of a lookup plan as a plan; ranges for the calls in one vector.

Blocks/RngForest.lean takes all calls of a plan as the trees of one forest. The implementation
treats the calls one after the other, and so does the range reduction by calls
(Blocks/RngCalls.lean): each call is a separate forest, of 2^B trees of keys. This file has no
protocol.
 * `Plan.one` P f: call f of the plan P, as a plan with this one call. All statements of
   Blocks/RngForest.lean apply to it with lf = 0 (no coordinate for the number of a call): its
   forest `(P.one f).lk E 0 (P.d f)` has 2^B trees of 2^(D - B) keys and a table of 2^(d f) entries,
   the table's own size.
 * `Plan.key_one`: the keys are those of call f.
 * `Plan.Valid.one`: the sizes of a valid plan fit each call.
 * `covPairs`, `isPad_of_covPairs`: in the plan with keys of two kinds the row positions of a call
   from `covPairs` on hold padding keys; their number is public.
 * `pre` w f: the sum of the widths w 0, .., w (f - 1): the first index of the range of call f in
   one vector of entries; `pre_mono`, `pre_succ`, `pre_apart`: the ranges follow each other and do
   not overlap.
 * `pick` w n v x: entry x of the vector of these ranges, computed as a sum over all n ranges, of
   which at most one term is not 0: without search and without choice; `pick_pre`.
Notation: a lookup plan (`Plan`) lists the calls of a range reduction: the keys of call f are affine
functions of the columns of the matrix W (the head of Blocks/RngPlan.lean); the fields of a plan
(`Plan`, Blocks/RngPlan.lean), natural numbers unless a type is given: `h`, `k`: the matrix W has h
rows and 2^k columns; `nc`: number of calls; `D`, `B`: the key hypercube has D coordinates, the last
B of which are the class; `lp`: a multiplicity has 2^lp bits; `d : ℕ → ℕ`, `off : ℕ → ℕ → F`,
`Γ : ℕ → ℕ → ℕ → F`: call f has the table {0, .., 2^(d f) - 1}, offsets off f and the matrix Γ f. A
key of call f has the number i = i_row 2^k + i_col (`Plan.key`).
`Plan.ofPairs F h k D B lp m2 y0 y1`: the plan with keys of two kinds, with the pairs of rows (y0 q,
y1 q), q < m2, as a parameter; `nCalls D k n`: number of calls for n rows of keys, R = 2^(D - k)
rows in a call (both: Blocks/RngPlan.lean). `lf`: the number of coordinates for the number of a call
(`Plan.lk`, Blocks/RngForest.lean).
Limits: nothing on messages. The order of the entries of the vector bit (the multiplicity bits of
all calls) in the implementation's file (columns of 1,024 rows) is not rendered: here the ranges of
the calls follow each other in one vector. (Where a multiplicity bit is in bit: `RngC.Par.plcB`,
Blocks/RngCalls.lean.)

Terms: lean/GLOSSARY.md.
"The implementation" in this file's comments is not the released programs: what is said of it need
not hold of them (lean/LIMITS.md, L1).
-/
import Blocks.RngForest

set_option autoImplicit false

namespace Blocks.Rng

open Finset

namespace Plan

variable {F : Type} [Field F] (P : Plan F)

/-- Call f of the plan, as a plan with one call. -/
def one (f : ℕ) : Plan F where
  h := P.h
  k := P.k
  nc := 1
  D := P.D
  B := P.B
  lp := P.lp
  d := fun _ => P.d f
  off := fun _ => P.off f
  Γ := fun _ => P.Γ f

theorem key_one (f g : ℕ) (W : ℕ → ℕ → F) (i : ℕ) : (P.one f).key g W i = P.key f W i := rfl

theorem keysAll_one (f : ℕ) (W : ℕ → ℕ → F) :
    (P.one f).KeysAll W ↔ ∀ i, i < 2 ^ P.D → InTab (P.d f) (P.key f W i) :=
  ⟨fun h i hi => h 0 Nat.one_pos i hi, fun h _ _ i hi => h i hi⟩

/-- Every key of every call is in its table if and only if this holds call by call. -/
theorem keysAll_iff_one (W : ℕ → ℕ → F) : P.KeysAll W ↔ ∀ f, f < P.nc → (P.one f).KeysAll W :=
  ⟨fun h f hf => (P.keysAll_one f W).2 (h f hf), fun h f hf => (P.keysAll_one f W).1 (h f hf)⟩

/-- The sizes of a valid plan fit each of its calls. -/
theorem Valid.one {P : Plan F} {p : ℕ} {WFp : (ℕ → ℕ → F) → Prop} (h : P.Valid p WFp)
    {f : ℕ} (hf : f < P.nc) :
    (P.one f).Valid p (P.one f).KeysOK where
  k_le := h.k_le
  B_le := h.B_le
  nc_pos := Nat.one_pos
  pl1 := fun _ => Iff.rfl
  pl2 := fun _ _ => h.pl2 f hf
  pl2' := h.pl2'

end Plan

/-! ## The padding of the plan with keys of two kinds -/

/-- The number of covered row positions of call f of the plan with keys of two kinds (`Plan.ofPairs`
with the same h, k, D, m2, Blocks/RngPlan.lean: the calls f < nCalls D k h are of the first kind,
the others of the second kind): all 2^(D - k), but in the last call of each kind. -/
def covPairs (h k D m2 f : ℕ) : ℕ :=
  if f < nCalls D k h then min (2 ^ (D - k)) (h - f * 2 ^ (D - k))
  else min (2 ^ (D - k)) (m2 - (f - nCalls D k h) * 2 ^ (D - k))

theorem covPairs_le (h k D m2 f : ℕ) : covPairs h k D m2 f ≤ 2 ^ (D - k) := by
  unfold covPairs
  split_ifs <;> exact min_le_left _ _

/-- The keys at the row positions from covPairs on are padding. -/
theorem isPad_of_covPairs (F : Type) [Field F] {h k D m2 : ℕ} (B lp : ℕ) (y0 y1 : ℕ → ℕ) {f i' : ℕ}
    (hc : covPairs h k D m2 f ≤ i') (hi : i' < 2 ^ (D - k)) :
    (Plan.ofPairs F h k D B lp m2 y0 y1).IsPad f i' := by
  unfold covPairs at hc
  by_cases hf : f < nCalls D k h
  · rw [if_pos hf] at hc
    refine isPad_first hf ?_
    rcases min_le_iff.1 hc with h1 | h1 <;> omega
  · rw [if_neg hf] at hc
    refine isPad_second hf ?_
    rcases min_le_iff.1 hc with h1 | h1 <;> omega

/-! ## Ranges in one vector -/

/-- the first index of range f, if range g has w g indices -/
def pre (w : ℕ → ℕ) (f : ℕ) : ℕ := ∑ g ∈ range f, w g

theorem pre_succ (w : ℕ → ℕ) (f : ℕ) : pre w (f + 1) = pre w f + w f := sum_range_succ _ _

theorem pre_mono (w : ℕ → ℕ) {f g : ℕ} (h : f ≤ g) : pre w f ≤ pre w g := by
  induction g with
  | zero => rw [Nat.le_zero.mp h]
  | succ g ih =>
    rcases Nat.lt_or_ge f (g + 1) with h1 | h1
    · exact (ih (by omega)).trans (by rw [pre_succ]; omega)
    · rw [show f = g + 1 by omega]

/-- An index of range f is in no other range. -/
theorem pre_apart (w : ℕ → ℕ) {f g x : ℕ} (hx : x < w f)
    (h : pre w g ≤ pre w f + x ∧ pre w f + x < pre w (g + 1)) : g = f := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h1 | h1
  · have := pre_mono w (show g + 1 ≤ f by omega)
    omega
  · have := pre_mono w (show f + 1 ≤ g by omega)
    rw [pre_succ] at this
    omega

/-- The vector of entries in which range f < n holds v f 0, v f 1, ... -/
def pick {K : Type} [AddCommMonoid K] (w : ℕ → ℕ) (n : ℕ) (v : ℕ → ℕ → K) (x : ℕ) : K :=
  ∑ f ∈ range n, if pre w f ≤ x ∧ x < pre w (f + 1) then v f (x - pre w f) else 0

theorem pick_pre {K : Type} [AddCommMonoid K] (w : ℕ → ℕ) {n : ℕ} (v : ℕ → ℕ → K) {f x : ℕ}
    (hf : f < n) (hx : x < w f) :
    pick w n v (pre w f + x) = v f x := by
  unfold pick
  rw [sum_eq_single f]
  · rw [if_pos ⟨Nat.le_add_right _ _, by rw [pre_succ]; omega⟩, Nat.add_sub_cancel_left]
  · intro g _ hg
    rw [if_neg fun h => hg (pre_apart w hx h)]
  · intro h
    exact absurd (mem_range.mpr hf) h

end Blocks.Rng
