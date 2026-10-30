-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/HonestTrace/CountsAttentionMap.lean

The key vectors of an attention sub-proof's lookup commute with a map of rings, so the matrix bA of
the bits of the counts (Johnson/HonestTrace/CountsAttention.lean) is the same over two fields with a
map between them.

Why. bA compares keys with table rows in the field K of its reading. One reader may take the cells
in a base field and another in an extension of it. "bA_map" says that both get one matrix, where the
second reading is φ of the first, as it is for cells that are integers cast into the two fields.

Main theorems:
* "kvA_map": for every map φ of commutative rings, every shape S, every fs, call number and place:
  A.kvA at the reading "φ of cell" is φ of A.kvA at cell.
* "bA_map": for every map φ of fields with decidable equality: bA at the reading "φ of cell" is bA
  at cell, at all rows and columns.
The names under "Att" say the same of the terms of OnBytes/Tie/Pv/Lookup/Ends/A.lean of which a key
is made: sums, limbs, the cells of "as", row maxima, denominators, index bits, tensors, the high
parts of the two remainders, scores, the score's part of a gap, softmax weights, accumulators, gaps
and the keys of a piece.

Limits. S and fs are any two values: nothing is asked of them. A map of fields is injective; for
rings that are no fields this file has kvA_map alone.

Not claimed: anything on a claim, a round or a message; that a prover's cells lie in any given
field.

-/
import Johnson.HonestTrace.CountsAttention

set_option autoImplicit false

namespace OnBytes.HonestTrace

open OnBytes.Model
open OnBytes.Ends (NameA)
open OnBytes.Ends.A

namespace Att

variable {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R')

/-- A map of rings commutes with A.sumN. -/
theorem sumN_map (n : ℕ) (f : ℕ → R) : φ (sumN n f) = sumN n fun i => φ (f i) := by
  unfold sumN
  have key : ∀ (l : List ℕ) (s : R),
      φ (l.foldl (fun s i => s + f i) s) = l.foldl (fun s i => s + φ (f i)) (φ s) := by
    intro l
    induction l with
    | nil =>
      intro s
      rfl
    | cons a l ih =>
      intro s
      rw [List.foldl_cons, List.foldl_cons, ih, map_add]
  rw [key, map_zero]

/-- A map of rings commutes with A.limbs. -/
theorem limbs_map (nl : ℕ) (f : ℕ → R) : φ (limbs nl f) = limbs nl fun l => φ (f l) := by
  unfold limbs
  rw [sumN_map]
  simp only [map_mul, map_natCast]

variable (S : Attention.Shape) (cell : NameA → R)

/-- The row maximum at the reading "φ of cell" is φ of the row maximum at cell. -/
theorem mx_map (lam hd i : ℕ) : mx S (fun n => φ (cell n)) lam hd i = φ (mx S cell lam hd i) := by
  unfold mx
  rw [limbs_map]
  rfl

/-- The denominator at the reading "φ of cell" is φ of the denominator at cell. -/
theorem den_map (lam hd i : ℕ) :
    den S (fun n => φ (cell n)) lam hd i = φ (den S cell lam hd i) := by
  unfold den
  rw [limbs_map]
  rfl

/-- A tensor of qa at the reading "φ of cell" is φ of the tensor at cell. -/
theorem ten_map (X : TenAt) (lam f i : ℕ) :
    ten S (fun n => φ (cell n)) X lam f i = φ (ten S cell X lam f i) := by
  unfold ten
  rw [limbs_map]
  rfl

/-- The score at the reading "φ of cell" is φ of the score at cell. -/
theorem score_map (lam hd g ti tj : ℕ) :
    score S (fun n => φ (cell n)) lam hd g ti tj = φ (score S cell lam hd g ti tj) := by
  unfold score
  rw [sumN_map]
  simp only [map_mul, ten_map]

/-- The softmax weight at the reading "φ of cell" is φ of the softmax weight at cell. -/
theorem wt_map (lam a : ℕ) (isD : Bool) (π : ℕ) :
    wt S (fun n => φ (cell n)) lam a isD π = φ (wt S cell lam a isD π) := by
  unfold wt
  simp only [map_add, map_mul, map_ofNat]
  rfl

/-- The accumulator at the reading "φ of cell" is φ of the accumulator at cell. -/
theorem acc_map (lam a g i n : ℕ) :
    acc S (fun n => φ (cell n)) lam a g i n = φ (acc S cell lam a g i n) := by
  unfold acc
  simp only [map_add, sumN_map, apply_ite φ, map_zero, map_mul, wt_map, ten_map]

/-- A.ssAt at the reading "φ of cell" is φ of A.ssAt at cell. -/
theorem ssAt_map (isD : Bool) (lam a κ : ℕ) :
    ssAt S (fun n => φ (cell n)) isD lam a κ = φ (ssAt S cell isD lam a κ) := by
  unfold ssAt
  simp only [apply_ite φ, map_zero, score_map]

/-- A.gapAt at the reading "φ of cell" is φ of A.gapAt at cell. -/
theorem gapAt_map (sh : ℕ) (isD : Bool) (lam a κ : ℕ) :
    gapAt S (fun n => φ (cell n)) sh isD lam a κ = φ (gapAt S cell sh isD lam a κ) := by
  unfold gapAt
  simp only [apply_ite φ, map_add, map_zero, map_natCast, mx_map]

/-- A.asC at the reading "φ of cell" is φ of A.asC at cell. -/
theorem asC_map (x lam a : ℕ) (isD : Bool) (π : ℕ) :
    asC S (fun n => φ (cell n)) x lam a isD π = φ (asC S cell x lam a isD π) := rfl

/-- An index bit at the reading "φ of cell" is φ of the index bit at cell. -/
theorem ib_map (lam k hd i : ℕ) :
    ib S (fun n => φ (cell n)) lam k hd i = φ (ib S cell lam k hd i) := rfl

/-- The high part of the first remainder at the reading "φ of cell" is φ of that part at cell. -/
theorem rh_map (lam f i : ℕ) : rh S (fun n => φ (cell n)) lam f i = φ (rh S cell lam f i) := rfl

/-- The high part of the second remainder at the reading "φ of cell" is φ of that part at cell. -/
theorem rhp_map (lam f i : ℕ) : rhp S (fun n => φ (cell n)) lam f i = φ (rhp S cell lam f i) := rfl

/-- A key of a piece at the reading "φ of cell" is φ of the key at cell. -/
theorem segKey_map (sh : ℕ) (s : Attention.Seg) (lam a κ : ℕ) :
    segKey S (fun n => φ (cell n)) sh s lam a κ = φ (segKey S cell sh s lam a κ) := by
  cases s <;>
    simp only [segKey, apply_ite φ, map_add, map_sub, map_mul, map_natCast, map_ofNat, map_one,
      sumN_map, asC_map, wt_map, gapAt_map, ssAt_map, den_map, acc_map, ten_map, rh_map, rhp_map,
      ib_map]

end Att

/-- **The key vectors commute with a map of rings.** For every map φ of commutative rings, every S,
fs, reading cell, call number q and place X: A.kvA at the reading "φ of cell" is φ of A.kvA at cell.
-/
theorem kvA_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (S : Attention.Shape)
    (fs : Forest.Shape) (cell : NameA → R) (q X : ℕ) :
    kvA S fs (fun n => φ (cell n)) q X = φ (kvA S fs cell q X) := by
  unfold kvA kvSel
  cases S.calls[q]? with
  | none => exact (map_zero φ).symm
  | some c =>
    show (match c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
      | some p => if true = true then
          segKey S (fun n => φ (cell n)) c.sh p.seg p.lam p.a (X - p.off) else 0
      | none => if true = true then ((Ends.tauN fs q (Ends.t0N fs q) : ℕ) : R') else 0) =
      φ (match c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
      | some p => if true = true then segKey S cell c.sh p.seg p.lam p.a (X - p.off) else 0
      | none => if true = true then ((Ends.tauN fs q (Ends.t0N fs q) : ℕ) : R) else 0)
    cases c.pcs.toList.find? fun p => decide (p.off ≤ X ∧ X < p.off + 2 ^ p.b) with
    | none => exact (map_natCast φ _).symm
    | some p => exact Att.segKey_map φ S cell c.sh p.seg p.lam p.a (X - p.off)

/-- **One matrix bA over two fields.** For every map φ of fields with decidable equality, every S,
fs and reading cell: bA at the reading "φ of cell" is bA at cell, at all rows and columns. -/
theorem bA_map {K K' : Type} [Field K] [DecidableEq K] [Field K'] [DecidableEq K'] (φ : K →+* K')
    (S : Attention.Shape) (fs : Forest.Shape) (cell : NameA → K) :
    bA S fs (fun n => φ (cell n)) = bA S fs cell := by
  funext r c
  unfold bA hitsA
  have e1 : tabOf K' fs = fun c t => φ (tabOf K fs c t) := by
    funext c t
    exact (map_natCast φ _).symm
  have e2 : kvA S fs (fun n => φ (cell n)) = fun c i => φ (kvA S fs cell c i) := by
    funext c i
    exact kvA_map φ S fs cell c i
  rw [e1, e2, hitsOf_map φ φ.injective]

end OnBytes.HonestTrace

#print axioms OnBytes.HonestTrace.Att.sumN_map
#print axioms OnBytes.HonestTrace.Att.limbs_map
#print axioms OnBytes.HonestTrace.Att.mx_map
#print axioms OnBytes.HonestTrace.Att.den_map
#print axioms OnBytes.HonestTrace.Att.ten_map
#print axioms OnBytes.HonestTrace.Att.score_map
#print axioms OnBytes.HonestTrace.Att.wt_map
#print axioms OnBytes.HonestTrace.Att.acc_map
#print axioms OnBytes.HonestTrace.Att.ssAt_map
#print axioms OnBytes.HonestTrace.Att.gapAt_map
#print axioms OnBytes.HonestTrace.Att.asC_map
#print axioms OnBytes.HonestTrace.Att.ib_map
#print axioms OnBytes.HonestTrace.Att.rh_map
#print axioms OnBytes.HonestTrace.Att.rhp_map
#print axioms OnBytes.HonestTrace.Att.segKey_map
#print axioms OnBytes.HonestTrace.kvA_map
#print axioms OnBytes.HonestTrace.bA_map
