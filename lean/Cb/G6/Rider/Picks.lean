-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Cb/G6/Rider/Picks.lean: picks of coordinates and arrays on cubes for riders: plain arithmetic.

Definitions, statements and proofs. No protocol, no reduction and no relation occurs here.

  keyIx, callIx, selAtt, selAtt_ok, selAtt_line: a pick of coordinates that is no interval.
  blkOf, gOf, iOf, cut_of, cut_lt: the cut of a vertex's number into (block | head | position).
  rowSumA, onPieces, onPieces_zero: a row sum over tiles; a map on (block, head, position) as an
  array on the cube, cut by a public indicator.
  two_lines_none: if no vertex counts, a source and a target with an indicator hold of everything.

The picks are plain functions on ℕ and compile.

Terms: lean/GLOSSARY.md.
-/
import Blocks.Ext
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Cb.Rider
open Blocks Finset

variable {E : Type} [Field E] [Fintype E]

/-! ## 1. A pick of coordinates that is no interval -/

/-- A point has dT + rK coordinates: a first part of dT, then a second part of rK. The shorter point
is the last iota coordinates of the second part, then the first part. `keyIx` gives coordinate j of
the shorter point as an index into the whole point. -/
def keyIx (dT rK iota j : ℕ) : ℕ := if j < iota then dT + rK - iota + j else j - iota
/-- The rider's coordinate t as an index into the shorter point: the place nb is skipped. -/
def callIx (nb t : ℕ) : ℕ := if t < nb then t else t + 1
/-- The pick: the rider's coordinate t as an index into the whole point. -/
def selAtt (dT rK iota nb t : ℕ) : ℕ := keyIx dT rK iota (callIx nb t)

theorem selAtt_ok {dT rK iota nb lgk lt ldh : ℕ} (h1 : iota ≤ rK)
    (hb : nb + 1 + lgk + lt + ldh = dT + iota) :
    (∀ t < nb + lgk + lt, ∀ t' < nb + lgk + lt,
      selAtt dT rK iota nb t = selAtt dT rK iota nb t' → t = t') ∧
    ∀ t < nb + lgk + lt, selAtt dT rK iota nb t + 1 ≤ dT + rK := by
  constructor
  · intro t ht t' ht' e
    unfold selAtt keyIx callIx at e
    split_ifs at e <;> omega
  · intro t ht
    unfold selAtt keyIx callIx
    split_ifs <;> omega

/-- Coordinate 0 of the key point is named where iota < nb: it is then the rider's coordinate iota.
-/
theorem selAtt_line {dT rK iota nb : ℕ} (h : iota < nb) : selAtt dT rK iota nb iota = 0 := by
  unfold selAtt keyIx callIx
  rw [if_pos h, if_neg (Nat.lt_irrefl _), Nat.sub_self]

/-! ## 2. Arrays on (block | head | position) -/

/-- The cut of a vertex's number X = (block | g | i), top bits first: the block. -/
def blkOf (lgk lt X : ℕ) : ℕ := X / 2 ^ lt / 2 ^ lgk
/-- The head g of X. -/
def gOf (lgk lt X : ℕ) : ℕ := X / 2 ^ lt % 2 ^ lgk
/-- The position i of X. -/
def iOf (lt X : ℕ) : ℕ := X % 2 ^ lt

theorem cut_of {lgk lt P g i : ℕ} (hg : g < 2 ^ lgk) (hi : i < 2 ^ lt) :
    blkOf lgk lt ((P * 2 ^ lgk + g) * 2 ^ lt + i) = P ∧ gOf lgk lt
        ((P * 2 ^ lgk + g) * 2 ^ lt + i) = g ∧
      iOf lt ((P * 2 ^ lgk + g) * 2 ^ lt + i) = i := by
  have hT : 0 < 2 ^ lt := Nat.pos_of_ne_zero (by positivity)
  have hG : 0 < 2 ^ lgk := Nat.pos_of_ne_zero (by positivity)
  have e1 : ((P * 2 ^ lgk + g) * 2 ^ lt + i) / 2 ^ lt = P * 2 ^ lgk + g := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hT, Nat.div_eq_of_lt hi, Nat.zero_add]
  refine ⟨?_, ?_, ?_⟩
  · unfold blkOf
    rw [e1, Nat.add_comm, Nat.add_mul_div_right _ _ hG, Nat.div_eq_of_lt hg, Nat.zero_add]
  · unfold gOf
    rw [e1, Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hg]
  · unfold iOf
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hi]

theorem cut_lt {nb lgk lt NP P g i : ℕ} (hN : NP ≤ 2 ^ nb) (hP : P < NP) (hg : g < 2 ^ lgk)
    (hi : i < 2 ^ lt) : (P * 2 ^ lgk + g) * 2 ^ lt + i < 2 ^ (nb + lgk + lt) := by
  have h1 : P * 2 ^ lgk + g + 1 ≤ 2 ^ nb * 2 ^ lgk := by
    have : (P + 1) * 2 ^ lgk ≤ 2 ^ nb * 2 ^ lgk := Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at this
    omega
  have h2 : (P * 2 ^ lgk + g + 1) * 2 ^ lt ≤ 2 ^ nb * 2 ^ lgk * 2 ^ lt := Nat.mul_le_mul_right _ h1
  rw [Nat.add_mul, Nat.one_mul] at h2
  rw [pow_add, pow_add]
  omega

section Array
variable {St M : Type}

/-- A row sum over tiles at (block b, head g, position i). A tile's side has B places; nS rows of nT
tile slots each, the last slot of each row left out (sg < nT - 1), a slot counting if `rowOf P sg`
is the tile row i / B; and the diagonal tile whole: all j < B, each with weight 1. nS, nT, B and
rowOf are free. -/
def rowSumA (nS nT B : ℕ) (rowOf : ℕ → ℕ → ℕ) (wtM : St → M → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → E)
    (wtD : St → M → ℕ → ℕ → ℕ → ℕ → ℕ → E) (st : St) (m : M) (b g i : ℕ) : E :=
  (∑ P ∈ range nS, ∑ sg ∈ range (nT - 1),
      if rowOf P sg = i / B then ∑ j ∈ range B, wtM st m b g P sg (i % B) j else 0) +
    ∑ j ∈ range B, wtD st m b g (i / B) (i % B) j

/-- A map on (block, head, position) as an array on the cube, cut by the public indicator "block <
NP". -/
def onPieces (lgk lt NP : ℕ) (u : ℕ → ℕ → ℕ → E) (X : ℕ) : E :=
  if blkOf lgk lt X < NP then u (blkOf lgk lt X) (gOf lgk lt X) (iOf lt X) else 0

omit [Fintype E] in
theorem onPieces_zero {nb lgk lt NP : ℕ} (hN : NP ≤ 2 ^ nb) (u : ℕ → ℕ → ℕ → E) :
    (∀ X < 2 ^ (nb + lgk + lt), onPieces lgk lt NP u X = 0) ↔
      ∀ P < NP, ∀ g < 2 ^ lgk, ∀ i < 2 ^ lt, u P g i = 0 := by
  constructor
  · intro h P hP g hg i hi
    have h1 := h _ (cut_lt hN hP hg hi)
    obtain ⟨e1, e2, e3⟩ := cut_of (P := P) hg hi
    unfold onPieces at h1
    rw [e1, e2, e3, if_pos hP] at h1
    exact h1
  · intro h X _
    unfold onPieces
    split
    · next hb =>
      exact h _ hb _ (Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity))) _
        (Nat.mod_lt _ (Nat.pos_of_ne_zero (by positivity)))
    · rfl

end Array

/-! ## 3. No vertex counts -/

omit [Fintype E] in
/-- If no vertex counts, source and target of a rider of two conditions with an indicator hold of
every tuple. -/
theorem two_lines_none (lt : ℕ) (cost : ℕ → Bool) (hc : ∀ X, cost X = false) (l3 l4 pt : ℕ → E) :
    (∀ X < 2 ^ lt, cost X = true → l3 X = 0 ∧ l4 X = 0) ∧
      ext lt (fun X => if cost X = true then l3 X else 0) pt = 0 ∧
      ext lt (fun X => if cost X = true then l4 X else 0) pt = 0 := by
  refine ⟨fun X _ h => absurd h (by rw [hc X]; exact Bool.false_ne_true), ?_, ?_⟩
  · exact ext_zero_of_forall (fun X _ => by rw [hc X]; rfl) _
  · exact ext_zero_of_forall (fun X _ => by rw [hc X]; rfl) _

end Cb.Rider

#print axioms Cb.Rider.selAtt_ok
#print axioms Cb.Rider.onPieces_zero
#print axioms Cb.Rider.two_lines_none
