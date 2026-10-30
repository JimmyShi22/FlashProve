-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Reads/PointCuts.lean: cuts of points, and the entries of the two vectors of the
positions with a cost. Tools for the tie of the weights at the output head's seat.

All of this file is a tool: it holds for all arrays, and names no description of the protocol.

Why. The list of tables at the output head's link is made of points that lie in the carried record
in `verify-on-bytes`'s form; the kind declares its weights at points of its own classes. Both are
cuts of the lookup's point and of its calls' key points. That the two agree is arithmetic on cuts.

What is here.
  `take_append`, `drop_append`: the two halves of a point that is glued of two.
  `last_size`, `last_tail`, `last_head_size`: the last n coordinates (`Point.last`,
    Johnson/Desc/Kinds/HeadParts.lean): their number; the last b of the last a + b; the number of
    the first a of them.
  `key_tail`: a key point zk of J + lt coordinates that ends as the lookup's point zx does, in its
    last ls + lt coordinates: its coordinates from J on are the last lt of zx, and the last ls of
    its first J are the first ls of the last ls + lt of zx.
  `cost_first`, `cost_count`: entry t of the two vectors that `Head.costWeights`
    (OnBytes/Model/HeadTables.lean) returns.

Of OnBytes/Model/ this file names `Head.costWeights`, `Head.Covered` and `eqTab`.

Limits. Nothing on what a point is, or when it is drawn. Nothing on soundness.


-/
import Johnson.Desc.Kinds.HeadParts
import OnBytes.Model.HeadTables
import Mathlib.Tactic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Reads

open OnBytes (E zeroE oneE)
open OnBytes.Model (eqTab)
open OnBytes.Model.Head (Covered costWeights)
open VerifiableInference.Desc.Kinds (Point)

variable {α : Type}

/-- The first half of a glued array. -/
theorem take_append (a b : Array α) {n : ℕ} (h : a.size = n) : (a ++ b).extract 0 n = a := by
  subst h
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

/-- The second half of a glued array. -/
theorem drop_append (a b : Array α) {n m : ℕ} (h : a.size = n) (hb : b.size = m) :
    (a ++ b).extract n (n + m) = b := by
  subst h hb
  apply Array.ext
  · simp
  · intro i h1 h2
    simp

/-- The number of the last n coordinates. -/
theorem last_size (z : Point) {n : ℕ} (h : n ≤ z.size) : (z.last n).size = n := by
  unfold Point.last
  simp only [Array.size_extract]
  omega

/-- The last b of the last a + b coordinates. -/
theorem last_tail (z : Point) {a b : ℕ} (h : a + b ≤ z.size) :
    (z.last (a + b)).extract a (a + b) = z.last b := by
  unfold Point.last
  rw [Array.extract_extract]
  congr 1 <;> omega

/-- The number of the first a of the last a + b coordinates. -/
theorem last_head_size (z : Point) {a b : ℕ} (h : a + b ≤ z.size) :
    ((z.last (a + b)).extract 0 a).size = a := by
  unfold Point.last
  simp only [Array.size_extract]
  omega

/-- **A key point that ends as the lookup's point does.** -/
theorem key_tail (zk zx : Point) {J ls lt : ℕ} (hs : zk.size = J + lt)
    (hl : zk.last (ls + lt) = zx.last (ls + lt)) (hJ : ls ≤ J) (hz : ls + lt ≤ zx.size) :
    zk.extract J (J + lt) = zx.last lt ∧
      (zk.extract 0 J).extract (J - ls) J = (zx.last (ls + lt)).extract 0 ls := by
  have hk : ls + lt ≤ zk.size := by omega
  constructor
  · rw [← last_tail zx hz, ← hl, last_tail zk hk]
    unfold Point.last
    congr 1 <;> omega
  · rw [← hl]
    unfold Point.last
    rw [Array.extract_extract, Array.extract_extract]
    congr 1 <;> omega

/-- Entry t of the weights of a point at the positions with a cost. -/
theorem cost_first (cov : Covered) (z : Array E) (t : ℕ) :
    (costWeights cov z).1.getD t zeroE =
      if cov.hOnC.getD t false = true then (eqTab z).getD t zeroE else zeroE := by
  unfold costWeights
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx]
  cases (eqTab z)[t]? <;> simp

/-- Entry t of the indicator of the positions with a cost. -/
theorem cost_count (cov : Covered) (z : Array E) {t : ℕ} (ht : t < (eqTab z).size) :
    (costWeights cov z).2.2.getD t zeroE =
      if cov.hOnC.getD t false = true then oneE else zeroE := by
  unfold costWeights
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_mapIdx, Array.getElem?_eq_getElem ht]
  simp

end VerifiableInference.Reads

#print axioms VerifiableInference.Reads.take_append
#print axioms VerifiableInference.Reads.drop_append
#print axioms VerifiableInference.Reads.last_size
#print axioms VerifiableInference.Reads.last_tail
#print axioms VerifiableInference.Reads.last_head_size
#print axioms VerifiableInference.Reads.key_tail
#print axioms VerifiableInference.Reads.cost_first
#print axioms VerifiableInference.Reads.cost_count
