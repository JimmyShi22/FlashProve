-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Pv/KeyLookup/LevStd.lean: where the own mask entries of the key levels and of the table's levels
stand, as a function of the public record and of two numberings of mask entries.

Definitions, statements and proofs. The record LevPl (Cb/Pv/KeyLookup/LevFit.lean) names the places
of the levels of the parts' product trees and of the table's tree as letters. Here it gets a value.
A level with k variables takes 2 k + 5 entries in a row: for each round of a variable, in the order
of the rounds, the coefficients of the first and second power; then, for the round of the further
variable, the constant first and the coefficients of the first and second power; then one entry for
each of the two shown values. At the last level of a part's tree the two shown values' entries are
not among these: they are the entries 2 i and 2 i + 1 of a second numbering.

Main names:
  Lev.offW k n: the number of the name n within the 2 k + 3 coefficients of a level with k
    variables.
  Lev.offW_nmV, offW_nmY, offW_nmC: at the names nmV k j t (round j < k: 2 j + t), nmV k k t (the
    further variable: 2 k + 1 + t) and nmC k (the constant: 2 k) of Cb/Pv/KeyLookup/LevRunA.lean.
  Lev.offW_lt: offW k n < 2 k + 3.
  Lev.grp more l: the entries that the levels 0, .., l - 1 take, level t having more + t variables.
  Lev.partSum S i: the entries of the first numbering that the trees of the parts before i take.
  LevPl.std A ms ix bK bI bT: the value: ms, ix number the mask entries; bK, bT are the numbers of
    the first entry of the key levels and of the table's levels in ms, bI that of the first entry
    in ix.
  Lev.grp_succ, partSum_succ: a level more; a part more.

Limits: no premise. Nothing is said on bK, bI, bT, nor on whether ms and ix are one-to-one, nor that
these are the places at which a program takes its entries.

-/
import Cb.Pv.KeyLookup.LevFit
import Cb.Pv.KeyLookup.LevRunA

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6
open Cb Cb.LdLkp

namespace Lev
section
variable {E : Type} [Field E] [Fintype E]

/-- The number of a name within a level's coefficients. -/
def offW : (k : ℕ) → PIdx (List.replicate k (pfCube E 2) ++ [pDummy E 2]) → ℕ
  | 0, i =>
    match (i : Fin 2 ⊕ Unit) with
    | .inr _ => 0
    | .inl t => 1 + t.val
  | k + 1, i =>
    match (i : Fin 2 ⊕ PIdx (List.replicate k (pfCube E 2) ++ [pDummy E 2])) with
    | .inl t => t.val
    | .inr n => 2 + offW k n

theorem offW_nmC : ∀ k, offW (E := E) k (nmC E k) = 2 * k
  | 0 => rfl
  | k + 1 => by
    show 2 + offW (E := E) k (nmC E k) = _
    rw [offW_nmC k]
    omega

theorem offW_nmY (t : Fin 2) : ∀ k j, k ≤ j → offW (E := E) k (nmV E k j t) = 2 * k + 1 + t.val
  | 0, _, _ => by
    show 1 + t.val = _
    omega
  | k + 1, j + 1, h => by
    show 2 + offW (E := E) k (nmV E k j t) = _
    rw [offW_nmY t k j (Nat.le_of_succ_le_succ h)]
    omega

theorem offW_nmV (t : Fin 2) : ∀ k j, j < k → offW (E := E) k (nmV E k j t) = 2 * j + t.val
  | k + 1, 0, _ => by
    show t.val = _
    omega
  | k + 1, j + 1, h => by
    show 2 + offW (E := E) k (nmV E k j t) = _
    rw [offW_nmV t k j (Nat.lt_of_succ_lt_succ h)]
    omega

theorem offW_lt : ∀ (k : ℕ) (n : PIdx (List.replicate k (pfCube E 2) ++ [pDummy E 2])),
    offW k n < 2 * k + 3
  | 0, n => by
    rcases (n : Fin 2 ⊕ Unit) with t | _
    · have ht : t.val < 2 := t.isLt
      show 1 + t.val < 3
      omega
    · show 0 < 3
      omega
  | k + 1, n => by
    rcases (n : Fin 2 ⊕ PIdx (List.replicate k (pfCube E 2) ++ [pDummy E 2])) with t | n'
    · have ht : t.val < 2 := t.isLt
      show t.val < _
      omega
    · show 2 + offW k n' < _
      have := offW_lt k n'
      omega

end

/-- The entries that the levels 0, .., l - 1 take. -/
def grp (more l : ℕ) : ℕ := ((List.range l).map fun t => 2 * (more + t) + 5).sum

/-- The entries of the first numbering that the trees of the parts before i take. -/
def partSum (S : Pub) (i : ℕ) : ℕ := ((List.range i).map fun a => grp 0 (S.v a) - 2).sum

theorem grp_succ (more l : ℕ) : grp more (l + 1) = grp more l + (2 * (more + l) + 5) := by
  unfold grp
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem partSum_succ (S : Pub) (i : ℕ) : partSum S (i + 1) = partSum S i + (grp 0 (S.v i) - 2) := by
  unfold partSum
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

end Lev

/-- The places of the key levels and of the table's levels. -/
def LevPl.std {E : Type} [Field E] [Fintype E] (A : Dat E) (ms ix : ℕ → A.J) (bK bI bT : ℕ) :
    LevPl A where
  wK := fun i l n => ms (bK + Lev.partSum A.toPub i + Lev.grp 0 l + Lev.offW (0 + l) n)
  cK := fun i l b =>
    if l + 1 = A.v i then ix (bI + 2 * i + (if b then 1 else 0))
    else ms (bK + Lev.partSum A.toPub i + Lev.grp 0 l + (2 * l + 3) + (if b then 1 else 0))
  wT := fun l n => ms (bT + Lev.grp A.mu l + Lev.offW (A.mu + l) n)
  cT := fun l b => ms (bT + Lev.grp A.mu l + (2 * (A.mu + l) + 3) + (if b then 1 else 0))

end Lk6

#print axioms Lk6.Lev.offW_nmC
#print axioms Lk6.Lev.offW_nmY
#print axioms Lk6.Lev.offW_nmV
#print axioms Lk6.Lev.offW_lt
#print axioms Lk6.Lev.grp_succ
#print axioms Lk6.Lev.partSum_succ
