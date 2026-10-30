-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/PiecesLaid.lean: THE SMALLNESS TEST: A LIGHT TEST ON PUBLIC NUMBERS, ON THE
FEW PIECES OF THE DIGITS' LOOKUP's TWO CALLS, THAT GIVES `digitsCover`
(Johnson/Desc/K8/Honest/DigitsLiveOf.lean), WHICH RUNS OVER ALL ENTRIES. Definitions with code,
statements and proofs. On plain data: no block, no prover. Lemmas; none of the library's goals.

tl: the smallness test's data. nb: the number of blocks of the digits' array ZZ's rows; mz: half the
number of its columns.
  `pieceKey p`   a piece's array, virtual row, first column and number of columns
  **`piecesLaid tl`**   with code: the first call's pieces bear (ZZ, i, 0, mz), i < nb, in that
      order; the second's (ZZ, nb + i, mz, mz): as piecesF (OnBytes/Model/Tail.lean) lays them
  `range_none`, `range_one`   of the numbers below n none, or just one, meets a test
  **`cover_of_laid`**   `piecesLaid tl` gives `digitsCover tl`
Limits. `piecesLaid` is a premise: that any state's data meet it is not shown here.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.DigitsLiveOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model OnBytes.Model.HTailF2
open VerifiableInference.Desc

/-- A piece's array, virtual row, first column and number of columns. -/
def pieceKey (p : OnBytes.Model.Piece) : Nat × Nat × Nat × Nat := (p.tree, p.row, p.c0, p.Cp)

/-- The two calls' pieces lie as piecesF lays them. -/
def piecesLaid (tl : HTailF2) : Bool :=
  (tl.z1.pieces.toList.map pieceKey ==
      (List.range tl.zzBlocks).map fun i => (tl.ix.ZZ, i, 0, tl.mz)) &&
    (tl.z2.pieces.toList.map pieceKey ==
      (List.range tl.zzBlocks).map fun i => (tl.ix.ZZ, tl.zzBlocks + i, tl.mz, tl.mz))

/-- The test of `pieceCovers` on a key. -/
def keyCovers (k : Nat × Nat × Nat × Nat) (t r i : Nat) : Bool :=
  decide (k.1 = t ∧ k.2.1 = r ∧ k.2.2.1 ≤ i ∧ i < k.2.2.1 + k.2.2.2)

theorem range_none (p : Nat → Bool) : ∀ n, (∀ i, i < n → p i = false) →
    ((List.range n).filter p).length = 0
  | 0, _ => rfl
  | n + 1, h => by
    rw [List.range_succ, List.filter_append, List.length_append,
      range_none p n fun i hi => h i (Nat.lt_succ_of_lt hi)]
    simp [h n (Nat.lt_succ_self n)]

theorem range_one (p : Nat → Bool) (b : Nat) : ∀ n, b < n → p b = true →
    (∀ i, i < n → i ≠ b → p i = false) → ((List.range n).filter p).length = 1
  | 0, hb, _, _ => absurd hb (Nat.not_lt_zero b)
  | n + 1, hb, hp, h => by
    rw [List.range_succ, List.filter_append, List.length_append]
    by_cases e : b = n
    · subst e
      rw [range_none p b fun i hi => h i (Nat.lt_succ_of_lt hi) (Nat.ne_of_lt hi)]
      simp [hp]
    · rw [range_one p b n (by omega) hp fun i hi => h i (Nat.lt_succ_of_lt hi)]
      simp [h n (Nat.lt_succ_self n) (Ne.symm e)]

/-- How many pairs' pieces cover an entry, by the keys. -/
theorem cover_count (tl : HTailF2) (t r i : Nat) :
    ((joinPairs tl).filter fun x => pieceCovers x.2 t r i).length =
      ((tl.z1.pieces.toList.map pieceKey).filter fun k => keyCovers k t r i).length +
        ((tl.z2.pieces.toList.map pieceKey).filter fun k => keyCovers k t r i).length := by
  have e : joinPairs tl = (tl.z1.pieces.toList.map fun p => (0, p)) ++
      (tl.z2.pieces.toList.map fun p => (1, p)) := by
    unfold joinPairs
    simp [HTailF2.zOf]
  rw [e, List.filter_append, List.length_append, List.filter_map, List.filter_map,
    List.filter_map, List.filter_map, List.length_map, List.length_map, List.length_map,
    List.length_map]
  rfl

/-- **The light test gives the test on all entries.** -/
theorem cover_of_laid (tl : HTailF2) (h : piecesLaid tl = true) : digitsCover tl = true := by
  unfold piecesLaid at h
  rw [Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  unfold digitsCover
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true]
  intro b hb u hu
  constructor
  · unfold oneCover
    rw [cover_count, h1, h2, List.filter_map, List.filter_map, List.length_map, List.length_map,
      range_one _ b _ hb (by simp [keyCovers, hu]) (fun i _ hi => by simp [keyCovers, hi]),
      range_none _ _ (fun i _ => by
        simp only [Function.comp, keyCovers, decide_eq_false_iff_not]
        intro hc
        have := hc.2.1
        omega)]
    rfl
  · unfold oneCover
    rw [cover_count, h1, h2, List.filter_map, List.filter_map, List.length_map, List.length_map,
      range_none _ _ (fun i hi => by
        simp only [Function.comp, keyCovers, decide_eq_false_iff_not]
        intro hc
        have := hc.2.1
        omega),
      range_one _ b _ hb (by simp [keyCovers, hu]) (fun i _ hi => by simp [keyCovers, hi])]
    rfl

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.range_one
#print axioms VerifiableInference.Desc.First.K8.Honest.cover_count
#print axioms VerifiableInference.Desc.First.K8.Honest.cover_of_laid
