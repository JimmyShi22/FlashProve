-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K9/Honest/LensPaid/LayFlat.lean: what the library's laying of a feed-forward segment's tables lays, read as
a list of pairs (matrix, rows in a block), and the sum over that list of "the matrix's rows over the rows in a block".
General: any list of sizes, any list of families, any function that gives a matrix's rows; no scope and no numeral.
Two definitions, statements and proofs.

  famPairs a: the pairs of one family a = (first matrix, number of parts, rows in a block): one pair for each part.
  famReads rows a: the sum over these pairs of rows (matrix) / (rows in a block).
  layParts_mats, layParts_pairs: the parts that Layer.layParts (OnBytes/Model/LayerForms.lean) lays for a family stand
    on the matrices M0, M0 + 1, ... in their order, whatever the sizes: by induction on the parts still to be laid,
    after layParts_run (Johnson/Road/FormsKeysTab.lean), which asks that all parts have one size.
  layTables_pairs: where Layer.layTables returns, the pairs of what it has laid are the families' pairs, family by
    family: by induction on the list of families, with the opening of layTables_bound (Johnson/Meaning/ReadsPlan.lean).
  sum_flat: the sum over all pairs is the sum of the families' sums.
  famReads_const, famReads_one: a family whose matrices all have m rows: parts * (m / L). After famSum_const and
    famSum_one (Johnson/Road/K4/Plan/TabsEndSum.lean).
  flat_below: if every family ends at or below B, every pair's matrix is below B.

Limits. Arithmetic on lists. That the laying returns anywhere is not said here. Nothing is said of the tables' places or
of what an entry holds. No property of the protocol is claimed: nothing is said on its soundness, completeness, binding
or hiding.
-/
import Johnson.Road.FormsKeysTab
import Johnson.Road.K4.Plan.TabsEndSum
import Johnson.Desc.First.K8.LawShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K9

open OnBytes.Model.Layer (TableAsk TableAt layParts layTables)
open VerifiableInference.Desc.First.K8 (triOf)

/-! ## One family -/

/-- The pairs (matrix, rows in a block) of one family, given as first matrix, number of parts, rows in a block. -/
def famPairs (a : ℕ × ℕ × ℕ) : List (ℕ × ℕ) :=
  (List.range a.2.1).map fun q => (a.1 + q, a.2.2)

/-- The reads of one family: over its pairs, the matrix's rows over the rows in a block. -/
def famReads (rows : ℕ → ℕ) (a : ℕ × ℕ × ℕ) : ℕ :=
  ((famPairs a).map fun t => rows t.1 / t.2).sum

/-- The last n parts of a family, each read as the pair of its matrix and a given number L, stand on the last n of its
matrices, in their order. -/
theorem layParts_mats (mats : Array (ℕ × ℕ)) (a : TableAsk) (L : ℕ) :
    ∀ (n p : ℕ), n ≤ a.parts → (layParts mats a n p).1.map (fun m => (m.1, L)) =
      (List.range n).map fun i => (a.M0 + (a.parts - n + i), L)
  | 0, p, _ => by
    show ([] : List (ℕ × ℕ)).map (fun m => (m.1, L)) = _
    simp
  | n + 1, p, hn => by
    rw [OnBytes.Road.layParts_succ]
    show (a.M0 + (a.parts - (n + 1)), L) :: (layParts mats a n _).1.map (fun m => (m.1, L)) = _
    rw [layParts_mats mats a L n _ (by omega), List.range_succ_eq_map, List.map_cons, List.map_map]
    refine congrArg₂ List.cons ?_ ?_
    · simp only [Nat.add_zero]
    · refine List.map_congr_left fun i _ => ?_
      show (a.M0 + (a.parts - n + i), L) = (a.M0 + (a.parts - (n + 1) + (i + 1)), L)
      have e : a.parts - n + i = a.parts - (n + 1) + (i + 1) := by omega
      rw [e]

/-- The parts that are laid for a family, as pairs, are the family's pairs. -/
theorem layParts_pairs (mats : Array (ℕ × ℕ)) (a : TableAsk) (p : ℕ) :
    (layParts mats a a.parts p).1.map (fun m => (m.1, a.L)) = famPairs (triOf a) := by
  rw [layParts_mats mats a a.L a.parts p (Nat.le_refl _)]
  simp only [Nat.sub_self, Nat.zero_add]
  rfl

/-! ## All families -/

/-- Where the laying returns, the pairs of what it has laid are the families' pairs, family by family. -/
theorem layTables_pairs (mats : Array (ℕ × ℕ)) : ∀ (asks : List TableAsk) (p : ℕ)
    (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ), layTables mats asks p = some r →
    (r.2.1.flatMap fun a => a.2.map fun m => (m.1, a.1.L)) = (asks.map triOf).flatMap famPairs
  | [], p, r, h => by
    unfold layTables at h
    cases h
    rfl
  | a :: rest, p, r, h => by
    unfold layTables at h
    dsimp only at h
    split at h
    · cases h
    · obtain ⟨r', hr, rfl⟩ := Option.map_eq_some_iff.mp h
      show (((a, (layParts mats a a.parts p).1) :: r'.2.1).flatMap
        fun a => a.2.map fun m => (m.1, a.1.L)) = _
      rw [List.flatMap_cons]
      show (layParts mats a a.parts p).1.map (fun m => (m.1, a.L)) ++ _ = _
      rw [layParts_pairs mats a p, layTables_pairs mats rest _ r' hr, List.map_cons, List.flatMap_cons]

/-- The sum over all pairs is the sum of the families' sums. -/
theorem sum_flat (rows : ℕ → ℕ) : ∀ l : List (ℕ × ℕ × ℕ),
    ((l.flatMap famPairs).map fun t => rows t.1 / t.2).sum = (l.map (famReads rows)).sum
  | [] => by simp
  | a :: l => by
    rw [List.flatMap_cons, List.map_append, List.sum_append, sum_flat rows l, List.map_cons, List.sum_cons]
    rfl

/-- A family whose matrices all have m rows. -/
theorem famReads_const (rows : ℕ → ℕ) {M0 n L m : ℕ} (h : ∀ q, q < n → rows (M0 + q) = m) :
    famReads rows (M0, n, L) = n * (m / L) := by
  have e : ((famPairs (M0, n, L)).map fun t => rows t.1 / t.2) = List.replicate n (m / L) := by
    rw [List.eq_replicate_iff]
    refine ⟨by simp [famPairs], fun b hb => ?_⟩
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hb
    unfold famPairs at ht
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 ht
    show rows (M0 + q) / L = m / L
    rw [h q (List.mem_range.1 hq)]
  show ((famPairs (M0, n, L)).map fun t => rows t.1 / t.2).sum = _
  rw [e, OnBytes.Road.K4.Plan.sum_rep]

/-- A family of one matrix. -/
theorem famReads_one (rows : ℕ → ℕ) {M0 L m : ℕ} (h : ∀ q, q < 1 → rows (M0 + q) = m) :
    famReads rows (M0, 1, L) = m / L := by
  rw [famReads_const rows h, Nat.one_mul]

/-- If every family ends at or below B, every pair's matrix is below B. -/
theorem flat_below {B : ℕ} {l : List (ℕ × ℕ × ℕ)} (h : ∀ a ∈ l, a.1 + a.2.1 ≤ B) :
    ∀ t ∈ l.flatMap famPairs, t.1 < B := by
  intro t ht
  obtain ⟨a, ha, hta⟩ := List.mem_flatMap.1 ht
  unfold famPairs at hta
  obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hta
  have h1 := h a ha
  have h2 := List.mem_range.1 hq
  show a.1 + q < B
  omega

end ProofFile.Honest.K9

#print axioms ProofFile.Honest.K9.famPairs
#print axioms ProofFile.Honest.K9.famReads
#print axioms ProofFile.Honest.K9.layParts_mats
#print axioms ProofFile.Honest.K9.layParts_pairs
#print axioms ProofFile.Honest.K9.layTables_pairs
#print axioms ProofFile.Honest.K9.sum_flat
#print axioms ProofFile.Honest.K9.famReads_const
#print axioms ProofFile.Honest.K9.famReads_one
#print axioms ProofFile.Honest.K9.flat_below
