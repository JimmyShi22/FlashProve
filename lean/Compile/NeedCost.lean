-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/NeedCost.lean: the hash blocks that the rounds of a protocol need, added up, and two helper
lemmas for counting (words of this library: lean/GLOSSARY.md).

When one hash function implements the typed oracles, a typed query costs as many hash queries as
hash blocks of its answer are asked for. Where, at the Fiat-Shamir query of round j, nbf j hash
blocks (those of the verifier message of that round) and the chaining value are asked for, that
query costs at most nbf j + 1. nbf is a parameter.

  `cnt_le_of`                  Of n indices, those equal to a or below b are at most b + 1.
  `CostBoundAt.weight`         A smaller weight costs no more.
  `sumNb nbf s i`              nbf j + 1 for each round j of the list of rounds s, added up; i is
                               the number of the first round.
  `sumNb_eq_sum`, `sumNb_le`   The same as the sum of a list; with nbf j ≤ K for every j it is at
                               most (the number of rounds) · (K + 1).

Use. For the compiled scheme: Compile/Batch/NeedCost.lean (the verifier's bound), with the choice
of hash blocks of Compile/Batch/NeedTable.lean.

Notation: `cnt n nd` (Rom/OverOneN.lean), a natural number: the number of flagged indices among n;
`c.CostBoundAt w t` (the same file), a proposition: on every path, whatever the answers and the
coins, the weights w o q of the queries add up to at most t; `s : Shape`: the list of rounds of a
protocol (`InteractiveOracleProof.shape`, Iop/InteractiveOracleProof.lean); hash block: a `Dig lam` (Iop/Wire.lean): lam bits.

Limits: nothing on any algorithm, but for `CostBoundAt.weight`, which is on every oracle algorithm.

Terms: lean/GLOSSARY.md.
-/
import Compile.NeedBlocks
import Compile.GlueBinding

set_option autoImplicit false

open Rom Iop

namespace Compile
namespace Need

/-! ## The number of needed blocks -/

/-- of n indices, those equal to a or below b are at most b + 1 -/
theorem cnt_le_of (n a b : ℕ) :
    cnt n (fun j : Fin n => decide (j.val = a ∨ j.val < b)) ≤ b + 1 := by
  rw [cnt_eq]
  have h : ((Finset.univ.filter fun j : Fin n => decide (j.val = a ∨ j.val < b) = true).map
        ⟨Fin.val, Fin.val_injective⟩) ⊆
      insert a (Finset.range b) := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.1 hx
    have hj' := of_decide_eq_true (Finset.mem_filter.1 hj).2
    rcases hj' with e | e
    · exact Finset.mem_insert.2 (Or.inl e)
    · exact Finset.mem_insert.2 (Or.inr (Finset.mem_range.2 e))
  have h1 := Finset.card_le_card h
  rw [Finset.card_map] at h1
  exact h1.trans ((Finset.card_insert_le _ _).trans (by rw [Finset.card_range]))

/-- a smaller weight costs no more -/
theorem _root_.Rom.OComp.CostBoundAt.weight {S : OSpec} {α : Type} {w w' : (o : S.ι) → S.Dom o → ℕ}
    (h : ∀ o q, w' o q ≤ w o q) {c : OComp S α} :
    ∀ {t : ℕ}, c.CostBoundAt w t → c.CostBoundAt w' t := by
  induction c with
  | pure a => exact fun _ => trivial
  | sample n k ih => exact fun H r => ih r (H r)
  | query o q k ih =>
    rintro t ⟨t', rfl, H⟩
    exact ⟨w o q - w' o q + t', by have := h o q; omega, fun r => (ih r (H r)).mono (by omega)⟩

/-! ## The sum -/

/-- for each round the blocks of its verifier message and the chaining value; i is the number of the
first round -/
def sumNb (nbf : ℕ → ℕ) : Shape → ℕ → ℕ
  | [], _ => 0
  | _ :: s, i => (nbf i + 1) + sumNb nbf s (i + 1)

/-! ## Lemmas on the sum -/

theorem sumNb_eq_sum (nbf : ℕ → ℕ) :
    ∀ (s : Shape) (i : ℕ), sumNb nbf s i = ((List.range s.length).map fun k => nbf (i + k) + 1).sum
  | [], _ => rfl
  | _ :: s, i => by
      rw [sumNb, sumNb_eq_sum nbf s (i + 1), List.length_cons, List.range_succ_eq_map,
        List.map_cons, List.sum_cons, List.map_map, Nat.add_zero]
      congr 2
      refine List.map_congr_left fun k _ => ?_
      show nbf (i + 1 + k) + 1 = nbf (i + (k + 1)) + 1
      rw [show i + 1 + k = i + (k + 1) by omega]

theorem sumNb_le {nbf : ℕ → ℕ} {K : ℕ} (h : ∀ i, nbf i ≤ K) :
    ∀ (s : Shape) (i : ℕ), sumNb nbf s i ≤ s.length * (K + 1)
  | [], _ => Nat.zero_le _
  | _ :: s, i => by
      have h1 := sumNb_le h s (i + 1)
      have h2 := h i
      rw [sumNb, List.length_cons, Nat.succ_mul]
      omega


end Need
end Compile
