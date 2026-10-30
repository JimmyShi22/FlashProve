-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Hiop/Chain.lean: the budget of a composition, written in its two parts, and small facts on the
positions and the oracles of two lists of rounds in a row.

In standard terms: book-keeping for the sequential composition of interactive oracle reductions.

Statements and proofs. A block is an interactive oracle reduction (`IOR`, Ior/Ior.lean); a chain is
the sequential composition of blocks (`IOR.seq`). In the constructions each block but the first
starts at (encoded index, oracles so far) and leaves (encoded index, oracles from then on).
Ior/Chain.lean has the rule for all properties along a chain (the bundle `IOR.Good`, the structure
of the properties of one IOR; `Spec.good_seq`; proved in Ior/ChainProofs.lean).

Main names:
 1. `OPos.forall_append`: what holds at every position of each of two shapes holds at every position
    of the two in a row. `fst_read`, `snd_read`: the oracles of a transcript of two shapes in a row,
    cut in two, are the oracles of its two parts.
 2. `budSeq_iff`: the composed budget, written with the two parts of the set of further positions.
    `budSeq_quiet`: if the second verifier reads nothing of its implicit instance and nothing is
    tied: `budSeq` ↔ each of the two bears the part of the further positions that lies in its own
    oracles.

Limits: this file gives no protocol. It says nothing on numbers of positions read in the oracles so
far.

Terms: lean/GLOSSARY.md.
-/
import Ior.Chain
import Ior.SeqProofs
import Ior.ExactSeq

set_option autoImplicit false

namespace Iop
open Prob
open scoped ENNReal

/-- If P holds at every position of the first shape and at every position of the second, it holds
at every position of the two in a row. -/
theorem OPos.forall_append {s t : Shape} {P : OPos (s ++ t) → Prop} (hl : ∀ p, P (OPos.left p))
    (hr : ∀ p, P (OPos.right (s := s) p)) (p : OPos (s ++ t)) : P p := by
  have e := OPos.elim_split (s := s) p
  rcases hq : OPos.split (s := s) p with q | q
  · rw [hq] at e
    exact e ▸ hl q
  · rw [hq] at e
    exact e ▸ hr q

namespace IOR
variable {X₁ X₂ X₃ : Type}

/-! ## 1. The oracles of a transcript's two parts -/

theorem fst_read {s t : Shape} (τ : Tr (s ++ t)) : Orcs.fst τ.read = (Tr.fst τ).read :=
  funext fun p => Tr.read_left τ p
theorem snd_read {s t : Shape} (τ : Tr (s ++ t)) :
    Orcs.snd (s := s) τ.read = (Tr.snd (s := s) τ).read :=
  funext fun p => Tr.read_right τ p

/-! ## 2. The composed budget -/

section Budget
variable {E₁ E₂ E₃ : ExtSpec} (R₁ : IOR X₁ E₁ X₂ E₂) (R₂ : IOR X₂ E₂ X₃ E₃)
  (b₁ : Rho R₁.shape → Finset (OPos R₁.shape) → Prop)
  (b₂ : Rho R₂.shape → Finset (OPos R₂.shape) → Prop)

open Classical in
/-- The composed budget, with the two parts of T written out. -/
theorem budSeq_iff (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape))) :
    budSeq R₁ R₂ b₁ b₂ ρ T ↔
    b₂ (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T) ∧
    b₁ (Rho.fst ρ)
      (partL T ∪
        (R₂.given (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T)).biUnion
          (R₁.srcO (Rho.fst ρ))) := by
  constructor
  · intro h
    exact h (partL T) (partR R₁.shape T) (fun _ => mem_partL) (fun _ => mem_partR)
  · intro h T₁ T₂ h₁ h₂
    have e₁ : T₁ = partL T := Finset.ext fun p => (h₁ p).trans mem_partL.symm
    have e₂ : T₂ = partR R₁.shape T := Finset.ext fun p => (h₂ p).trans mem_partR.symm
    subst e₁ e₂
    exact h

/-- If the second verifier reads nothing of its implicit instance and nothing is tied: `budSeq` ↔
each bears its own part of the further positions. -/
theorem budSeq_quiet (hr : ∀ ρ, R₂.extReads ρ = ∅) (ht : ∀ ρ p, R₂.tie ρ p = ∅)
    (ρ : Rho (R₁.shape ++ R₂.shape)) (T : Finset (OPos (R₁.shape ++ R₂.shape))) :
    budSeq R₁ R₂ b₁ b₂ ρ T ↔
    b₁ (Rho.fst ρ) (partL T) ∧ b₂ (Rho.snd (s := R₁.shape) ρ) (partR R₁.shape T) := by
  classical
  have hg : ∀ ρ₂ T₂, R₂.given ρ₂ T₂ = ∅ := fun ρ₂ T₂ => by
    unfold given
    rw [hr, Finset.empty_union]
    exact Finset.eq_empty_of_forall_notMem fun u hu => by
      obtain ⟨p, _, hp⟩ := Finset.mem_biUnion.1 hu
      rw [ht] at hp
      exact Finset.notMem_empty _ hp
  rw [budSeq_iff, hg, Finset.biUnion_empty, Finset.union_empty, and_comm]

end Budget
end IOR
end Iop
