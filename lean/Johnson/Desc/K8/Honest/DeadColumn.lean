-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/K8/Honest/DeadColumn.lean: THE SMALLNESS TEST: HOW OFTEN A COLUMN OF THE DRAWN MATRIX
IS ALL 0. Statements and proofs. A count over the typed matrix of coefficients, two uniform bits
each (`Dr s`, Cb/Pv/Tail/Size.lean; `Prob.Coef`, Prob/Window.lean: 0 at two of the four values). No
block, no state, no prover. Lemmas; none of the library's goals. NOTHING IS CLAIMED ON COMPLETENESS,
SOUNDNESS OR HIDING.

  `dead_row`    of the rows of one combination: half have a 0 at a given column
  **`dead_one`**   of the typed matrices: just one in 2^tau has a given column all 0
  **`dead_few`**   so at most (columns) in 2^tau have some column all 0
  `live_iff`    the tie to the verifier's own sequence: where the smallness test's data hold the
      sequence that a typed matrix stands for (`listOf`, OnBytes/Tie/Pv/Tail/Draw.lean),
      `columnLive` (Johnson/Desc/K8/Honest/FallCount.lean) says no at a column just if that column
      of the typed matrix is all 0
THE MEASURE is over a uniform typed matrix. It is no count of drawn sequences (4^n typed matrices
stand for 3^n sequences) and none of written verifier messages.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.K8.Honest.FallCount
import OnBytes.Tie.Pv.Tail.Draw
import Prob.Window
import Prob.Count

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K8.Honest
open OnBytes OnBytes.Model Cb.Pv.Tail OnBytes.Tie.Pv.Tail

/-- Of the rows of k coefficients: twice as many as have a 0 at column c. -/
theorem dead_row (k : Nat) (c : Fin k) :
    Prob.cnt (fun row : Fin k → Prob.Coef => (row c).val = 0) * 2 =
      Fintype.card (Fin k → Prob.Coef) := by
  have h := Prob.cnt_pi_coord (A := fun _ : Fin k => Prob.Coef) c (fun x : Prob.Coef => x.val = 0)
  rw [Prob.Coef.cnt_val.1] at h
  have h4 : Fintype.card Prob.Coef = 4 := by decide
  rw [h4] at h
  omega

/-- Of the matrices of tau rows of k coefficients: 2^tau times as many as have column c all 0. -/
theorem dead_block (tau k : Nat) (c : Fin k) :
    Prob.cnt (fun M : Fin tau → Fin k → Prob.Coef => ∀ u, (M u c).val = 0) * 2 ^ tau =
      Fintype.card (Fin tau → Fin k → Prob.Coef) := by
  rw [Prob.cnt_forall_pow (fun row : Fin k → Prob.Coef => (row c).val = 0) tau, ← mul_pow,
    dead_row k c]
  simp only [Fintype.card_fun, Fintype.card_fin]

/-- **One column.** -/
theorem dead_one (s : Size) (μ : Fin s.NM) (c : Fin (s.k μ)) :
    Prob.cnt (fun β : Dr s => ∀ u, (β μ u c).val = 0) * 2 ^ s.tau = Fintype.card (Dr s) := by
  have h := Prob.cnt_pi_coord (A := fun ν : Fin s.NM => Fin s.tau → Fin (s.k ν) → Prob.Coef) μ
    (fun M : Fin s.tau → Fin (s.k μ) → Prob.Coef => ∀ u, (M u c).val = 0)
  have hb := dead_block s.tau (s.k μ) c
  have hpos : 0 < Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef) := Fintype.card_pos
  have e : (Prob.cnt (fun β : Dr s => ∀ u, (β μ u c).val = 0) * 2 ^ s.tau) *
      Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef) =
      Fintype.card (Dr s) * Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef) := by
    calc (Prob.cnt (fun β : Dr s => ∀ u, (β μ u c).val = 0) * 2 ^ s.tau) *
          Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef)
        = (Prob.cnt (fun β : Dr s => ∀ u, (β μ u c).val = 0) *
            Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef)) * 2 ^ s.tau := by ring
      _ = (Prob.cnt (fun M : Fin s.tau → Fin (s.k μ) → Prob.Coef => ∀ u, (M u c).val = 0) *
            Fintype.card (Dr s)) * 2 ^ s.tau := by rw [h]
      _ = (Prob.cnt (fun M : Fin s.tau → Fin (s.k μ) → Prob.Coef => ∀ u, (M u c).val = 0) *
            2 ^ s.tau) * Fintype.card (Dr s) := by ring
      _ = Fintype.card (Dr s) * Fintype.card (Fin s.tau → Fin (s.k μ) → Prob.Coef) := by
          rw [hb]
          ring
  exact Nat.eq_of_mul_eq_mul_right hpos e

/-- **Some column.** -/
theorem dead_few (s : Size) :
    Prob.cnt (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) *
        2 ^ s.tau ≤ s.columns * Fintype.card (Dr s) := by
  have h1 : Prob.cnt (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) ≤
      ∑ x : (Σ μ : Fin s.NM, Fin (s.k μ)), Prob.cnt (fun β : Dr s => ∀ u, (β x.1 u x.2).val = 0) :=
    (Prob.cnt_mono fun β ⟨μ, c, h⟩ => (⟨⟨μ, c⟩, h⟩ :
      ∃ x : (Σ μ : Fin s.NM, Fin (s.k μ)), ∀ u, (β x.1 u x.2).val = 0)).trans
      (Prob.cnt_exists_le fun (x : Σ μ : Fin s.NM, Fin (s.k μ)) (β : Dr s) =>
        ∀ u, (β x.1 u x.2).val = 0)
  calc Prob.cnt (fun β : Dr s => ∃ (μ : Fin s.NM) (c : Fin (s.k μ)), ∀ u, (β μ u c).val = 0) *
        2 ^ s.tau
      ≤ (∑ x : (Σ μ : Fin s.NM, Fin (s.k μ)),
          Prob.cnt (fun β : Dr s => ∀ u, (β x.1 u x.2).val = 0)) * 2 ^ s.tau :=
        Nat.mul_le_mul_right _ h1
    _ = ∑ x : (Σ μ : Fin s.NM, Fin (s.k μ)), Fintype.card (Dr s) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun x _ => dead_one s x.1 x.2
    _ = s.columns * Fintype.card (Dr s) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_sigma, smul_eq_mul]
        simp [Size.columns]

/-- The tie to the verifier's own sequence. -/
theorem live_iff (s : Size) (β : Dr s) (tl : HTailF2) (μ : Fin s.NM) (c : Fin (s.k μ))
    (h1 : tl.cfF = listOf β) (h2 : tl.tau = s.tau) (h3 : tl.cfFirst.getD μ.val 0 = firstCol s μ) :
    columnLive tl μ.val c.val = false ↔ ∀ u, (β μ u c).val = 0 := by
  simp only [columnLive, List.any_eq_false, List.mem_range, bne_iff_ne, ne_eq, Decidable.not_not]
  rw [h1, h2, h3]
  constructor
  · intro h u
    rw [← listOf_get β μ c u]
    exact h u.val u.isLt
  · intro h u hu
    rw [listOf_get β μ c ⟨u, hu⟩]
    exact h ⟨u, hu⟩

end VerifiableInference.Desc.First.K8.Honest

#print axioms VerifiableInference.Desc.First.K8.Honest.dead_one
#print axioms VerifiableInference.Desc.First.K8.Honest.dead_few
#print axioms VerifiableInference.Desc.First.K8.Honest.live_iff
