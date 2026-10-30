-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdRelAny.lean: mutual correlated agreement at every radius, nothing assumed beyond the
hypotheses of the statements: a weak bound.

Statements and proofs.
A code `C : LdCode E P` (Cb/Ld/LdRel.lean) encodes (message, randomness) to a native word; `C.T`
takes a native word f to a long word T f, with a symbol at each long position in P (`C.Aa`:
coordinates of a long symbol). Here E is a finite field and P is finite.
The laws (`C.Laws`): encoder and transformation are linear, the encoder is injective, and T f at a
long position depends only on f at the native positions that `C.src` names for it.
For native words f₀, f₁ and a radius e, a θ in E is exceptional if on some set S that omits at most
e long positions T f₀ + θ T f₁ agrees with the transform of a codeword (`C.OnCode`), while T f₀ and
T f₁ do not both do so on S. `C.MCAat e bad` says that every line has at most bad exceptional θ.
Many statements of this library are written twice: a definition in the namespace `Spec` states a
proposition, and a theorem of the same name outside that namespace proves it (lean/GLOSSARY.md).

Main names:
  `Spec.ld_mca_sets`: for a code read under a transformation (`LdCode`) with the laws, and any
    radius e, the number of exceptional θ of a line is at most the number of sets of long positions
    that omit at most e positions (`cnt`, Prob/Cnt.lean).

Why: each such set S has at most one exceptional θ, because if two different points of the line
T f₀ + θ T f₁ agree with codewords on S, so do T f₀ and T f₁ (the code is linear).

Limits: the number of sets grows exponentially with the number of positions: this is not a proximity
gap, and no parameter of a real protocol can rest on it. It serves as a guard: on a small code it
gives a count below the size of the field at a radius not below half the distance, so that the nine
clauses of `Spec.ld_toy` can be met together, with nothing assumed beyond the hypotheses of
`Spec.ld_toy` (Cb/Ld/LdRelToy.lean). Below a third of the distance (3 e < d) this library has e + 1
(`ldw_third`, Cb/Ld/LdBaseThird.lean; `Spec.prox_third`, stated in Cb/Gen/CodeList.lean); above, the
bound of a real code is a hypothesis wherever it is used, but for Reed-Solomon codes within half the
distance, whose bound is the number of positions (`mca_rsCode`, Code/Half.lean), and for codes whose
bound is proved from theirs.
The bound is this library's; it is not in the paper that this protocol builds on (lean/CREDITS.md).

Terms: lean/GLOSSARY.md.
-/
import Cb.Gen.CodeEraseLdProofs
import Prob.Count

set_option autoImplicit false

namespace Cb
open Prob

namespace Spec

/-- At most one exceptional θ for each large set of long positions. -/
def ld_mca_sets (E P : Type) [Field E] [Finite E] [Fintype P] : Prop :=
  ∀ C : LdCode E P,
    C.Laws → ∀ e : ℕ, C.MCAat e (cnt fun S : Finset P => Fintype.card P ≤ S.card + e)

/-- A larger count. States: `C.MCAat e bad` gives `C.MCAat e bad'` at every larger count,
bad ≤ bad'. -/
def ld_mca_mono (E P : Type) [Field E] [Finite E] [Fintype P] : Prop :=
  ∀ (C : LdCode E P) (e bad bad' : ℕ), bad ≤ bad' → C.MCAat e bad → C.MCAat e bad'

end Spec

/-- Under `hL : C.Laws`: combinations of two long words that agree with codewords on S (`h₀`, `h₁`)
agree with a codeword on S. -/
theorem onCode_line {E P : Type} [Field E] {C : LdCode E P} (hL : C.Laws) {S : Finset P}
    {g₀ g₁ : P → C.Aa → E} (c₀ c₁ : E) (h₀ : C.OnCode g₀ S) (h₁ : C.OnCode g₁ S) :
    C.OnCode (c₀ • g₀ + c₁ • g₁) S := by
  obtain ⟨m₀, r₀, a₀⟩ := h₀
  obtain ⟨m₁, r₁, a₁⟩ := h₁
  exact ⟨_, _, agreesOn_line hL (w₀ := (m₀, r₀)) (w₁ := (m₁, r₁)) c₀ c₁ a₀ a₁⟩

variable (E P : Type) [Field E] [Finite E] [Fintype P]

theorem ld_mca_mono : Spec.ld_mca_mono E P := fun _ _ _ _ hb h f₀ f₁ => le_trans (h f₀ f₁) hb

theorem ld_mca_sets : Spec.ld_mca_sets E P := by
  intro C hL e f₀ f₁
  classical
  cases nonempty_fintype E
  refine le_trans
    (cnt_exists_le (fun (S : Finset P) (θ : E) =>
      Fintype.card P ≤ S.card + e ∧
      C.OnCode (C.T f₀ + θ • C.T f₁) S ∧
      ¬ (C.OnCode (C.T f₀) S ∧ C.OnCode (C.T f₁) S))) ?_
  rw [cnt_eq_card_filter, Finset.card_filter]
  refine Finset.sum_le_sum fun S _ => ?_
  split_ifs with hS
  · refine cnt_le_one fun θ θ' h h' => ?_
    by_contra hne
    have hd : θ - θ' ≠ 0 := sub_ne_zero.2 hne
    have h1 : C.OnCode (C.T f₁) S := by
      have := onCode_line hL ((θ - θ')⁻¹) (-(θ - θ')⁻¹) h.2.1 h'.2.1
      have e1 : (θ - θ')⁻¹ • (C.T f₀ + θ • C.T f₁) + (-(θ - θ')⁻¹) • (C.T f₀ + θ' • C.T f₁) =
          C.T f₁ := by
        funext x α
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        have : (θ - θ')⁻¹ * (C.T f₀ x α + θ * C.T f₁ x α) +
              -(θ - θ')⁻¹ * (C.T f₀ x α + θ' * C.T f₁ x α) =
            (θ - θ')⁻¹ * (θ - θ') * C.T f₁ x α := by ring
        rw [this, inv_mul_cancel₀ hd, one_mul]
      rwa [e1] at this
    have h0 : C.OnCode (C.T f₀) S := by
      have := onCode_line hL 1 (-θ) h.2.1 h1
      have e0 : (1 : E) • (C.T f₀ + θ • C.T f₁) + (-θ) • C.T f₁ = C.T f₀ := by
        funext x α
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rwa [e0] at this
    exact h.2.2 ⟨h0, h1⟩
  · exact le_of_eq (cnt_false fun θ h => hS h.1)

end Cb
