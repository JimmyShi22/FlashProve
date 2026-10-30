-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/SumAdd.lean: the library's honest round polynomials of a fold are additive in the
message and in the hiding polynomial's coefficients. Statements and proofs. Pure algebra.
Terms of this folder: Johnson/LinkSim/Spec.lean.

What this file has.
  honQ_add      The honest round polynomials SumPar.honQ at the message w.1 + w'.1 and the
                coefficients W + W' are the sum of honQ at (w, W) and at (w', W'), for the same
                claim x, sampled coefficient ε and point γ.
  honQ_zero     At the message 0 and the coefficients 0 they are 0.
  sTr_add       The round polynomials of the claim polynomial (sTr, Cb/Ld/LdSum.lean) are additive
                in the message's table m, at a fixed L and point.
Here honQ is the hiding polynomial's round polynomials plus ε times those of the claim polynomial.
The proof uses hTr_add (Cb/Ld/LdHideProofs.lean) for the first summand.

How it fits. Used in the proof of homeExact (Johnson/LinkSim/AtHome/Home.lean).
Johnson/LinkSim/AtText/Fold.lean uses honQ_add and honQ_zero.

Other names (namespace OnBytes.LinkSim).
  sBl_add, sHalf_add, sFold1_add   the pairing of two tables is additive in the second table; a
                table's halves and its fold in one variable are additive.
  tabM_add      the message's table of a stage (SumPar.tabM) is additive.
Terms: lean/GLOSSARY.md.

-/
import Cb.Ld.LdSum
import Cb.Ld.LdHideProofs

set_option autoImplicit false

namespace OnBytes.LinkSim
open Cb

section Rounds
variable {E : Type} [Field E] {J : Type} [Fintype J]

/-- The pairing sBl is additive in the second table. -/
theorem sBl_add {k : ℕ} (L m m' : (Fin k → Bool) → J → E) :
    sBl L (m + m') = sBl L m + sBl L m' := by
  show (∑ b, ∑ c, L b c * (m b c + m' b c)) = (∑ b, ∑ c, L b c * m b c) + ∑ b, ∑ c, L b c * m' b c
  simp only [mul_add, Finset.sum_add_distrib]

/-- A table's halves are additive. -/
theorem sHalf_add {k : ℕ} (β : Bool) (m m' : (Fin (k + 1) → Bool) → J → E) :
    sHalf β (m + m') = sHalf β m + sHalf β m' := rfl

/-- The fold in one variable is additive. -/
theorem sFold1_add {k : ℕ} (x : E) (m m' : (Fin (k + 1) → Bool) → J → E) :
    sFold1 x (m + m') = sFold1 x m + sFold1 x m' := by
  funext b c
  show (1 - x) * (sHalf false m b c + sHalf false m' b c) +
      x * (sHalf true m b c + sHalf true m' b c) =
    ((1 - x) * sHalf false m b c + x * sHalf true m b c) +
      ((1 - x) * sHalf false m' b c + x * sHalf true m' b c)
  ring

/-- The claim polynomial's round polynomials are additive in the message. -/
theorem sTr_add (n : ℕ) : ∀ (k : ℕ) (L m m' : (Fin k → Bool) → J → E) (γ : HPt (sVars E n k))
    (i : RIdx (sVars E n k)), sTr n k L (m + m') γ i = sTr n k L m γ i + sTr n k L m' γ i
  | 0, _, _, _, _, i => i.elim
  | k + 1, L, m, m', γ, .inl t => by
      simp only [sTr, sHalf_add, add_sub_add_comm, sBl_add]
      split_ifs <;> ring
  | k + 1, L, m, m', γ, .inr i => by
      show sTr n k (sFold1 γ.1 L) (sFold1 γ.1 (m + m')) γ.2 i = _
      rw [sFold1_add]
      exact sTr_add n k _ _ _ γ.2 i

end Rounds

section Par
variable {E P : Type} [Field E] [Fintype E] (Y : SumPar E P)

/-- The message's table of a stage is additive in the message. -/
theorem tabM_add (m m' : Y.Cin.J → E) : Y.tabM (m + m') = Y.tabM m + Y.tabM m' := by
  funext b c
  cases c <;> rfl

/-- The honest round polynomials are additive in the message and in the hiding polynomial's
coefficients, at fixed x, ε and γ. -/
theorem honQ_add (w w' w'' : Y.Cin.N.Wit) (h : w''.1 = w.1 + w'.1) (x : Y.Xi)
    (W W' : HIdx Y.vars → E) (ε : E) (γ : HPt Y.vars) :
    Y.honQ w'' x (W + W') ε γ = Y.honQ w x W ε γ + Y.honQ w' x W' ε γ := by
  funext i
  have e : hTr Y.vars (0 : E) (W + W') γ = hTr Y.vars 0 W γ + hTr Y.vars 0 W' γ := by
    have := hTr_add Y.vars (0 : E) 0 W W' γ
    rwa [add_zero] at this
  show hTr Y.vars 0 (W + W') γ i + ε * sTr Y.n Y.k (Y.tabL x) (Y.tabM w''.1) γ i =
    (hTr Y.vars 0 W γ i + ε * sTr Y.n Y.k (Y.tabL x) (Y.tabM w.1) γ i) +
      (hTr Y.vars 0 W' γ i + ε * sTr Y.n Y.k (Y.tabL x) (Y.tabM w'.1) γ i)
  rw [e, h, tabM_add, sTr_add]
  show (hTr Y.vars 0 W γ i + hTr Y.vars 0 W' γ i) + _ = _
  ring

/-- At the message 0 and the coefficients 0 the honest round polynomials are 0. -/
theorem honQ_zero (w : Y.Cin.N.Wit) (h : w.1 = 0) (x : Y.Xi) (ε : E) (γ : HPt Y.vars) :
    Y.honQ w x 0 ε γ = 0 := by
  have e := honQ_add Y w w w (by rw [h, add_zero]) x 0 0 ε γ
  rw [add_zero] at e
  exact left_eq_add.mp e

end Par

end OnBytes.LinkSim

#print axioms OnBytes.LinkSim.sTr_add
#print axioms OnBytes.LinkSim.honQ_add
#print axioms OnBytes.LinkSim.honQ_zero
