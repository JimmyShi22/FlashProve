-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Front.lean: the functions that build the link prover's first message are
additive. General lemmas.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. In the link's front the prover folds each committed table's rows into one row
at the verifier's point γ, and lays out the two folded rows as the first prover state. Each lemma
says that one of these functions maps a sum to the sum of the images, at fixed sizes S and a fixed
point γ.
  membMsg_add    one folded row's message is additive in the fold's coefficients and in its other
                 entries (Johnson/Prover/Link/FrontMsg.lean).
  frontMem_add   the two folded rows' messages are additive in the two tables and in the other
                 entries (Johnson/Prover/Link/BodyEnds.lean).
  mu0_add, membN_add   the layouts of the folded rows' messages are additive
                 (Johnson/Prover/Link/FrontMsg.lean, Johnson/Prover/Link/FrontCols.lean).
  firstPS_add    the first prover state at sums is the sum (addPS, Defs.lean) of the first states
                 (Johnson/Prover/Link/BodyState.lean).
The proofs use foldAll_add (Johnson/LinkSim/FoldAdd.lean).

How it fits. FrontStep.lean, PadPlace.lean, ShortTail.lean and TwoAnswers.lean use these lemmas.

Limits.
  - In every lemma the sizes and the point are the same on both sides.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.State

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

theorem membMsg_add (S : Sz) (u u' : S.Co → GE) (fr fr' : S.MJ → GE) :
    membMsg S (u + u') (fr + fr') = membMsg S u fr + membMsg S u' fr' := by
  funext j
  rcases j with x | x
  · show membMsg S (u + u') (fr + fr') (.inl x) =
      membMsg S u fr (.inl x) + membMsg S u' fr' (.inl x)
    simp only [membMsg]
    split_ifs <;> rfl
  · exact x.1.elim

theorem frontMem_add (S : Sz) (γ : Fin S.P.v → GE)
    (M₀ M₀' M₁ M₁' : (Fin S.P.v → Bool) → S.Co → GE) (fr fr' : Bool → S.MJ → GE) :
    frontMem S γ (M₀ + M₀') (M₁ + M₁') (fr + fr') =
      frontMem S γ M₀ M₁ fr + frontMem S γ M₀' M₁' fr' := by
  funext a
  cases a
  · show membMsg S (foldAll γ (M₀ + M₀')) (fr false + fr' false) = _
    rw [foldAll_add, membMsg_add]
    rfl
  · show membMsg S (foldAll γ (M₁ + M₁')) (fr true + fr' true) = _
    rw [foldAll_add, membMsg_add]
    rfl

theorem mu0_add (S : Sz) (t : ℕ) (m m' : Bool → S.MJ → GE) :
    mu0 S t (m + m') = mu0 S t m + mu0 S t m' := by
  funext x
  rcases x with x | x
  · show mu0 S t (m + m') (.inl x) = mu0 S t m (.inl x) + mu0 S t m' (.inl x)
    simp only [mu0]
    split_ifs
    · rfl
    · exact (add_zero _).symm
  · exact (add_zero (0 : GE)).symm

theorem membN_add (S : Sz) (m m' : Bool → S.MJ → GE) (a : Bool) (i j : ℕ) :
    membN S (m + m') a i j = membN S m a i j + membN S m' a i j := by
  unfold membN
  split_ifs
  · rfl
  · exact (add_zero _).symm

/-- The first prover state is additive in the folded rows' messages, their tails, and the row
beside them with its tail. -/
theorem firstPS_add (S : Sz) (m m' : Bool → S.MJ → GE) (tN tN' : Bool → ℕ → ℕ → GE)
    (φN φN' ψN ψN' : ℕ → GE) :
    firstPS S (m + m') (tN + tN') (φN + φN') (ψN + ψN') =
      addPS (firstPS S m tN φN ψN) (firstPS S m' tN' φN' ψN') := by
  refine ps_ext (funext fun i => ?_) (funext fun _ => (add_zero (0 : GE)).symm)
    (funext fun n => funext fun q => ?_) (funext fun _ => funext fun _ => (add_zero (0 : GE)).symm)
    rfl rfl (funext fun _ => (add_zero (0 : GE)).symm) (funext fun _ => (add_zero (0 : GE)).symm)
  · show (firstPS S (m + m') (tN + tN') (φN + φN') (ψN + ψN')).tabM i =
      (firstPS S m tN φN ψN).tabM i + (firstPS S m' tN' φN' ψN').tabM i
    unfold firstPS
    simp only
    split_ifs
    · exact membN_add S m m' _ _ _
    · exact (add_zero _).symm
  · show (firstPS S (m + m') (tN + tN') (φN + φN') (ψN + ψN')).tM n q =
      (firstPS S m tN φN ψN).tM n q + (firstPS S m' tN' φN' ψN').tM n q
    unfold firstPS
    simp only
    split_ifs
    · rfl
    · exact (add_zero _).symm

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.frontMem_add
#print axioms OnBytes.LinkSim.AtText.firstPS_add
