-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/State.lean: the functions that build and read the link prover's state are
additive. General lemmas.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Each lemma says that a function of the prover's state (PS,
Johnson/Prover/Link/BodyState.lean) maps a sum to the sum of the images, at fixed sizes s, a fixed
fold point γ and a fixed stage. Sums of states are addPS (Johnson/LinkSim/AtText/Defs.lean).
  muOf_add, rhoOf_add, phiOf_add, psiOf_add   the four parts read off a state (its messages μOf, its
                 tails ρOf, and the messages φOf and tails ψOf of its further table) are additive
                 (Johnson/Prover/Link/BodyState.lean).
  foldMsg_add, foldTl_add   folding messages and tails at a fixed point is additive
                 (Johnson/Prover/Link/FoldEnc.lean).
  gMain_add, gMask_add      building the next stage's main table and mask table is additive
                 (Johnson/Prover/Link/SwitchMsg.lean).
  nextPS_add     the step from a stage to the next (nextPS, Johnson/Prover/Link/BodyState.lean) maps
                 sums of states, of new coins and of free entries to sums.
  packed_add, packedN_add   packing a fold's coefficients W into a mask row is additive in W
                 (Johnson/Prover/Link/FoldHolds.lean, Johnson/Prover/Link/BodyPack.lean).
  mainOf_add, maskOf_add    reading the main row and the mask row of a message is additive
                 (Johnson/Prover/Link/BaseClaim.lean).
  ps_ext         two states with equal fields are equal.
The proofs use foldV_add (Johnson/LinkSim/FoldAdd.lean) and pkAtC_add
(Johnson/LinkSim/PackAdd.lean).

How it fits. Step.lean, FrontStep.lean, LastStep.lean, Front.lean, CoinsAdd.lean, CoinsPlaces.lean
and ShortTail.lean use these lemmas.

Limits.
  - In every lemma the sizes, the point and the stage are the same on both sides.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Defs
import Johnson.LinkSim.FoldAdd
import Johnson.LinkSim.PackAdd

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

theorem ps_ext {P Q : PS} (h1 : P.tabM = Q.tabM) (h2 : P.tabZ = Q.tabZ) (h3 : P.tM = Q.tM)
    (h4 : P.tZ = Q.tZ) (h5 : P.fM = Q.fM) (h6 : P.fT = Q.fT) (h7 : P.sM = Q.sM)
    (h8 : P.sT = Q.sT) : P = Q := by
  cases P
  cases Q
  simp only at h1 h2 h3 h4 h5 h6 h7 h8
  subst h1 h2 h3 h4 h5 h6 h7 h8
  rfl

theorem muOf_add (s : Sg) (P Q : PS) : μOf s (addPS P Q) = μOf s P + μOf s Q := by
  funext x
  cases x <;> rfl

theorem rhoOf_add (s : Sg) (P Q : PS) : ρOf s (addPS P Q) = ρOf s P + ρOf s Q := by
  funext x
  cases x <;> rfl

theorem phiOf_add (s : Sg) (P Q : PS) : φOf s (addPS P Q) = φOf s P + φOf s Q := rfl

theorem psiOf_add (s : Sg) (P Q : PS) : ψOf s (addPS P Q) = ψOf s P + ψOf s Q := rfl

theorem foldMsg_add (s : Sg) (μ μ' : s.cIn.J → GE) (φ φ' : s.cFr.J → GE)
    (γ : Fin (s.h + s.g) → GE) :
    foldMsg s (μ + μ') (φ + φ') γ = foldMsg s μ φ γ + foldMsg s μ' φ' γ := by
  funext j
  rcases j with j | j | j
  · exact congrFun (foldV_add γ (fun x => μ (.inl x)) fun x => μ' (.inl x)) j
  · exact congrFun (foldV_add (preP s γ) (fun x => μ (.inr x)) fun x => μ' (.inr x)) j
  · exact congrFun (foldV_add (preP s γ) φ φ') j

theorem foldTl_add (s : Sg) (ρ ρ' : s.cIn.Q → GE) (ψ ψ' : s.cFr.Q → GE)
    (γ : Fin (s.h + s.g) → GE) :
    foldTl s (ρ + ρ') (ψ + ψ') γ = foldTl s ρ ψ γ + foldTl s ρ' ψ' γ := by
  funext j
  rcases j with j | j | j
  · exact congrFun (foldV_add γ (fun x => ρ (.inl x)) fun x => ρ' (.inl x)) j
  · exact congrFun (foldV_add (preP s γ) (fun x => ρ (.inr x)) fun x => ρ' (.inr x)) j
  · exact congrFun (foldV_add (preP s γ) ψ ψ') j

theorem gMain_add (s : Sg) (μ ν : s.cMid.J → GE) (i : ℕ) :
    gMain s (μ + ν) i = gMain s μ i + gMain s ν i := by
  unfold gMain
  split_ifs
  · rfl
  · exact (add_zero _).symm

theorem gMask_add (s : Sg) (μ ν : s.cMid.J → GE) (tl tl' : s.cMid.Q → GE) (fr fr' : ℕ → GE)
    (i : ℕ) :
    gMask s (μ + ν) (tl + tl') (fr + fr') i = gMask s μ tl fr i + gMask s ν tl' fr' i := by
  unfold gMask
  split_ifs <;> rfl

/-- The step from a stage to the next maps sums of states, new coins and free entries to sums. -/
theorem nextPS_add (s : Sg) (γ : Fin (s.h + s.g) → GE) (fr fr' : ℕ → GE) (new new' P Q : PS) :
    nextPS s γ (fr + fr') (addPS new new') (addPS P Q) =
      addPS (nextPS s γ fr new P) (nextPS s γ fr' new' Q) := by
  refine ps_ext (funext fun i => ?_) (funext fun i => ?_) rfl rfl rfl rfl rfl rfl
  · show gMain s (foldMsg s (μOf s (addPS P Q)) (φOf s (addPS P Q)) γ) i = _
    rw [muOf_add, phiOf_add, foldMsg_add, gMain_add]
    rfl
  · show gMask s (foldMsg s (μOf s (addPS P Q)) (φOf s (addPS P Q)) γ)
      (foldTl s (ρOf s (addPS P Q)) (ψOf s (addPS P Q)) γ) (fr + fr') i = _
    rw [muOf_add, phiOf_add, rhoOf_add, psiOf_add, foldMsg_add, foldTl_add, gMask_add]
    rfl

theorem packed_add (s : Sg) (hl : s.h + 2 * s.g + 1 ≤ s.Z.l)
    (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE) :
    packed s hl (W + W') = packed s hl W + packed s hl W' :=
  pkAtC_add s.h s.g 1 (placeF s hl) W W'

theorem packedN_add (s : Sg) (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE) (b j : ℕ) :
    packedN s (W + W') b j = packedN s W b j + packedN s W' b j := by
  unfold packedN
  split_ifs with h
  · rw [packed_add]
    rfl
  · exact (add_zero _).symm

theorem mainOf_add (s : Sg) (w w' : s.cIn.J → GE) (j : ℕ) :
    mainOf s (w + w') j = mainOf s w j + mainOf s w' j := by
  unfold mainOf
  split_ifs
  · rfl
  · exact (add_zero _).symm

theorem maskOf_add (s : Sg) (w w' : s.cIn.J → GE) (j : ℕ) :
    maskOf s (w + w') j = maskOf s w j + maskOf s w' j := by
  unfold maskOf
  split_ifs
  · rfl
  · exact (add_zero _).symm

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.nextPS_add
#print axioms OnBytes.LinkSim.AtText.packedN_add
