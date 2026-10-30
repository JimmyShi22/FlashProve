-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/FoldInjAt.lean: a fold's rounds determine the hiding polynomial's
coefficients, at a fixed claim, message and challenges. General lemmas.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. foldRV s v m W D is the list of rounds that the prover sends in a fold, with
claim coefficients v, message m, hiding-polynomial coefficients W and challenges D
(Johnson/Prover/Link/FoldSay.lean).
  foldRV_inj       if foldRV s v m W D = foldRV s v m W' D, then W = W'.
  foldRV_forces    so, if the rounds at the message m + dm and coefficients W are the rounds at m
                   and W', then W' = W + foldShift s v dm D: the shift of the coefficients is
                   forced. It is the converse of foldRV_shift (Johnson/LinkSim/AtText/Fold.lean).
The proofs use hW_inj, addW_cancel (Johnson/LinkSim/FoldInj.lean) and foldRV_shift.

How it fits. ShortTail.lean, a negative test of the form of Spec.linkShiftIn, uses foldRV_forces to
prove that the difference of a row's message is forced. TwoAnswers.lean uses ofE_inj
from this file.

The other names.
  ofE_inj          two field elements that are written alike are equal.
  pairs_of_showRV  equal lists of rounds have equal pairs of coefficients 0 and 2 (the converse of
                   showRV_pairs, Johnson/LinkSim/AtText/Fold.lean).

Limits.
  - The claim's coefficients v and the challenges are the same on both sides.
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Fold
import Johnson.LinkSim.FoldInj

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link

theorem ofE_inj {x y : GE} (h : ofE x = ofE y) : x = y := by
  rw [← toE_ofE x, ← toE_ofE y, h]

theorem pairs_of_showRV : ∀ (k : ℕ) (q q' : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    showRV k q D = showRV k q' D → pairsOf k q = pairsOf k q'
  | 0, _, _, _, _ => rfl
  | k + 1, q, q', D, h => by
      have h' : (⟨[.e (ofE (q (Sum.inl (0 : Fin 3)))), .e (ofE (q (Sum.inl (2 : Fin 3))))], D 0⟩ :
          Fmt.RoundView) :: showRV k (fun i => q (Sum.inr i)) (fun n => D (n + 1)) =
        ⟨[.e (ofE (q' (Sum.inl (0 : Fin 3)))), .e (ofE (q' (Sum.inl (2 : Fin 3))))], D 0⟩ ::
          showRV k (fun i => q' (Sum.inr i)) fun n => D (n + 1) := h
      have h1 := congrArg Fmt.RoundView.vals (List.cons.inj h').1
      have h2 := pairs_of_showRV k _ _ _ (List.cons.inj h').2
      have a0 : Fmt.ItemValue.e (ofE (q (Sum.inl (0 : Fin 3)))) = .e (ofE (q' (Sum.inl (0 : Fin 3)))) :=
        (List.cons.inj h1).1
      have a2 : Fmt.ItemValue.e (ofE (q (Sum.inl (2 : Fin 3)))) = .e (ofE (q' (Sum.inl (2 : Fin 3)))) :=
        (List.cons.inj (List.cons.inj h1).2).1
      show (q (Sum.inl (0 : Fin 3)), q (Sum.inl (2 : Fin 3))) ::
          pairsOf k (fun i => q (Sum.inr i)) =
        (q' (Sum.inl (0 : Fin 3)), q' (Sum.inl (2 : Fin 3))) :: pairsOf k fun i => q' (Sum.inr i)
      rw [h2, ofE_inj (Fmt.ItemValue.e.inj a0), ofE_inj (Fmt.ItemValue.e.inj a2)]

/-- A fold's rounds, at a fixed claim, message and challenges, determine the coefficients W. -/
theorem foldRV_inj (s : Sg) (v m : s.cIn.J → GE) (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) (h : foldRV s v m W D = foldRV s v m W' D) : W = W' := by
  unfold foldRV at h
  have h1 := congrArg Fmt.RoundView.vals (List.cons.inj h).1
  have a : Fmt.ItemValue.e (ofE (hMu (sVars GE 2 (s.h + s.g)) W)) =
      .e (ofE (hMu (sVars GE 2 (s.h + s.g)) W')) := (List.cons.inj h1).1
  have hp := pairs_of_showRV _ _ _ _ (List.cons.inj h).2
  have sp : ∀ V : HIdx (sVars GE 2 (s.h + s.g)) → GE,
      foldQ s v m V (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) =
        hTr (sVars GE 2 (s.h + s.g)) 0 V (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) +
          foldQ s v m 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) := by
    intro V
    have e := foldQ_add s v 0 m V 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))
    rw [zero_add, add_zero, foldQ_zeroMsg] at e
    exact e
  rw [sp W, sp W', pairsOf_add, pairsOf_add] at hp
  exact hW_inj _ W W' 0 _ (ofE_inj (Fmt.ItemValue.e.inj a))
    (addW_cancel _ _ _ (by rw [length_pairsOf, length_pairsOf])
      (by rw [length_pairsOf, length_pairsOf]) hp)

/-- If the rounds at m + dm and W equal the rounds at m and W', then W' = W + foldShift s v dm D. -/
theorem foldRV_forces (s : Sg) (v m dm : s.cIn.J → GE)
    (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE) (D : ℕ → Fmt.Drawn)
    (h : foldRV s v (m + dm) W D = foldRV s v m W' D) : W' = W + foldShift s v dm D := by
  rw [foldRV_shift] at h
  exact (foldRV_inj s v m _ _ D h).symm

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.foldRV_inj
#print axioms OnBytes.LinkSim.AtText.foldRV_forces
