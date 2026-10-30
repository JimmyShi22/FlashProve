-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/Fold.lean: in a fold's rounds, a change of the message is compensated by a
shift of the hiding polynomial's coefficients. General lemmas.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. In a fold the honest prover runs a sumcheck on the stage's message m, with a
hiding polynomial whose coefficients are W; the rounds it sends are foldRV s v m W D
(Johnson/Prover/Link/FoldSay.lean), where v is the claim's coefficients and D the challenges.
  foldRV_shift   foldRV s v (m + dm) W D = foldRV s v m (W + foldShift s v dm D) D: the same list of
                 rounds, for every claim v, every message m and change dm, every W and all
                 challenges D. There is no premise.
  foldShift s v dm D   the shift of the coefficients: shiftH (Johnson/LinkSim/FoldShift.lean) with
                 the sum changed by 0 and, for the rounds, at the coefficients 0 and 2 of the round
                 polynomials that the message dm gives without a hiding polynomial.
The proofs use honQ_add, honQ_zero (Johnson/LinkSim/SumAdd.lean), fold_shift
(Johnson/LinkSim/FoldShift.lean) and hTr_add (Cb/Ld/LdHideProofs.lean).

How it fits. Step.lean uses foldRV_shift at each fold, and AtStage (SpecStage.lean) asks that the
two runs' coefficients differ by foldShift.

The other names.
  foldQ_add      the honest round polynomials (foldQ, Johnson/Prover/Link/FoldHolds.lean) are
                 additive in the message and the coefficients, at a fixed claim, coefficient and
                 point.
  pairsOf_add, length_pairsOf   the pairs of coefficients 0 and 2 of the round polynomials
                 (Johnson/LinkSim/FoldTriTie.lean) are additive; there is one pair per round.
  showRV_pairs   the rounds, as the prover sends them, depend on these pairs alone.
  foldQ_zeroMsg  at the message 0 the round polynomials are those of the hiding polynomial alone.
  pairs_zero, addW_zero_left   the hiding polynomial 0 gives pairs of zeros; adding pairs of zeros
                 changes nothing.

Limits.
  - The claim's coefficients v are the same on both sides.
  - The shift reads the challenges of all the fold's rounds.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Prover.Link.FoldSay
import Johnson.LinkSim.SumAdd
import Johnson.LinkSim.FoldShift

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link
open VerifiableInference.Desc VerifiableInference.Desc.K12

theorem foldQ_add (s : Sg) (v m m' : s.cIn.J → GE) (W W' : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (ε : GE) (γ : HPt (sVars GE 2 (s.h + s.g))) :
    foldQ s v (m + m') (W + W') ε γ = foldQ s v m W ε γ + foldQ s v m' W' ε γ :=
  honQ_add (s.par 0) (m, fun _ => 0) (m', fun _ => 0) (m + m', fun _ => 0) rfl _ W W' ε γ

theorem pairsOf_add : ∀ (k : ℕ) (q q' : RIdx (sVars GE 2 k) → GE),
    pairsOf k (q + q') = addW (pairsOf k q) (pairsOf k q')
  | 0, _, _ => rfl
  | k + 1, q, q' => by
      show (q _ + q' _, q _ + q' _) :: pairsOf k ((fun i => q (.inr i)) + fun i => q' (.inr i)) = _
      rw [pairsOf_add k]
      rfl

theorem length_pairsOf : ∀ (k : ℕ) (q : RIdx (sVars GE 2 k) → GE), (pairsOf k q).length = k
  | 0, _ => rfl
  | k + 1, q => congrArg (· + 1) (length_pairsOf k fun i => q (.inr i))

theorem showRV_pairs : ∀ (k : ℕ) (q q' : RIdx (sVars GE 2 k) → GE) (D : ℕ → Fmt.Drawn),
    pairsOf k q = pairsOf k q' → showRV k q D = showRV k q' D
  | 0, _, _, _, _ => rfl
  | k + 1, q, q', D, h => by
      have h1 := (List.cons.inj h).1
      have h2 := (List.cons.inj h).2
      show (⟨[.e (ofE (q (Sum.inl (0 : Fin 3)))), .e (ofE (q (Sum.inl (2 : Fin 3))))], D 0⟩ :
          Fmt.RoundView) :: showRV k (fun i => q (Sum.inr i)) (fun n => D (n + 1)) =
        ⟨[.e (ofE (q' (Sum.inl (0 : Fin 3)))), .e (ofE (q' (Sum.inl (2 : Fin 3))))], D 0⟩ ::
          showRV k (fun i => q' (Sum.inr i)) fun n => D (n + 1)
      have e0 : q (Sum.inl (0 : Fin 3)) = q' (Sum.inl (0 : Fin 3)) := (Prod.ext_iff.mp h1).1
      have e2 : q (Sum.inl (2 : Fin 3)) = q' (Sum.inl (2 : Fin 3)) := (Prod.ext_iff.mp h1).2
      rw [showRV_pairs k _ _ _ h2, e0, e2]

/-- At the message 0, the round polynomials are those of the hiding polynomial alone. -/
theorem foldQ_zeroMsg (s : Sg) (v : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE) (ε : GE)
    (γ : HPt (sVars GE 2 (s.h + s.g))) :
    foldQ s v 0 W ε γ = hTr (sVars GE 2 (s.h + s.g)) 0 W γ := by
  have e0 : foldQ s v 0 0 ε γ = 0 := honQ_zero (s.par 0) (0, fun _ => 0) rfl _ ε γ
  funext i
  have e1 : foldQ s v 0 0 ε γ i = hTr (sVars GE 2 (s.h + s.g)) 0 0 γ i +
      ε * sTr 2 (s.h + s.g) ((s.par 0).tabL (0, (fun x => v (.inl x), fun x => v (.inr x))))
        ((s.par 0).tabM 0) γ i := rfl
  have e2 : hTr (sVars GE 2 (s.h + s.g)) (0 : GE) 0 γ = 0 := by
    have := hTr_add (sVars GE 2 (s.h + s.g)) (0 : GE) 0 0 0 γ
    rw [add_zero, add_zero] at this
    exact left_eq_add.mp this
  rw [e0, e2] at e1
  show hTr (sVars GE 2 (s.h + s.g)) 0 W γ i +
      ε * sTr 2 (s.h + s.g) ((s.par 0).tabL (0, (fun x => v (.inl x), fun x => v (.inr x))))
        ((s.par 0).tabM 0) γ i = _
  have e3 : ε * sTr 2 (s.h + s.g)
      ((s.par 0).tabL (0, (fun x => v (.inl x), fun x => v (.inr x)))) ((s.par 0).tabM 0) γ i =
      0 := by
    have : (0 : GE) = 0 + _ := e1
    rw [zero_add] at this
    exact this.symm
  rw [e3, add_zero]

/-- The hiding polynomial 0 gives pairs of zeros. -/
theorem pairs_zero : ∀ (k : ℕ) (γ : HPt (sVars GE 2 k)),
    pairsOf k (hTr (sVars GE 2 k) (0 : GE) 0 γ) = List.replicate k (0, 0) := by
  intro k γ
  have e : hTr (sVars GE 2 k) (0 : GE) 0 γ = 0 := by
    have := hTr_add (sVars GE 2 k) (0 : GE) 0 0 0 γ
    rw [add_zero, add_zero] at this
    exact left_eq_add.mp this
  rw [e]
  clear e γ
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg (List.cons ((0 : GE), (0 : GE))) ih

theorem addW_zero_left : ∀ {k : ℕ} (l : List (GE × GE)), l.length = k →
    addW (List.replicate k (0, 0)) l = l
  | 0, [], _ => rfl
  | 0, _ :: _, h => by cases h
  | _ + 1, [], h => by cases h
  | k + 1, x :: l, h => by
      show (0 + x.1, 0 + x.2) :: addW (List.replicate k (0, 0)) l = x :: l
      rw [addW_zero_left l (Nat.succ.inj h), zero_add, zero_add]

/-- The shift of the hiding polynomial's coefficients that compensates the change dm of the
message. -/
def foldShift (s : Sg) (v dm : s.cIn.J → GE) (D : ℕ → Fmt.Drawn) :
    HIdx (sVars GE 2 (s.h + s.g)) → GE :=
  shiftH (s.h + s.g) 0 (pairsOf (s.h + s.g)
    (foldQ s v dm 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))))

/-- The fold's rounds at the message m + dm and the coefficients W are its rounds at m and
W + foldShift s v dm D. -/
theorem foldRV_shift (s : Sg) (v m dm : s.cIn.J → GE) (W : HIdx (sVars GE 2 (s.h + s.g)) → GE)
    (D : ℕ → Fmt.Drawn) :
    foldRV s v (m + dm) W D = foldRV s v m (W + foldShift s v dm D) D := by
  have hs := fold_shift (s.h + s.g) (0 : HIdx (sVars GE 2 (s.h + s.g)) → GE) 0
    (pairsOf (s.h + s.g)
      (foldQ s v dm 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))))
    (length_pairsOf _ _) 0 (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))
  have hW := fold_shift (s.h + s.g) W 0
    (pairsOf (s.h + s.g)
      (foldQ s v dm 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))))
    (length_pairsOf _ _) 0 (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))
  unfold foldRV
  have eμ : hMu (sVars GE 2 (s.h + s.g)) (W + foldShift s v dm D) =
      hMu (sVars GE 2 (s.h + s.g)) W := by
    rw [foldShift, hW.1, add_zero]
  rw [eμ]
  refine congrArg _ (showRV_pairs _ _ _ _ ?_)
  have a1 : foldQ s v (m + dm) W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) =
      foldQ s v m W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) +
        foldQ s v dm 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) := by
    have := foldQ_add s v m dm W 0 (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))
    rwa [add_zero] at this
  have a2 : foldQ s v m (W + foldShift s v dm D) (drawnE (D 0))
        (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) =
      foldQ s v m W (drawnE (D 0)) (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) +
        foldQ s v 0 (foldShift s v dm D) (drawnE (D 0))
          (ptK (s.h + s.g) fun n => drawnE (D (n + 1))) := by
    have := foldQ_add s v m 0 W (foldShift s v dm D) (drawnE (D 0))
      (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))
    rwa [add_zero] at this
  rw [a1, a2, pairsOf_add, pairsOf_add, foldQ_zeroMsg]
  congr 1
  have h2 := hs.2
  rw [zero_add] at h2
  have z : pairsOf (s.h + s.g) (hTr (sVars GE 2 (s.h + s.g)) (0 : GE) 0
      (ptK (s.h + s.g) fun n => drawnE (D (n + 1)))) =
      List.replicate (s.h + s.g) (0, 0) := pairs_zero _ _
  rw [z] at h2
  rw [foldShift, h2, addW_zero_left _ (length_pairsOf _ _)]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.foldQ_add
#print axioms OnBytes.LinkSim.AtText.foldRV_shift
