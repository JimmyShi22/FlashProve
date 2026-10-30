-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/LastStepOr.lean: the last stage at two runs side by side, with the premise
on the claim asked only where the sampled element is not 0.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. The same as LastStep.lean, under a weaker premise. Where LastStep.lean asks
that the claim left at the base case be true (ClaimTrue), these lemmas ask that either the element
sampled in the base case's first round is 0 (LamZero) or the claim is true.
  last_tau_or      under that premise, the honest run's first-round element equals tauStar
                   computed at the other run.
  lastOut_same_or  under that premise, the last stage's output has the same groups at both runs,
                   and the honest run's rounds are the other run's with the first-round element
                   replaced by tauStar.
Why the weaker premise suffices: tauStar is the honest run's element plus the sampled element
times (the claim's left side at the honest run's last message, minus its target). Where the
sampled element is 0, the second term is 0.

How it fits. Induct.lean uses lastOut_same_or as the base case of its induction, to prove
Spec.bodyShiftOr (SpecShiftIn.lean).

Limits.
  - These lemmas are about one stage, the last.
Sources. The formula of the replaced element, on which the statements here rest, follows a write-up
of ours that is not in this repository (AtText/ShiftDefs.lean, "Sources."); how far the plan of the
proofs follows it is not known. That write-up does not count as made independently of the further
work that this protocol builds on (lean/CREDITS.md, under that heading).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.LastStep
import Johnson.LinkSim.AtText.SpecShiftIn

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link

variable {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12} {Pr Ps d : PS}
  {colr cols : ℕ → List UInt64} {D : ℕ → Fmt.Drawn}

/-- If the sampled element is 0 or the claim is true, the honest run's first-round element equals
tauStar computed at the other run. -/
theorem last_tau_or (hst : Pr = addPS Ps d) (hw : WordRel D cur o d)
    (hcl : LamZero D ⟨j, cur, l, o, t, Pr, colr⟩ ∨ ClaimTrue p ⟨j, cur, l, o, t, Pr, colr⟩) :
    tauSW (sgOf cur).C (sgOf cur).Z (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).c
        (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).d Pr.sM (Pr.fM 0) =
      tauStar p ⟨j, cur, l, o, t, Ps, cols⟩ D := by
  rcases hcl with h0 | hcl
  · have h0' : toE ((D o).elems.headD (0, 0, 0)) = 0 := h0
    have hcE : claimEnd p ⟨j, cur, l, o, t, Ps, cols⟩ = claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩ :=
      rfl
    unfold tauSW tauStar
    rw [hcE]
    refine congrArg ofE ?_
    have b0 : (fun i => Ps.sM i + toE ((D o).elems.headD (0, 0, 0)) *
        mainOf (sgOf cur) (μOf (sgOf cur) Ps) i) = Pr.sM := by
      funext i
      rw [hst]
      show _ = Ps.sM i + d.sM i
      rw [hw.sM i, h0']
      ring
    have b1 : (fun i => Ps.fM 0 i + toE ((D o).elems.headD (0, 0, 0)) *
        maskOf (sgOf cur) (μOf (sgOf cur) Ps) i) = Pr.fM 0 := by
      funext i
      rw [hst]
      show _ = Ps.fM 0 i + d.fM 0 i
      rw [hw.fM i, h0']
      ring
    show _ = formG (sgOf cur).C.l _ (fun i => Ps.sM i + toE ((D o).elems.headD (0, 0, 0)) *
        mainOf (sgOf cur) (μOf (sgOf cur) Ps) i) +
      formG (sgOf cur).Z.l _ (fun i => Ps.fM 0 i + toE ((D o).elems.headD (0, 0, 0)) *
        maskOf (sgOf cur) (μOf (sgOf cur) Ps) i) - toE ((D o).elems.headD (0, 0, 0)) * _
    rw [b0, b1, h0']
    ring
  · exact last_tau hst hw hcl

/-- The last stage, under LamZero or ClaimTrue: the same groups at both runs, and the same rounds
except the first-round element, which is tauStar. -/
theorem lastOut_same_or (hst : Pr = addPS Ps d) (hw : WordRel D cur o d)
    (hc : ∀ x ∈ Fmt.listOf (openAt (sgOf cur).C.a (D (o + 1)).poss), colr x = cols x)
    (hcl : LamZero D ⟨j, cur, l, o, t, Pr, colr⟩ ∨ ClaimTrue p ⟨j, cur, l, o, t, Pr, colr⟩) :
    (lastOut p j cur o t Pr colr (rowOf t) D).gs = (lastOut p j cur o t Ps cols (rowOf t) D).gs ∧
      (lastOut p j cur o t Pr colr (rowOf t) D).rs =
        (lastOut p j cur o t Ps cols (rowOf t) D).rs.set 0
          ⟨[.e (tauStar p ⟨j, cur, l, o, t, Ps, cols⟩ D)], D o⟩ := by
  constructor
  · exact congrArg (fun g => [g]) (last_group_same hc)
  · show [(⟨[.e (tauSW (sgOf cur).C (sgOf cur).Z (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).c
          (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).d Pr.sM (Pr.fM 0))], D o⟩ : Fmt.RoundView),
        ⟨(shownAll (sgOf cur).C (sgOf cur).Z ((D o).elems.headD (0, 0, 0))
          (mainOf (sgOf cur) (μOf (sgOf cur) Pr)) (Pr.tM 0)
          (maskOf (sgOf cur) (μOf (sgOf cur) Pr)) (Pr.tZ 0) Pr.sM Pr.sT (Pr.fM 0)
          (Pr.fT 0)).map .e, D (o + 1)⟩] =
      [⟨[.e (tauStar p ⟨j, cur, l, o, t, Ps, cols⟩ D)], D o⟩,
        ⟨(shownAll (sgOf cur).C (sgOf cur).Z ((D o).elems.headD (0, 0, 0))
          (mainOf (sgOf cur) (μOf (sgOf cur) Ps)) (Ps.tM 0)
          (maskOf (sgOf cur) (μOf (sgOf cur) Ps)) (Ps.tZ 0) Ps.sM Ps.sT (Ps.fM 0)
          (Ps.fT 0)).map .e, D (o + 1)⟩]
    rw [last_tau_or hst hw hcl, last_shown_same hst hw]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.last_tau_or
#print axioms OnBytes.LinkSim.AtText.lastOut_same_or
