-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/LinkSim/AtText/LastStep.lean: at the last stage, under premises on the two runs side by
side, and if the claim left at the base case is true, they disclose the same, except one element,
which is tauStar.
Terms: Johnson/LinkSim/Spec.lean; for the prover's algorithm, Johnson/LinkSim/AtText/Defs.lean.

What this file proves. Take the honest run (prover state Pr, columns colr) and the other run (Ps,
cols) at the last stage, at the same verifier challenges D. Assume that the states differ by d
(Pr = Ps + d) and that the masking words differ as WordRel says
(Johnson/LinkSim/AtText/SpecStage.lean): by minus the sampled element times the difference of
the last messages and their tails.
  last_shown_same   the four lists that the base case's second round discloses (shownAll,
                    Johnson/Prover/Link/Base.lean) are the same at both runs.
  last_group_same   the group of columns at the base case's opening is the same, if the two runs'
                    columns agree at the positions opened.
  last_tau          if the claim left at the base case is true at the honest run's last message
                    (ClaimTrue), the honest run's first-round element (tauSW at its masking word)
                    equals tauStar computed at the other run (Johnson/LinkSim/AtText/Defs.lean).
  lastOut_same      so, under these premises, the last stage's output (lastOut,
                    Johnson/Prover/Link/BodyAll.lean) has the same groups at both runs, and the
                    honest run's rounds are the other run's with the first-round element replaced by
                    tauStar.
Each statement is an equation between the two runs.

How it fits. LastStepOr.lean proves the same under a weaker premise (lastOut_same_or), and
Induct.lean uses that form as the base case of its induction on the list of stages. Under
Johnson/LinkSim/ no file uses lastOut_same itself.

Limits.
  - That the claim is true is a premise of last_tau and lastOut_same; LastStepOr.lean asks it only
    where the sampled element is not 0.
  - These lemmas are about one stage, the last.
Sources. The formula of the replaced element, on which the statements here rest, follows a write-up
of ours that is not in this repository (AtText/ShiftDefs.lean, "Sources."); how far the plan of the
proofs follows it is not known. That write-up does not count as made independently of the further
work that this protocol builds on (lean/CREDITS.md, under that heading).
Terms: lean/GLOSSARY.md.

-/
import Johnson.LinkSim.AtText.Step

set_option autoImplicit false

noncomputable section

namespace OnBytes.LinkSim.AtText
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open H2K.Pub (sgOf)
open Johnson.Prover.Link

variable {p : P12} {j : ℕ} {cur : Fmt.M1.Stage} {l : Laid} {o : ℕ} {t : T12} {Pr Ps d : PS}
  {colr cols : ℕ → List UInt64} {D : ℕ → Fmt.Drawn}

/-- If the states differ by d and the masking words as WordRel says, the four lists that the base
case's second round discloses are the same at both runs. -/
theorem last_shown_same (hst : Pr = addPS Ps d) (hw : WordRel D cur o d) :
    shownAll (sgOf cur).C (sgOf cur).Z ((D o).elems.headD (0, 0, 0))
        (mainOf (sgOf cur) (μOf (sgOf cur) Pr)) (Pr.tM 0) (maskOf (sgOf cur) (μOf (sgOf cur) Pr))
        (Pr.tZ 0) Pr.sM Pr.sT (Pr.fM 0) (Pr.fT 0) =
      shownAll (sgOf cur).C (sgOf cur).Z ((D o).elems.headD (0, 0, 0))
        (mainOf (sgOf cur) (μOf (sgOf cur) Ps)) (Ps.tM 0) (maskOf (sgOf cur) (μOf (sgOf cur) Ps))
        (Ps.tZ 0) Ps.sM Ps.sT (Ps.fM 0) (Ps.fT 0) := by
  have e0 : mainOf (sgOf cur) (μOf (sgOf cur) Pr) =
      mainOf (sgOf cur) (μOf (sgOf cur) Ps) + mainOf (sgOf cur) (μOf (sgOf cur) d) := by
    rw [hst, muOf_add]
    exact funext fun i => mainOf_add _ _ _ i
  have e1 : maskOf (sgOf cur) (μOf (sgOf cur) Pr) =
      maskOf (sgOf cur) (μOf (sgOf cur) Ps) + maskOf (sgOf cur) (μOf (sgOf cur) d) := by
    rw [hst, muOf_add]
    exact funext fun i => maskOf_add _ _ _ i
  have e2 : Pr.tM 0 = Ps.tM 0 + d.tM 0 := by rw [hst]; rfl
  have e3 : Pr.tZ 0 = Ps.tZ 0 + d.tZ 0 := by rw [hst]; rfl
  rw [e0, e1, e2, e3, shownAll_shift]
  have a0 : (fun i => Pr.sM i + toE ((D o).elems.headD (0, 0, 0)) *
      mainOf (sgOf cur) (μOf (sgOf cur) d) i) = Ps.sM := by
    funext i
    rw [hst]
    show Ps.sM i + d.sM i + _ = _
    rw [hw.sM i]
    ring
  have a1 : (fun q => Pr.sT q + toE ((D o).elems.headD (0, 0, 0)) * d.tM 0 q) = Ps.sT := by
    funext q
    rw [hst]
    show Ps.sT q + d.sT q + _ = _
    rw [hw.sT q]
    ring
  have a2 : (fun i => Pr.fM 0 i + toE ((D o).elems.headD (0, 0, 0)) *
      maskOf (sgOf cur) (μOf (sgOf cur) d) i) = Ps.fM 0 := by
    funext i
    rw [hst]
    show Ps.fM 0 i + d.fM 0 i + _ = _
    rw [hw.fM i]
    ring
  have a3 : (fun q => Pr.fT 0 q + toE ((D o).elems.headD (0, 0, 0)) * d.tZ 0 q) = Ps.fT 0 := by
    funext q
    rw [hst]
    show Ps.fT 0 q + d.fT 0 q + _ = _
    rw [hw.fT q]
    ring
  rw [a0, a1, a2, a3]

/-- The group of columns at the base case's opening is the same at both runs. -/
theorem last_group_same
    (hc : ∀ x ∈ Fmt.listOf (openAt (sgOf cur).C.a (D (o + 1)).poss), colr x = cols x) :
    groupAt (sgOf cur).C.a (D (o + 1)).poss colr =
      groupAt (sgOf cur).C.a (D (o + 1)).poss cols := by
  unfold groupAt
  exact List.map_congr_left fun x hx => by rw [hc x hx]

/-- If the claim is true at the honest run's last message, the honest run's first-round element
equals tauStar computed at the other run. -/
theorem last_tau (hst : Pr = addPS Ps d) (hw : WordRel D cur o d)
    (hcl : ClaimTrue p ⟨j, cur, l, o, t, Pr, colr⟩) :
    tauSW (sgOf cur).C (sgOf cur).Z (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).c
        (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).d Pr.sM (Pr.fM 0) =
      tauStar p ⟨j, cur, l, o, t, Ps, cols⟩ D := by
  have hcE : claimEnd p ⟨j, cur, l, o, t, Ps, cols⟩ = claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩ := rfl
  unfold tauSW tauStar
  rw [hcE]
  refine congrArg ofE ?_
  have hcl' : formG (sgOf cur).C.l (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).c
        (mainOf (sgOf cur) (μOf (sgOf cur) Pr)) +
      formG (sgOf cur).Z.l (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).d
        (maskOf (sgOf cur) (μOf (sgOf cur) Pr)) =
      toE (claimEnd p ⟨j, cur, l, o, t, Pr, colr⟩).tau := hcl
  have b0 : (fun i => Ps.sM i + toE ((D o).elems.headD (0, 0, 0)) *
      mainOf (sgOf cur) (μOf (sgOf cur) Ps) i) =
      fun i => Pr.sM i + toE ((D o).elems.headD (0, 0, 0)) *
        mainOf (sgOf cur) (μOf (sgOf cur) Pr) i := by
    funext i
    rw [hst, muOf_add, mainOf_add]
    show _ = Ps.sM i + d.sM i + _
    rw [hw.sM i]
    ring
  have b1 : (fun i => Ps.fM 0 i + toE ((D o).elems.headD (0, 0, 0)) *
      maskOf (sgOf cur) (μOf (sgOf cur) Ps) i) =
      fun i => Pr.fM 0 i + toE ((D o).elems.headD (0, 0, 0)) *
        maskOf (sgOf cur) (μOf (sgOf cur) Pr) i := by
    funext i
    rw [hst, muOf_add, maskOf_add]
    show _ = Ps.fM 0 i + d.fM 0 i + _
    rw [hw.fM i]
    ring
  show _ = formG (sgOf cur).C.l _ (fun i => Ps.sM i + toE ((D o).elems.headD (0, 0, 0)) *
      mainOf (sgOf cur) (μOf (sgOf cur) Ps) i) +
    formG (sgOf cur).Z.l _ (fun i => Ps.fM 0 i + toE ((D o).elems.headD (0, 0, 0)) *
      maskOf (sgOf cur) (μOf (sgOf cur) Ps) i) - _
  rw [b0, b1, tauSW_line, hcl']
  ring

/-- The last stage: the same groups at both runs, and the same rounds except the first-round
element, which is tauStar. -/
theorem lastOut_same (hst : Pr = addPS Ps d) (hw : WordRel D cur o d)
    (hc : ∀ x ∈ Fmt.listOf (openAt (sgOf cur).C.a (D (o + 1)).poss), colr x = cols x)
    (hcl : ClaimTrue p ⟨j, cur, l, o, t, Pr, colr⟩) :
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
    rw [last_tau hst hw hcl, last_shown_same hst hw]

end OnBytes.LinkSim.AtText

#print axioms OnBytes.LinkSim.AtText.last_shown_same
#print axioms OnBytes.LinkSim.AtText.last_tau
#print axioms OnBytes.LinkSim.AtText.lastOut_same
