-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Model/Fit/FitPlanned.lean: wherever the program's planner returns at three configuration
files, every entry of the six plans of a key file's and a proof file's chains, as they are read back
from the chains' parameter bytes, asks few blocks of a hash chain's answer and counts at most two
roots. No premise but the planner's yes.

Main names:
  small_of_planned : Verify.planned pol KL layout = .ok p → every entry of the six plans as the
    planner has made them (p.chains.made.key, p.chains.made.proof) is Small
    (OnBytes/Params/Fit/FitCalc.lean).
  fits_of_planned : Verify.planned pol KL layout = .ok p → Six Fits p (SmallRead.lean in this
    folder): of every entry e of the plans p.chains.key.oneTime | shared | second and
    p.chains.proof.first | shared | second (….given.plan.entries): e.logN ≤ 64,
    Fmt.blocksFor (Fmt.wordsAtMost e .sealed) + 1 < 2 ^ 48 and e.roots ≤ 2.
How it goes: FitTop.lean in this folder has the first under caps on two records of sizes
(made_small_planned); these follow from the yes of the planner's own routine sized, from the ranges
that the reader of the parameter file's 32 lines admits, and from the text of the routine that makes
a request's links from the declared arrays and the layout file's lines (Plan.reqFrame;
OnBytes/Params/Fit/TreesFrame.lean) (OnBytes/Params/Fit/FitCaps.lean, KeyCaps.lean; TreesShapes.lean
in this folder).
Limits: nothing where the planner refuses. That the planner returns at any files is not said here.
Nothing on the plan of an entry's chain (Configured.entry), which the planner also makes. Nothing on
what a round's error is. "sealed" is the kind of round with the most words (Fmt.wordsAtMost).
The program does not import this file.

-/
import OnBytes.Model.Fit.FitTop
import OnBytes.Model.Fit.TreesShapes
import OnBytes.Params.Fit.KeyCaps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Model.Verify

section
variable {pol KL : ByteArray} {layout : Option ByteArray} {p : Planned}

/-- **Every entry of the six made plans is Small.** -/
theorem small_of_planned (h : planned pol KL layout = .ok p) :
    ∀ P ∈ p.chains.made.key ++ p.chains.made.proof, ∀ r ∈ P.rounds, Params.Small r.entry := by
  obtain ⟨links, shapes, rest, declared, file, rl, lay, hX, hL, _, h1, h2, hc, _, _, hrf, hsub⟩ :=
    planned_parts h
  have LC := Params.linesCap_of_read hL
  have hz := (Params.configure_plans hc).1
  have hcl : Params.TreeClassCap shapes.sub.links := by
    rw [hsub]
    exact subproofsWith_class p.X hrf
  exact made_small_planned h (Params.reqCap_of_sized hz LC hcl) (Params.keyCap_of_sized hz LC)

/-- **Every entry of the six plans as read back asks few blocks and counts at most two roots.** -/
theorem fits_of_planned (h : planned pol KL layout = .ok p) : Six Fits p :=
  fits_read h (small_of_planned h)

end

end OnBytes.Model.Verify

#print axioms OnBytes.Model.Verify.small_of_planned
#print axioms OnBytes.Model.Verify.fits_of_planned
