-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K3/Law/LookHeardOne.lean: the honest side of the kind "lookup" (K3).
Conditional on `StageStep` and on `LeavesStep` (Honest/K3/Law/Statements.lean: statements, proved in
no file that this one imports) and at one part of keys: the conclusion of `LookHeard`: the
verifier's hearing returns on the rounds of a course; with two clauses more on what the rows that
were heard are worth (`RowsGood`; the leaves' row). One theorem.

Terms. Honest/K3/GLOSSARY.md ("course", "hearing", "stage").

What is shown.
  `lookHeard_one`: a composition of `lookHeard_of_steps` (Honest/K3/Law/LookHeard.lean), which asks
    that the course's rounds are cut by stage, with Honest/K3/Law/CutOf.lean, which shows that they
    are.

Hypotheses that remain.
  `StageStep` and `LeavesStep`: both are assumed here. Shown in: `stageStep` and `leavesStep`
    (Honest/K3/Law/StageStep.lean), conditional on `HB`; `stageStepP` and `leavesStepP`
    (Honest/K3/Law/HBPaid.lean), without `HB`, resting on the theorems of Honest/SumLaw/.
  One part of keys: every lookup of a proof file's links is such.
  By name: `SS`, `LS`, `hp`. Besides: `hF`: `Fit R`; `I0`: the invariant in front of the first
    stage; `h`: the course's stages answer (`R.rounds = some x`).

Users. This file is imported by Honest/K3/Law/LookOne.lean.

Limits. It is not `LookHeard` itself, which speaks of every face.
Not claimed: anything on soundness, completeness or any other property of a protocol.
-/
import Johnson.Desc.ProofFile.Honest.K3.Law.LookHeard
import Johnson.Desc.ProofFile.Honest.K3.Law.CutOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K3.Law
open OnBytes (oneE)
open OnBytes.Model (Fork Aff Reading)
open OnBytes.Slice (GE)
open OnBytes.PscRun (Filled Sized Later)
open VerifiableInference.Desc.Part
open VerifiableInference.Desc.K3 (hearV)

/-- **Conditional on `StageStep`, on `LeavesStep`, at one part of keys: the conclusion of
`LookHeard`.** -/
theorem lookHeard_one (SS : StageStep) (LS : LeavesStep) (W : Type) (R : Course W) (F : Fork)
    (x : List Fmt.RoundView) (v : Nat) (hp : R.f.parts = [v]) (hF : Fit R) (I0 : Inv R 0 F)
    (h : R.rounds = some x) :
    ∃ g G, hearV R.f F x = some (g, G) ∧ HeardIs R g ∧ Inv R (stages R.f).length G ∧
      (∀ j, R.first + firstSlot R.f .leaves ≤ j →
        j < R.first + firstSlot R.f .leaves + Stage.own R.f .leaves → ¬ Filled G j) ∧
      RowsGood R g.rows G ∧
      (∀ cf : GE, Sums R .leaves (rd (R.claimed .leaves)) cf →
        ∀ (F' G' H : Fork) (y : Aff) (mask : Nat → GE) (entry : Nat → Nat → Nat → GE),
          Sized F' → Later G F' → MaskedSum.row g.leaves oneE {} F' = some (y, G') →
          Later G' H → MasksAre R mask →
          y.value Reading.gl (H.worldOf Reading.gl mask entry) = rd g.leaves.eps * (1 - cf)) :=
  lookHeard_of_steps SS LS R F x v hp hF I0 (cut_of_rounds R x hF h)

#print axioms ProofFile.Honest.K3.Law.lookHeard_one

end ProofFile.Honest.K3.Law
