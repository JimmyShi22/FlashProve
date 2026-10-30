-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FrontAtSmall.lean

What it proves. At the small made-up chain of SharedSmall.lean (P3), at the test on G_u: the Bool
frontFiveB (FrontAtShape.lean) is true at the plan's term for the shape of the state on entry, by
the kernel's evaluation. So at every job of a proximity test with the parameters p whose state on
entry is doorUF's (DoorsByShape.lean), FrontAsks (ShapeAll.lean) holds at every input and whatever
precedes the test, whatever the readers of the key and of the columns are: all eight clauses, with
no premise left.

Names.
  five_small   frontFiveB at the term.
  frontAsks_small   FrontAsks at every input and whatever precedes the test.
  The guards show that frontFiveB can fail.

Limits. One small made-up plan. The test on G_u alone: at the test on G_omega the first fold sends
its own mask, and frontFiveB is false there (a guard). The theorem is also true of the fall-back: it
does not tell a fold that failed from one that returned, and it is no statement that the state on
entry is the verifier's. FrontAsks is on the verifier's state alone: nothing on the prover's data,
nothing on the test's own challenges. The job is a parameter: jobAtU (JobShared.lean) is of another
type of jobs, of several sendings. It stands over files that are not in the library yet, as
MarksBehind.lean does. Nothing on completeness, on soundness or on what a view shows.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FrontAtShape
import Johnson.Desc.ProofFile.Honest.K12.DoorsAtSmall

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (TableKey)
open VerifiableInference.Desc (Block OpenedColumn)
open ProofFile.Honest.K12 (TestJob FrontAsks frontFiveB frontAsks_all)
open ProofFile.Honest.Sh (testSh)
open Desc.K14.Shape (doorO)

variable {W X : Type}

/-- **The five clauses on the shape hold at the plan's term.** -/
theorem five_small : frontFiveB p P3.codes (Desc.K14.Shape.doorU (endOf P3 sentU3)) = true := by
  decide +kernel

theorem early_p : p.early = true := by decide +kernel

/-- **FrontAsks at every input and whatever precedes the test on G_u, at P3.** -/
theorem frontAsks_small (J : TestJob W X) (hp : J.p = p) (key : W → TableKey)
    (cols : W → Front X → List OpenedColumn) (hJ : J.rec₀ = doorUF P3 sentU3 bs3 key cols) (w : W)
    (fr : Front X) : ∃ Dp, FrontAsks J w fr P3.codes Dp :=
  frontAsks_all J P3.codes (Desc.K14.Shape.doorU (endOf P3 sentU3)) (by rw [hp]; exact early_p)
    (fun w fr => by rw [hJ]; exact shape_small_UF key cols w fr) (by rw [hp]; exact five_small)
    (fun w fr => by
      rw [hJ]
      exact ⟨(three_small_UF key cols w fr).tidy, (three_small_UF key cols w fr).plain,
        (three_small_UF key cols w fr).claims⟩) w fr

/-! ## Guards -/

-- the Bool can fail: at other codes; at the old fall-back's shape; at the term of the other door
#guard !frontFiveB p {} (Desc.K14.Shape.doorU (endOf P3 sentU3))
#guard !frontFiveB p P3.codes (testSh (stateOfPub (pubBehind P3 sentU3, 0)))
#guard !frontFiveB pO P3.codes (doorO (endOmega P3 sentU3 p))
-- at the honest state it holds
#guard frontFiveB p P3.codes (testSh (doorAtU colsU () ProofFile.Honest.K12.Light.SharedToy.fr))

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.SharedSmall.five_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.early_p
#print axioms ProofFile.Honest.K12.Light.SharedSmall.frontAsks_small
