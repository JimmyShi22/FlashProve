-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/TwoTypes.lean: what it means that two jobs of a proximity test are
the same job at two types X and X' of the value that the prover's parts pass on. Definitions only.

Why. A job (`TestJob W X`, Test.lean; `RunJob W X`, RunJob.lean) has fields that read what precedes
the test (`Front X`, Johnson/Desc/ProofFile/Honest/Sum.lean), and with it the passed-on value. So
`proverSideOfProximityTest` (Parts.lean) is not one definition that is general in X: it is applied to a job at X and
to a job at X', and a hypothesis has to say that the two are the same job.

  `FrontBy r`    two fronts have the same challenges and the same rounds shown, and their passed-on
                 values are related by r
  `JobAlike r`   two values of `TestJob` have the same parameters, members and sender of the fresh
                 table, and their three functions agree on fronts related by `FrontBy r`
  `RunAlike r`   the same for two values of `RunJob`
  `TestJob.reOwn g`, `RunJob.reOwn g`   a job at X as a job at X': it reads the passed-on value
                 through g : X' → X

TwoTypesLaw.lean proves that the jobs made by `reOwn` satisfy the two relations, and what follows
from the relations for `proverSideOfProximityTest`, `lightHalf` and `lightHalfOf`.

Limits.
- `JobAlike` and `RunAlike` are hypotheses on the caller's two jobs. Nothing here shows them for
  jobs that are written separately at two types.
- If r never holds, the clauses on the functions are empty.
- Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunJob

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light

variable {W X X' : Type}

/-- Two fronts with the same challenges and rounds shown, their passed-on values related by r. -/
def FrontBy (r : X → X' → Prop) (a : Front X) (b : Front X') : Prop :=
  a.heard = b.heard ∧ r a.own b.own ∧ a.seen = b.seen

/-- The same job at two types of the passed-on value. -/
structure JobAlike (r : X → X' → Prop) (J : TestJob W X) (J' : TestJob W X') : Prop where
  p : J.p = J'.p
  members : J.members = J'.members
  fresh : J.fresh = J'.fresh
  rec₀ : ∀ w fr fr', FrontBy r fr fr' → J.rec₀ w fr = J'.rec₀ w fr'
  rows₀ : ∀ w fr fr', FrontBy r fr fr' → J.rows₀ w fr = J'.rows₀ w fr'
  trees₀ : ∀ w fr fr', FrontBy r fr fr' → J.trees₀ w fr = J'.trees₀ w fr'

/-- The same job on words at two types of the passed-on value. -/
structure RunAlike (r : X → X' → Prop) (R : RunJob W X) (R' : RunJob W X') : Prop where
  p : R.p = R'.p
  members : R.members = R'.members
  fresh : R.fresh = R'.fresh
  trees : R.trees = R'.trees
  rec₀ : ∀ w fr fr', FrontBy r fr fr' → R.rec₀ w fr = R'.rec₀ w fr'
  rows : ∀ w fr fr', FrontBy r fr fr' → R.rows w fr = R'.rows w fr'

/-- A front at X' as a front at X. -/
def frontVia (g : X' → X) (fr : Front X') : Front X := ⟨fr.heard, g fr.own, fr.seen⟩

/-- The job at another type of the passed-on value: it reads that value through g. -/
def _root_.ProofFile.Honest.K12.TestJob.reOwn (g : X' → X) (J : TestJob W X) : TestJob W X' :=
  { p := J.p, members := J.members, fresh := J.fresh
    rec₀ := fun w fr => J.rec₀ w (frontVia g fr)
    rows₀ := fun w fr => J.rows₀ w (frontVia g fr)
    trees₀ := fun w fr => J.trees₀ w (frontVia g fr) }

/-- The job on words at another type of the passed-on value: it reads that value through g. -/
def RunJob.reOwn (g : X' → X) (R : RunJob W X) : RunJob W X' :=
  { p := R.p, members := R.members, fresh := R.fresh, trees := R.trees
    rec₀ := fun w fr => R.rec₀ w (frontVia g fr)
    rows := fun w fr => R.rows w (frontVia g fr) }

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.FrontBy
#print axioms ProofFile.Honest.K12.Light.JobAlike
#print axioms ProofFile.Honest.K12.Light.RunAlike
#print axioms ProofFile.Honest.K12.Light.frontVia
#print axioms ProofFile.Honest.K12.TestJob.reOwn
#print axioms ProofFile.Honest.K12.Light.RunJob.reOwn
