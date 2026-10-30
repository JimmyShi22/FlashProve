-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/ExactFirstAtU.lean: `exact_first` (Sim/ExactFirst.lean) at a
job that is named: the job of the test on G_u of the small made-up shared chain,
`(jobAtU ⟨P3, 0⟩ p door weights rand u?).toRun.toTest` (JobShared.lean, SharedSmall.lean), for every
state function `door`, both readers and every vector. And two small facts on the job of any
`ManyJob` (RunMany.lean) that statements of this folder ask as hypotheses.

What is stated. The frame's sentence `ExactMember` (Johnson/Desc/ProofFile/Honest/Small/Field.lean:
the text of the field `exact` of `Good`, Honest/Side.lean, at one member) at the test's first member
(`firstMember`, Sim/Row.lean), for every `On`, every `bud` and every side σ, under two hypotheses on
the simulators' job: it stands at the place p, and it says that the fresh table came earlier. It is
an equation between two laws: of what the first part shows, played alone over the 2 k + 1 values
that it spends, and of what `firstSim` (Sim/Sims.lean) yields over 2 k + 1 values of its own.

  `formPub_small`, `enough_small`, `tables_small`   the three hypotheses of `FirstPub` on the
                 place's numbers, at p: evaluated by Lean's kernel
  `firstPub_atU`   `FirstPub` at the job
  `exact_first_atU`   the statement
  `rowsRead_many`   `rowsRead` (Sim/Spec.lean) holds at the job of every `ManyJob`
  `rowsMu_many`    the hypothesis hrows of `onFree_of_lent` (Sim/OnFromLent.lean) and
                 `agree_of_ties` (AgreeBook.lean) holds there too

By what. `exact_first`, called. `many_rows` (LentLaw3.lean), called.

Limits.
- It is an instance of a theorem, not a member of the sentence: no side, no state of a run, no front
  and no challenges are written out here at which the sentence's own hypotheses hold together
  (`meets_head_U`, Sim/MeetsAtHead.lean, has them at the full size, under the library's head, at
  written letters: not at this small chain).
- It stands at a state on entry that is made of the plan's public part, not shown to be the
  verifier's: `door` is a parameter, and what the first fold shows is computed from it. The public
  checks on these jobs (FitShared.lean and the files that it names) are no hypotheses here.
- It is shown at no job that is played; nor are these checks.
- It speaks of the parts of `proverSideOfProximityTest` (Parts.lean), not of the guarded halves (PartsByJob.lean).
- What the parts send is `testAll` (Johnson/Desc/ProofFile/Honest/K12/Test.lean), cut into parts in
  Parts.lean, over the random values of Coins.lean, both beside it. How far `testAll` is tied to the
  library's `bodyAll` is said in Test.lean's limits.
- What Sim/ExactFirst.lean says of its own worth holds here: the sentence samples the spent values
  anew and looks at this part's rounds alone. By the book the same 2 k + 1 values are meant to stand
  elsewhere in a run: in the fresh table in its sender's tree, and in what the second part carries.
  Nothing here joins these.
- One small made-up place. Nothing on the second member, nor where the first fold sends its own
  table.
- No file of this folder states a security property by itself. Nothing on completeness, soundness or
  hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.ExactFirst
import Johnson.Desc.ProofFile.Honest.K12.Sim.Spec
import Johnson.Desc.ProofFile.Honest.K12.SharedSmall
import Johnson.Desc.ProofFile.Honest.K12.JobShared
import Johnson.Desc.ProofFile.Honest.K12.LentLaw3

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (T12)
open Johnson.Prover.Link (μOf)
open H2K.Pub (sgOf)
open H2K.JointK (laidOf)
open ProofFile.Honest.Small (ExactMember)
open ProofFile.Honest.K12.Light.SharedSmall (P3 p)

/-! ## 1 The place's numbers -/

theorem formPub_small : formPubB p = true := by decide +kernel

theorem enough_small : firstLen p.nums.stages ≤ (laidOf p).length := by decide +kernel

/-- Each declared oracle message has the depth and the width of the tree that the text sends. -/
theorem tables_small {W X : Type} (J : TestJob W X) (hJ : J.p = p)
    (hfr : J.fresh.isNone = false) : tablesFitB J = true := by
  unfold tablesFitB depthAt
  rw [hJ, hfr]
  decide +kernel

/-! ## 2 At the job -/

theorem firstPub_atU {W X Pb : Type} (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb)
    (hp : Js.p = p) (ho : Js.own = false) :
    FirstPub (jobAtU ⟨P3, 0⟩ p door weights rand u?).toRun.toTest Js :=
  ⟨hp, ho, formPub_small, enough_small, tables_small _ rfl rfl⟩

/-- The frame's sentence at the first member of the job, for every `On`, `bud` and side. -/
theorem exact_first_atU {S Cl V W X Pb : Type} (φ : Face V W Pb) (σ : Side S Cl V W X Pb)
    (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (u? : Option (W → Front X → ℕ → OnBytes.E)) (Js : SimJob Pb) (chain firstTree : ℕ)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop) (hp : Js.p = p)
    (ho : Js.own = false) :
    ExactMember φ σ chain firstTree On bud
      (firstMember (jobAtU ⟨P3, 0⟩ p door weights rand u?).toRun.toTest Js) :=
  exact_first φ σ _ Js chain firstTree On bud rfl (firstPub_atU door weights rand u? Js hp ho)

/-! ## 3 The job's rows -/

theorem rowsRead_many {W X : Type} (A : ManyJob W X) : rowsRead A.toRun.toTest :=
  fun w fr mem mem' h => many_rows A w fr mem mem' fun t ht => h t (by
    show t < (A.mems.map (·.sent)).length
    rw [List.length_map]
    exact ht)

theorem rowsMu_many {W X : Type} (A : ManyJob W X) (s : Fmt.M1.Stage) (w : W) (fr : Front X)
    (mem mem' : ℕ → Stretch) (h : ∀ t, t < A.toRun.toTest.members.length → mem t = mem' t) :
    μOf (sgOf s) (A.toRun.toTest.rows₀ w fr mem) = μOf (sgOf s) (A.toRun.toTest.rows₀ w fr mem') :=
  congrArg (μOf (sgOf s)) (rowsRead_many A w fr mem mem' h)

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.formPub_small
#print axioms ProofFile.Honest.K12.Light.enough_small
#print axioms ProofFile.Honest.K12.Light.tables_small
#print axioms ProofFile.Honest.K12.Light.firstPub_atU
#print axioms ProofFile.Honest.K12.Light.exact_first_atU
#print axioms ProofFile.Honest.K12.Light.rowsRead_many
#print axioms ProofFile.Honest.K12.Light.rowsMu_many
