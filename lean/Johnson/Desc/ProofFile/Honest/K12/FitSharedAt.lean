-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/FitSharedAt.lean: the public checks on the jobs of the shared
chain's two proximity tests are true at the small made-up chain of SharedSmall.lean (`P3`, `p`,
`pO`), as theorems that Lean's kernel evaluates; and `ManyJob.layFits` (RunMany.lean) as a check on
public data alone, on the job's side too. It imports Mathlib.

  `stagesOk_p`, `stagesOk_pO`   `StagesOk` (RunBy.lean) at the two tests' stages
  `sharedFitsU_small`, `sharedFitsOmega_small`   the members' code sizes (FitShared.lean)
  `freshFitsU_small`, `freshFitsOmega_small`   the first fresh table's numbers (FitShared.lean)
  `rowsFit_small_U`, `rowsFit_small_Omega`   so `RunJob.rowsFit` is true at the two jobs, for every
                 state function, every pair of readers, every vector passed in, every input,
                 whatever precedes the test, and all random values, without hypothesis
  `freshFits_small_U`, `freshFits_small_Omega`   and `TestJob.freshFits` (Test.lean) is true there
  `pubJob`, `layFits_pubJob`   `layFits` reads of a job its parameters and its members' shapes
                 alone: it has the same value at a job that is built from these
  `shapesAtU`, `shapesAtOmega`, `shapes_atU`, `shapes_atOmega`   the members' shapes at `jobAtU` and
                 `jobAtOmega` do not depend on the state function, the readers or the vector
  `pubU`, `pubO`   the public parts (`pubOf`, FitShared.lean) of the two states on entry, written
                 out by hand
  `layFits_pubU`, `layFits_pubO`   `layFitsPub` is true at them, at the jobs' parameters and shapes
  `layFits_small_U`, `layFits_small_Omega`   at every state whose public part is `pubU` (`pubO`),
                 `layFits` is true at the job, for every state function, every pair of readers and
                 every vector passed in
  `pub_door`, `layFits_door`, `layFits_job_all`   JobSharedToy.lean's state on entry to the test on
                 G_u has the public part `pubU`, so `layFits` is true there; the same said of that
                 job's state function, which is constant
`sendingsFit` at `P3` is proved in SharedSmall.lean (`sendingsFit_P3`).

So, of the six public checks on a job of this kind, at this example: `StagesOk`, `rowsFit` for all
arguments, `sendingsFit` and the fresh table's numbers are theorems at both tests; `OnBytes.linOk`
is a `#guard` (SharedSmall.lean). `layFits` is a theorem at every state with the written public
part, and at JobSharedToy.lean's state on entry to the test on G_u; at its state on entry to the
test on G_omega it is a `#guard`.

By what. `decide +kernel` for the checks at written data, then the theorems of FitSharedLaw.lean.

Limits.
- One small made-up example; no stored proof's parameters.
- That JobSharedToy.lean's state on entry to the test on G_omega (`doorO`) has the public part
  `pubO` is a `#guard`, not a theorem. `decide` does not reduce there: `doorO` is computed from a
  whole run of `runBy` on random values that are field elements.
- That a job's state on entry has one public part for every input and whatever precedes the test is
  up to the caller (`layFits_all`, FitSharedLaw.lean, names that premise). JobSharedToy.lean's two
  jobs have a constant state function.
- The limits of FitShared.lean apply. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.FitSharedLaw
import Johnson.Desc.ProofFile.Honest.K12.JobSharedToy

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K14 (SendPub sendPlace)

variable {W X : Type}

/-! ## 1 What `layFits` reads of a job -/

/-- A job that holds parameters and members' shapes and nothing else: no rows, no tree, no state. -/
def pubJob (q : P12) (shapes : List MemShape) : ManyJob Unit Unit :=
  { p := q
    mems := shapes.map fun s =>
      { sent := (⟨sendPlace 0, 0⟩, 0, ⟨0, 0⟩), shape := s
        rows := fun _ _ _ => { M := [], Rh := [], W := [], Sg := [], P := [], Pi := [] } }
    fresh := none, rec₀ := fun _ _ => noState, trees := [] }

theorem layFits_pubJob (A : ManyJob W X) (t : T12) :
    A.layFits t = (pubJob A.p (A.mems.map (·.shape))).layFits t := by
  simp [ManyJob.layFits, pubJob, ManyJob.s₀, List.zipIdx_map, List.all_map, Function.comp_def]

/-- The members' shapes at `jobAtU`, taken from that job at arguments that hold nothing. -/
def shapesAtU (A : SendPub) (q : P12) : List MemShape :=
  (jobAtU A q (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩) (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩)
    none : ManyJob Unit Unit).mems.map (·.shape)

/-- The members' shapes at `jobAtOmega`, taken from that job at arguments that hold nothing. -/
def shapesAtOmega (A : SendPub) (q : P12) : List MemShape :=
  (jobAtOmega A q (fun _ _ => noState) (fun _ => ⟨fun _ _ => 0⟩)
    (fun _ => ⟨fun _ _ => 0, fun _ _ => 0⟩) none : ManyJob Unit Unit).mems.map (·.shape)

theorem shapes_atU (A : SendPub) (q : P12) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtU A q door weights rand u?).mems.map (·.shape) = shapesAtU A q := rfl

theorem shapes_atOmega (A : SendPub) (q : P12) (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtOmega A q door weights rand omega?).mems.map (·.shape) = shapesAtOmega A q := rfl

end ProofFile.Honest.K12.Light

namespace ProofFile.Honest.K12.Light.SharedSmall
open OnBytes (noId)
open VerifiableInference.Desc.K12 (T12)
open ProofFile.Honest.K12.Light.SharedToy (job jobO door doorO)

variable {W X : Type}

/-! ## 2 The checks on stages, rows and the first fresh table -/

theorem stagesOk_p : StagesOk p.nums.stages = true := by decide +kernel

theorem stagesOk_pO : StagesOk pO.nums.stages = true := by decide +kernel

theorem sharedFitsU_small : sharedFitsU ⟨P3, 0⟩ p = true := by decide +kernel

theorem sharedFitsOmega_small : sharedFitsOmega ⟨P3, 0⟩ pO = true := by decide +kernel

theorem freshFitsU_small : freshFitsU ⟨P3, 0⟩ p = true := by decide +kernel

theorem freshFitsOmega_small : freshFitsOmega pO = true := by decide +kernel

theorem rowsFit_small_U (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (u? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X) (mem : ℕ → Stretch) :
    (jobAtU ⟨P3, 0⟩ p door weights rand u?).toRun.rowsFit w fr mem = true :=
  rowsFit_atU _ _ sharedFitsU_small door weights rand u? w fr mem

theorem rowsFit_small_Omega (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (w : W) (fr : Front X)
    (mem : ℕ → Stretch) :
    (jobAtOmega ⟨P3, 0⟩ pO door weights rand omega?).toRun.rowsFit w fr mem = true :=
  rowsFit_atOmega _ _ sharedFitsOmega_small door weights rand omega? w fr mem

theorem freshFits_small_U (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (u? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtU ⟨P3, 0⟩ p door weights rand u?).toRun.toTest.freshFits = true :=
  freshFits_atU _ _ freshFitsU_small door weights rand u?

theorem freshFits_small_Omega (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) :
    (jobAtOmega ⟨P3, 0⟩ pO door weights rand omega?).toRun.toTest.freshFits = true :=
  freshFits_atOmega ⟨P3, 0⟩ _ freshFitsOmega_small door weights rand omega?

/-! ## 3 `layFits` -/

/-- The public part of the state on entry to the test on G_u: two groups, four oracle messages (o_u,
the first fresh table, o_omega, o_sp); group 0 is under test. -/
def pubU : PubState × ℕ :=
  (⟨codes2, #[⟨0, 0, #[0, 3], #[false, false]⟩, ⟨1, 0, #[2, 3], #[false, false]⟩],
    #[⟨0, 2, 3, 0, noId, 1⟩, ⟨noId, 0, 1, 1, 0, 0⟩, ⟨1, 1, 3, 0, noId, 1⟩, ⟨noId, 0, 3, 1, 0, 1⟩]⟩,
    0)

/-- The public part of the state on entry to the test on G_omega: the two groups and four oracle
messages more that the test on G_u has made; group 1 is under test. -/
def pubO : PubState × ℕ :=
  (⟨codes2, #[⟨0, 0, #[0, 3], #[false, false]⟩, ⟨1, 0, #[2, 3], #[false, false]⟩,
      ⟨2, 1, #[4], #[false]⟩, ⟨3, 2, #[6], #[false]⟩],
    #[⟨0, 2, 3, 0, noId, 1⟩, ⟨noId, 0, 1, 1, 0, 0⟩, ⟨1, 1, 3, 0, noId, 1⟩, ⟨noId, 0, 3, 1, 0, 1⟩,
      ⟨2, 2, 3, 2, 1, 1⟩, ⟨noId, 0, 1, 2, 1, 0⟩, ⟨3, 1, 3, 1, 2, 1⟩, ⟨3, 1, 3, 1, 2, 0⟩]⟩, 1)

theorem layFits_pubU : layFitsPub (pubJob p (shapesAtU ⟨P3, 0⟩ p)) pubU = true := by decide +kernel

theorem layFits_pubO : layFitsPub (pubJob pO (shapesAtOmega ⟨P3, 0⟩ pO)) pubO = true := by
  decide +kernel

theorem layFits_small_U (door : W → Front X → T12) (weights : W → Weights) (rand : W → TableRand)
    (u? : Option (W → Front X → ℕ → OnBytes.E)) (t : T12) (h : pubOf t = pubU) :
    (jobAtU ⟨P3, 0⟩ p door weights rand u?).layFits t = true := by
  rw [layFits_pubJob, shapes_atU, layFits_pub, h]
  exact layFits_pubU

theorem layFits_small_Omega (door : W → Front X → T12) (weights : W → Weights)
    (rand : W → TableRand) (omega? : Option (W → Front X → ℕ → OnBytes.E)) (t : T12)
    (h : pubOf t = pubO) : (jobAtOmega ⟨P3, 0⟩ pO door weights rand omega?).layFits t = true := by
  rw [layFits_pubJob, shapes_atOmega, layFits_pub, h]
  exact layFits_pubO

theorem pub_door : pubOf door = pubU := by decide +kernel

theorem layFits_door : (job {}).layFits door = true := layFits_small_U _ _ _ _ door pub_door

/-- At JobSharedToy.lean's job, whose state function is constant: for every input and whatever
precedes the test. -/
theorem layFits_job_all (w : Unit) (fr : Front Unit) :
    (job {}).layFits ((job {}).rec₀ w fr) = true := by
  refine layFits_all (job {}) pubU (fun _ _ => pub_door) ?_ w fr
  rw [← pub_door, ← layFits_pub]
  exact layFits_door

-- the state on entry to the test on G_omega: evaluated, not proved (see the limits)
#guard pubOf doorO == pubO
#guard (jobO 0).layFits doorO
-- the two written public parts differ, and each check is false at the other's
#guard pubOf doorO != pubU && pubOf door != pubO
#guard !layFitsPub (pubJob p (shapesAtU ⟨P3, 0⟩ p)) pubO &&
  !layFitsPub (pubJob pO (shapesAtOmega ⟨P3, 0⟩ pO)) pubU
-- with one more mask row in o_sp's shape the check is false
#guard !layFitsPub (pubJob p (shapesAtU ⟨P3, 0⟩ p))
  ({ pubU.1 with shapes := pubU.1.shapes.modify 3 fun s => { s with maskRows := 2 } }, 0)

end ProofFile.Honest.K12.Light.SharedSmall

#print axioms ProofFile.Honest.K12.Light.layFits_pubJob
#print axioms ProofFile.Honest.K12.Light.shapes_atU
#print axioms ProofFile.Honest.K12.Light.shapes_atOmega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.stagesOk_p
#print axioms ProofFile.Honest.K12.Light.SharedSmall.stagesOk_pO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.sharedFitsU_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.sharedFitsOmega_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.freshFitsU_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.freshFitsOmega_small
#print axioms ProofFile.Honest.K12.Light.SharedSmall.rowsFit_small_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.rowsFit_small_Omega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.freshFits_small_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.freshFits_small_Omega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_pubU
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_pubO
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_small_U
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_small_Omega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.pub_door
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_door
#print axioms ProofFile.Honest.K12.Light.SharedSmall.layFits_job_all
#print axioms ProofFile.Honest.K12.Light.pubJob
#print axioms ProofFile.Honest.K12.Light.shapesAtU
#print axioms ProofFile.Honest.K12.Light.shapesAtOmega
#print axioms ProofFile.Honest.K12.Light.SharedSmall.pubU
#print axioms ProofFile.Honest.K12.Light.SharedSmall.pubO
