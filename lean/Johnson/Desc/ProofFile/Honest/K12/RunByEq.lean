-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunByEq.lean: proof of `Spec.runBy_eq` (RunBySpecTop.lean). For
every job, prover's input, random values and sampled challenges: if the stages pass `StagesOk`
(RunBy.lean), the rounds, the trees (as functions on all positions) and the opened columns of
`runBy` (RunBy.lean) at the input `RunIn.ofTest` (RunOf.lean) are those of the reference definition
`testAll` (Test.lean).

  `own_col`, `first_tab`   proofs of `Spec.own_col` and `Spec.first_tab`
  `stagesBy_eq`   proof of `Spec.stagesBy_eq`
  `runBy_eq`     the statement, at `Seams.lib`
  `runBy_halving_eq`   the same at `Seams.halving` (Halve.lean)

By what. The two implications `stagesBy_of` (RunByAll.lean) and `runBy_of` (RunByTop.lean), applied
to the lemmas' proofs, each in its own file (see RunBySpec.lean's head).

Limits.
- One hypothesis: `StagesOk`, a Bool on the list of stages, which is public. It is proved at literal
  parameter sets (RunBySpecAt.lean) and at every p whose block `proximityTestKind X p` passes its test on the plan
  (`stagesOk_of_planOk`, StagesOfPlan.lean). That a job's p is such a p is for whoever applies the
  equation to show.
- Of the five clauses of `switchFitB` the proofs take out the first four (`nx_stage`,
  RunByNext.lean; `okFrom_cons`, RunByTies.lean; `pow2B_of_fit`, `switchFitB_pows`, RunByAll.lean).
  By their text none uses the fifth, Z.a ≤ C.a: `StagesOk` asks one clause more than this proof
  needs.
- Where `testAll`'s output is unusable (a state on entry that holds no claim, a `decide`
  function that rejects, a sampled factor that is 0) so is `runBy`'s, in the same way. The warnings
  (`RunOut.no`) are not covered.
- The input `RunIn.ofTest` (RunOf.lean) is made of the job's own functions. The first stage's rows
  are the job's, evaluated over the field and encoded. The trees that hold them, and the state that
  the test is entered with, are the terms that `testAll` uses too: so for the columns opened at the
  first switch the equation compares a term with itself. For first rows and trees computed on words:
  `runJob_eq` (RunJobLaw.lean).
- Two definitions give the same words. Nothing follows on what a verifier decides. Nothing on
  completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunByTop
import Johnson.Desc.ProofFile.Honest.K12.RunByAll
import Johnson.Desc.ProofFile.Honest.K12.RunByDense
import Johnson.Desc.ProofFile.Honest.K12.RunByFold
import Johnson.Desc.ProofFile.Honest.K12.RunByNext
import Johnson.Desc.ProofFile.Honest.K12.RunByLast
import Johnson.Desc.ProofFile.Honest.K12.RunByAns
import Johnson.Desc.ProofFile.Honest.K12.RunByTies

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open Johnson.Prover.Link (wr)
open H2K.Pub (sgOf)

theorem own_col : Spec.own_col := fun s P p T => funext fun x => col_fresh s P p T x

theorem first_tab : Spec.first_tab := by
  intro W X J w fr C s rest h hr ok
  have hs0 : J.s₀ = s := by
    unfold TestJob.s₀
    rw [h]
    rfl
  have hh : s.h ≤ s.k := okFrom_le ok
  have hroom : 2 * s.k + 1 ≤ s.h + s.Z.l := okFrom_room ok (by
    cases rest with
    | nil => exact absurd rfl hr
    | cons _ _ => rfl)
  have H := (tiesBy_of s rest C ok).2 hr
  have hW : (coinsOf (s :: rest) C.hide C.rest).W (sgOf s) 0 =
      hideAt ((sgOf s).h + (sgOf s).g) C.hide := by
    simp only [coinsOf, if_true]
  refine ⟨rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show (ridersBy .two (sortedOf (s :: rest) C) 1 s false).1 =
      (List.range (2 ^ s.h)).map fun b => wr s.Z.l ((J.first w fr C).fM b)
    rw [ride_fresh (sortedOf (s :: rest) C) 1 s _ hh hroom (H.1.trans hW) H.2]
    unfold TestJob.first
    rw [hs0]
  · show (ridersBy .two (sortedOf (s :: rest) C) 1 s false).2 =
      (List.range (2 ^ s.h)).map fun b => wr s.Z.r ((J.first w fr C).fT b)
    rw [nx_riders_mid]
    rfl

theorem stagesBy_eq : Spec.stagesBy_eq :=
  stagesBy_of denseBy_reads foldBy_eq nextBy_tab colBy_eq ansBy_eq lastBy_eq

/-- Where the stages pass `StagesOk`, `runBy` at `Seams.lib` and `RunIn.ofTest` gives the rounds,
trees and opened columns of `testAll`. The warnings are left out. -/
theorem runBy_eq : Spec.runBy_eq := runBy_of stagesBy_eq own_col tiesBy_of first_tab

/-- The same at `Seams.halving`. -/
theorem runBy_halving_eq (W X : Type) (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins)
    (D : ℕ → Fmt.Drawn) (ok : StagesOk J.p.nums.stages = true) :
    (runBy Seams.halving (RunIn.ofTest J w fr C) D).toB = testAll J w fr C D := by
  rw [halving_rounds]
  exact runBy_eq W X J w fr C D ok

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.own_col
#print axioms ProofFile.Honest.K12.Light.first_tab
#print axioms ProofFile.Honest.K12.Light.stagesBy_eq
#print axioms ProofFile.Honest.K12.Light.runBy_eq
#print axioms ProofFile.Honest.K12.Light.runBy_halving_eq
