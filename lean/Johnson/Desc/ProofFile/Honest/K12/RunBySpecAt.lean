-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/RunBySpecAt.lean: `StagesOk` (RunBy.lean), the hypothesis of
`runBy_eq` (RunByEq.lean), is true at eleven parameter sets of a proximity test: the eight of the
two stored example proofs (Johnson/Desc/K12/Law/PlacesSmall.lean, PlacesFull.lean) and the three of
the larger key file (PlacesKeyFull.lean). Eleven theorems, `stagesOk_piU` to `stagesOk_piKWFull`,
each checked by Lean's kernel by evaluation. At the key file's test on the ranges it is not shown
here. And `#guard` lines that show that `StagesOk` can be false. It imports no Mathlib.

Negative tests, at `piU`'s stages with one clause broken each (`bent`): a stage's h above its k; a
mask row too short for the coefficients; the last stage's k; its h; each of the five clauses of
`switchFitB`; one stage alone; none. The changes are chosen so that the other clauses hold; that
they do is not tested here.

Limits. The eleven parameter sets are literals, generated from a run's printout (see the heads of
their files). No theorem says that a job's parameters equal one of them. Whoever applies `runBy_eq`
to a job has to prove `StagesOk` at that job's own stages; `stagesOk_of_planOk` (StagesOfPlan.lean)
gives it where the block at the job's parameters passes its test on the plan.

Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.RunBy
import Johnson.Desc.K12.Law.PlacesSmall
import Johnson.Desc.K12.Law.PlacesFull
import Johnson.Desc.K12.Law.PlacesKeyFull

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light.SpecAt
open H2K.Member
open Fmt.M1 (Stage)

theorem stagesOk_piU : StagesOk piU.nums.stages = true := by decide +kernel
theorem stagesOk_piO : StagesOk piO.nums.stages = true := by decide +kernel
theorem stagesOk_piW : StagesOk piW.nums.stages = true := by decide +kernel
theorem stagesOk_piL : StagesOk piL.nums.stages = true := by decide +kernel
theorem stagesOk_piUFull : StagesOk piUFull.nums.stages = true := by decide +kernel
theorem stagesOk_piOFull : StagesOk piOFull.nums.stages = true := by decide +kernel
theorem stagesOk_piWFull : StagesOk piWFull.nums.stages = true := by decide +kernel
theorem stagesOk_piLFull : StagesOk piLFull.nums.stages = true := by decide +kernel
theorem stagesOk_piKUFull : StagesOk piKUFull.nums.stages = true := by decide +kernel
theorem stagesOk_piKOFull : StagesOk piKOFull.nums.stages = true := by decide +kernel
theorem stagesOk_piKWFull : StagesOk piKWFull.nums.stages = true := by decide +kernel

/-- `piU`'s stages with f applied to stage i. -/
def bent (i : Nat) (f : Stage → Stage) : List Stage := piU.nums.stages.modify i f

#guard piU.nums.stages.length == 3 && StagesOk (bent 0 id)
#guard !StagesOk (bent 1 fun s => { s with h := s.k + 1 })
#guard !StagesOk (bent 0 fun s => { s with Z := { s.Z with l := 8 } })
-- two rows of half the length at the last stage, so that switchFitB still holds
#guard !StagesOk (bent 2 fun s => { s with k := 1, C := { s.C with l := s.C.l / 2 } })
-- two mask rows at the last stage; switchFitB still holds
#guard !StagesOk (bent 2 fun s => { s with h := 1 })
-- the five clauses of switchFitB, at the first switch: the tables' entries; the mask table's room;
-- a main row's length three times a power of two, at all stages; a mask row's length; the depths
#guard !StagesOk (bent 1 fun s => { s with k := s.k + 1 })
#guard !StagesOk (bent 0 fun s => { s with C := { s.C with r := 1000 } })
#guard !StagesOk (piU.nums.stages.map fun s => { s with C := { s.C with l := 3 * s.C.l } })
#guard !StagesOk (bent 1 fun s => { s with Z := { s.Z with l := 300 } })
#guard !StagesOk (bent 0 fun s => { s with Z := { s.Z with a := s.C.a + 1 } })
#guard !StagesOk (piU.nums.stages.take 1) && !StagesOk []

end ProofFile.Honest.K12.Light.SpecAt

#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piU
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piO
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piW
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piL
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piUFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piOFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piWFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piLFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piKUFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piKOFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.stagesOk_piKWFull
#print axioms ProofFile.Honest.K12.Light.SpecAt.bent
