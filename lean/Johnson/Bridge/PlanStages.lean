-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Bridge/PlanStages.lean: the stages of all proximity tests of a key file, an entry file and a
proof file AS FUNCTIONS OF THE PLANNER's RECORDS, and one test on these records whose yes gives, at
every such stage, what Johnson/Bridge/FoldPriced.lean and Johnson/Bridge/BaseAtWritten.lean say of
one place. No numeral of a plan is written here.

This file rests on Cb/Bridge/CodeListRSProved.lean, and so on the files under ThirdParty/:
files adapted from ArkLib and
Mathlib (lean/LIMITS.md, L15).
Like the files of Cb/Bridge/, this file was written by AI systems that had seen ArkLib's source
(https://github.com/Verified-zkEVM/ArkLib, a copy marked as
commit 2817d8c7d2f28d706b17f8de0f885880d0b2eb13; Copyright ArkLib Contributors, Apache-2.0), so it
does not count as written independently of it. It takes no text from ArkLib or from ThirdParty/ and
follows no file of theirs.

Definitions with code, and two statements that follow from Johnson/Bridge/BrOf.lean.

Main names:
  `placeOf σ y`: a planner's stage as (stage, radius), by `stageOf` and `radiusOf`
    (Johnson/Top/H/StageJ.lean).
  `foldedOf σ st`, `lastOf σ st`: of a test's list of stages: all but the last, and the last.
  `keyTests Z`, `proofTests Z`: the key file's and the proof file's four tests' lists of stages.
  `linkFolds z`: the groups of a proof file's links as they are closed: `framesFrom`
    (OnBytes/Plan/ReqFrames.lean), field `closed`, at the records that have a link.
  `planFolds Z`: every stage that is folded, in the order: the key file's proof of the ranges,
    folded row, Omega, own test; the entry file's test; the proof file's links; its last test behind
    the links, folded row, Omega, own test.
  `baseWorks M`: the bits of work of the plans' rounds of the name «BASE», in the chains' order: the
    proof file's three chains, the key file's, the entry file's.
  `lastStages Z`, `planLasts M`: the nine last stages, in that order; each with the bits of work of
    the round «BASE» of the same number.
  `wholeB M`: each of the nine tests has a stage; there are as many rounds «BASE» as last stages;
    every link of the request has its record.
  `planStagesB M`: THE TEST: `wholeB`; `foldsB` at `planFolds`; `lastsB` at `planLasts`.
  `planStagesB_folds`, `planStagesB_lasts`: its yes gives `FoldedPlace.Paid` at every folded stage
    and `LastPlace.Paid` at every last stage of these records. No hypothesis on codes.

Limits: `foldsB` and `lastsB` say yes at an empty list: `wholeB` is what keeps a record without
stages from passing; that a request has a link at all is not asked. `wholeB`'s third clause holds of
every request, by reading (`reqGroups` makes one group more than there are links): it has never said
no. THE TEST LOOKS AT EACH STAGE BY ITSELF: the code switches between a test's stages (and whether
neighbours fit), the rounds «LOC» and «SEND seed» and the batching are not tested here: at records
in which a test's last stage stood twice the test still said yes. WHICH ROUND «BASE» BELONGS TO
WHICH TEST IS BY ORDER ALONE: nothing here ties a plan's round to a test's last stage but its number
in the row. That the records are those of a file's public files is asked where they are made
(`Params.configure`; `Model.Verify.planned`). That the rounds of a plan are the rounds of these
stages, and that a verifier's description runs these stages, is not said here. `stageOf` does not
read a group's number of slots: at a link's group where that number is not 1 the stage is not the
whole of the group. The test has been EVALUATED at stored sets of public files, in a file that does
not ship; no theorem says that it says yes at any plan. No sum over rounds. Nothing on a verifier or
a file.

-/
import Johnson.Bridge.BrOf
import OnBytes.Plan.ReqFrames

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Bridge
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Plan Johnson.Top.H

/-- A planner's stage as (stage, radius). -/
def placeOf (σ : Setting) (y : StageSize) : Sg × ℕ := (stageOf y.g y.t, radiusOf σ y.g)

/-- The stages of a test that are folded: all but the last. -/
def foldedOf (σ : Setting) (st : List StageSize) : List (Sg × ℕ) := st.dropLast.map (placeOf σ)

/-- The last stage of a test. -/
def lastOf (σ : Setting) (st : List StageSize) : List (Sg × ℕ) :=
  st.getLast?.toList.map (placeOf σ)

/-- The groups of a proof file's links, as they are closed. -/
def linkFolds (z : ProofSized) : List (Sg × ℕ) :=
  ((framesFrom z 0 (reqGroups z.request).toList z.request.link [] z.link.group).filter
    fun n => n.link.isSome).map fun n => (stageOf n.closed z.link.t, radiusOf z.set n.closed)

/-- The key file's four tests' lists of stages. -/
def keyTests (Z : Params.Sized) : List (List StageSize) :=
  [Z.key.ranges.test.stages, Z.key.once.folded.stages, Z.key.once.omega.stages,
    Z.key.once.own.stages]

/-- The proof file's four tests' lists of stages. -/
def proofTests (Z : Params.Sized) : List (List StageSize) :=
  [Z.proof.last.stages, Z.proof.batch.folded.stages, Z.proof.batch.omega.stages,
    Z.proof.batch.own.stages]

/-- **Every stage that is folded.** -/
def planFolds (Z : Params.Sized) : List (Sg × ℕ) :=
  (keyTests Z).flatMap (foldedOf Z.key.set) ++ foldedOf Z.set Z.link.linked.stages ++
    linkFolds Z.proof ++ (proofTests Z).flatMap (foldedOf Z.proof.set)

/-- The bits of work of the plans' rounds «BASE», in the chains' order. -/
def baseWorks (M : Configured) : List ℕ :=
  (M.proof ++ M.key ++ [M.entry]).flatMap fun P =>
    (P.plan.entries.filter fun e => e.name == "BASE").map (·.work)

/-- The nine last stages, in the order of the rounds «BASE». -/
def lastStages (Z : Params.Sized) : List (Sg × ℕ) :=
  (proofTests Z).flatMap (lastOf Z.proof.set) ++ (keyTests Z).flatMap (lastOf Z.key.set) ++
    lastOf Z.set Z.link.linked.stages

/-- **Every last stage**, with the bits of work of the round «BASE» of the same number. -/
def planLasts (M : Configured) : List (Sg × ℕ × ℕ) :=
  (lastStages M.sized).zipWith (fun p w => (p.1, p.2, w)) (baseWorks M)

/-- So that, by reading, nothing falls away in silence: each of the nine tests has a stage; there
are as many rounds «BASE» as last stages; every link of the request has its record, so its group is
among the folds. -/
def wholeB (M : Configured) : Bool :=
  ((keyTests M.sized ++ proofTests M.sized ++ [M.sized.link.linked.stages]).all fun st =>
      !st.isEmpty) &&
    Nat.beq (baseWorks M).length (lastStages M.sized).length &&
    Nat.beq (linkFolds M.sized.proof).length M.sized.proof.request.link.length

/-- **The test on the planner's records.** -/
def planStagesB (M : Configured) : Bool :=
  wholeB M && foldsB (planFolds M.sized) && lastsB (planLasts M)

/-- **A yes of the test: every folded stage of the records is paid.** No hypothesis on codes. -/
theorem planStagesB_folds {M : Configured} (h : planStagesB M = true) :
    ∀ p ∈ planFolds M.sized, (FoldedPlace.of p.1 p.2).Paid :=
  foldsB_paid (Bool.and_eq_true_iff.1 (Bool.and_eq_true_iff.1 h).1).2

/-- **A yes of the test: every last stage of the records is paid.** No hypothesis on codes. -/
theorem planStagesB_lasts {M : Configured} (h : planStagesB M = true) :
    ∀ p ∈ planLasts M, (LastPlace.of p.1 p.2.1 p.2.2).Paid :=
  lastsB_paid (Bool.and_eq_true_iff.1 h).2

end Johnson.Bridge

#print axioms Johnson.Bridge.planStagesB_folds
#print axioms Johnson.Bridge.planStagesB_lasts
