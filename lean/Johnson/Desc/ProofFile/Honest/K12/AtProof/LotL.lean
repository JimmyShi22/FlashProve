-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/LotL.lean: the honest side of the first chain's lot of the
kind K12 ("the proximity test at F:2 (K12)", Johnson/Desc/ProofFile/Lot/K12.lean), in the form
`HLot` (Johnson/Desc/ProofFile/Honest/Frame.lean). Definitions with code; no theorem.

  `lotL`    the lot: by the door `lotOf` (Doors.lean in this folder), the job `jobL` (JobL.lean in
            this folder) at the place's numbers as the lot of that name lays them
            (`H2U.p12OfMade`, Johnson/Desc/K12/AtPlan.lean) and at the finish of the code switch
            (`finishAt`). NO HALF where the plan has no such finish, and none where the public
            test `fitsL` (JobL.lean) says no: there the job's text might read a random value at
            another place than the sender laid it
  `bareL`   the bare job at the same members and the same word on the fresh table: a stand-in of
            public numbers, for a test of the laying

THE LETTERS. The state on entry (`door`) is an argument of the lot and is filled by nothing here:
how a prover's side can make the verifier's state in front of this test is not settled by this file.
So are the main rows' data, the readers and the closing, which `jobL` hands to the sender's own
text. Each is a function of the public part and the ground, as the halves are.

A BARE HALF IS NOT TO BE LAID INTO A FILLING THAT IS PLAYED, COUNTED OR OF RECORD (Doors.lean).

WHAT IS NO LETTER. The place's numbers: the term of the library's own lot. The members and the word
on the fresh table: the sender's own reckoning. The rows and the trees: the sender's own text and
the library's, at three of the letters.

Limits.
- AT THE FIRST CHAIN's TEST THE ROWS ARE NOT ALL PLAIN, BY AN EVALUATION: at the verifier's state
  there, at one honest run, two marks have been evaluated false: `takenPlainB`
  (Johnson/Desc/K12/Honest/Shape/TestFinishSix.lean: the rows that the test takes in at the group
  under test) and `stPlainB` (Johnson/Desc/Ground/Shape/Marks.lean: every open row and every sample
  row of the whole statement). An evaluation, no theorem. `stPlainB` gives `takenPlainB`
  (`taken_of_plain`, TestFinishSix.lean). The library proves `DenseRow` of the rows taken in
  (`taken_dense_entered`, Johnson/AtFull/Shape/TakenRowsDense.lean). The second member's condition
  `onFreeT` (Sim/TreesExact.lean) asks `stPlainB` of the job's own state on entry
  (`ShapeAsks.plainRows`, PlanB.lean): at a job whose state on entry is a state at which that mark
  is false the condition fails, and the sentence under it says nothing. That a job's state on entry
  is the verifier's is shown of no job. The files whose names end in Dense.lean, beside their
  sources, ask `DenseRow` of the rows taken in at the group under test instead (`onFreeTD`,
  `exact_free_trees_dense`, Sim/TreesExactDense.lean). They do not reach this place yet.
- THE LOT GIVES NO HALF WHERE `fitsL` SAYS NO, and is silent about it: the frame's lists of what has
  no half (`lacking`, `OnlineProverWithDescription.stillIdle`) show the place.
- WHERE THE SENDER's TEXT REFUSES, THE JOB LAYS ROWS OF ZEROS WITHOUT A WARNING (`rowsL`,
  JobL.lean), and the tree's message is the zero message (`treesL`): that it returns is a premise
  of whoever states a law on this lot. WANTED BESIDE IT, BY NAME, WHEREVER `jobL` IS LAID: the
  closing's refusals hang on public fields alone. Nothing here shows it.
- Nothing compares a letter with a description, with a run or with another letter.
- All other limits of JobL.lean stand. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Doors
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobL

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc.K12 (P12 T12)

variable {V W₀ Rc Xi Tr X : Type}

/-- **The lot.** door, D, readers, closing: letters. -/
def lotL (door : Pub → Ground → Local W₀ Rc Xi Tr → Front X → T12)
    (D : Pub → Ground → RowDataOf Xi) (readers : Pub → Ground → Local W₀ Rc Xi Tr → Readers)
    (closing : Pub → Ground → K2.Closing) : HLot V (Local W₀ Rc Xi Tr) X :=
  lotOf fun Z G => (finishAt Z G).bind fun p =>
    if fitsL (H2U.p12OfMade Z.made) p then
      some (jobL (H2U.p12OfMade Z.made) (door Z G) (D Z G) (readers Z G) (closing Z G) p)
    else none

/-- **The bare job at the lot's members.** -/
def bareL {W : Type} (q : P12) (p : K2.SwitchPlace) : TestJob W X :=
  bareJob q (membersL p) (freshL p)

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.lotL
#print axioms ProofFile.Honest.K12.AtProof.bareL
