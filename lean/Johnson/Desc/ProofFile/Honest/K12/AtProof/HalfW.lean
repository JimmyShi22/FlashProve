-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/AtProof/HalfW.lean: the job at the last chain's proximity test at
a public part, and its pair behind the guard: the twin at W of HalfU.lean. Definitions with code.

  `inOf`        what W's sending's job reads of the input: the instance and the readers
  `jobRealW`, `realW`   `jobW` (JobW.lean) at the public part's own numbers: the place's `four`; the
                 first opening's job `K1.firstJob`; W's sending's job at the data
                 `K13.wDataAt pile`; `sendPub`; the state on entry `doorW` (DoorLast.lean) at the
                 description handed
  `halfW`       the pair of parts at the test's place, behind the guard (FieldGuard.lean); no side
                 where the job is not made

What the job reads. Of the input: its instance, its readers (the witness, the index, the stored
tables' pads and encoding randomness), through `readers`, `weights` and `rand`; of the run's coins,
the group's stretches; of the front, what was heard, and the state on entry as below.

What may be said here on hiding, and no more
(a rule of use for whoever builds on this file;
no theorem):
«The state on entry reads the instance's public part, the rounds shown, and ALL columns opened in
front of this test, in the order of reading: the first chain's, the shared chain's, the last
chain's own. They are computed from the witness, the index, the stored tables' pads and encoding
randomness, AND THE RUN's COINS. Never a word on a simulator at this place without «given the
instance's public part, the rounds shown and all columns opened in front, in all three chains».
But for the stored tables' columns no one can hand a simulator these from outside: the simulators
of EVERY part in front must have made them: this test stands last, and its «given» is the whole
view in front. At a called part of the walk the field begins with the two earlier chains' views'
own columns (door_last_at_called); that what follows them are the last chain's view's is not
typed, and that each tree's budget counts them is typed by nobody.»

Limits.
- EIGHT LETTERS: `pile`, `readers`, `weights`, `rand`, `no`, S, the description Fd against Z, and
  `enter`. `n₁` is counted off Fd's own list. NOT TO BE LAID BEFORE EACH IS THE SENDER's OWN, BY rfl
  OR A LEMMA: nothing here holds them against `K1.wSide`'s and the first opening's letters: with two
  readers the test's rows are not the sender's.
- The pair stands behind the guard: at `opened = none` each of its moves errs: so under `run` and
  `midAt`, which hand none, it errs at its first round: a statement over these behind that round
  says nothing of such a prover. `midSharedAt` plays the shared chain alone and does not reach it.
- `doorW`'s default `idleT12` is silent; behind the guard only a refusal of its folds reaches it. It
  holds nothing: unlike the fall-backs at U and O, which are made of the plan's shape, no public
  test is said to hold at it.
- `halfW` asks no test on the shape: `askOf` reads `rowsOf`, and at a shape whose matrix's places
  run into the pads an entry of the matrix lies where a pad of the index committer is due
  (JobShared.lean), at Omega's member here as at O. Under the library's head the shape of the shared
  chain passes `LinShape.ok` (`linOk_at_head`, Honest/K14/SendingsAtFilling.lean, with `linOk_ok`),
  and that is the shape at which `askOf` reads here, where the shared chain's eight sub-protocols
  are made (`sendPub`, AtProof/Members.lean; `sendPub_at_head`, AtProof/HalfAtPure.lean). No one
  theorem joins these.
- Omega's message 0 is a member at O and again here: its tree is opened at two tests, main rows
  alone. BookPlan.lean frees a tree all of whose tenants say "sampled" from its clause `once`; whose
  budget counts both openings is not said.
- `memOfSending`'s last `none`: no vector is handed: Omega's rows are the sending's own data at
  `ask`.
- The guard tests the move's own Seen, the door reads the front's: the front that `moveAt` lays
  carries that field: `front_opened` (FieldGuard.lean).
- The filling `onlineProverPartsInUse` holds this half as its `second` (`filling_at_head`,
  AtFullSide/K12/DescAtHeadW.lean: under the library's head, where `onlineProverFromPublicFiles` returns at that filling
  and the shared chain's six are made), and W's sending's half (`K1.wSide`) in its last lot
  (Honest/K1/Law/WSideAtFill.lean).
- All limits of JobW.lean and DoorLast.lean stand. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean in the folder above.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtProof.JobW
import Johnson.Desc.ProofFile.Honest.K12.DoorLast
import Johnson.Desc.ProofFile.Honest.K12.FieldGuard
import Johnson.Desc.ProofFile.Honest.K12.AtProof.Doors
import Johnson.Desc.ProofFile.Honest.K13.WData

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtProof
open VerifiableInference.Desc (Block FileDescription)
open VerifiableInference.Desc.K12 (P12 T12)
open ProofFile.Honest.K12.Light (ManyJob doorW askOf)

variable {V W₀ Rc Xi Tr X : Type}

/-- What W's sending's job reads of the input. -/
def inOf (readers : Local W₀ Rc Xi Tr → Readers) (w : Local W₀ Rc Xi Tr) : K1.PlaceIn Xi :=
  ⟨w.x, readers w⟩

/-- **The job at the last chain's test, at a public part.** S: the sizes of the first opening's
job. Fd, enter: the description and the test's way in. pile: the rows that the batching piles up.
no: the number that a place's first new message gets. rand: the index committer's values, at the
shared chain's plan. -/
def jobRealW (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String T12)
    (pile : Pub → Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : Pub) (G : Ground) :
    Option (ManyJob (Local W₀ Rc Xi Tr) X) :=
  (four Z).bind fun F => (sendPub Z).bind fun A =>
    (OnBytes.linMessageW Z.first.lin).map fun msg =>
      jobW F.W (doorW Fd (·.x) enter placeW idleT12) (K1.firstJob S Z G)
        (K1.wJobAt Z.first (K1.wGp Z) 4 msg (no ⟨1, none, 4, .K1⟩) (K13.wDataAt pile Z G)) A readers
        (inOf readers) (askOf A weights (rand A.P)) (Fd.first.blocksInOrder.flatMap (·.rounds)).length

/-- The same as a `TestJob`. -/
def realW (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String T12)
    (pile : Pub → Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : Pub) (G : Ground) :
    Option (TestJob (Local W₀ Rc Xi Tr) X) :=
  (jobRealW S Fd enter pile no readers weights rand Z G).map (·.toRun.toTest)

/-- **The pair of parts at the test's place, behind the guard**; no side where the job is not made.
-/
def halfW (S : OnBytes.HonestTrace.Sz) (Fd : FileDescription Xi) (enter : Fd.S₃ → Except String T12)
    (pile : Pub → Ground → K13.PileOf Xi) (no : VerifiableInference.Desc.Place → Nat)
    (readers : Local W₀ Rc Xi Tr → Readers) (weights : Local W₀ Rc Xi Tr → Weights)
    (rand : Desc.K14.P14 → Local W₀ Rc Xi Tr → TableRand) (Z : Pub) (G : Ground) :
    List (Placed V (Local W₀ Rc Xi Tr) X) :=
  (realW S Fd enter pile no readers weights rand Z G).toList.map fun J =>
    (proverSideOfProximityTest J : Placed V (Local W₀ Rc Xi Tr) X).needsField

end ProofFile.Honest.K12.AtProof

#print axioms ProofFile.Honest.K12.AtProof.inOf
#print axioms ProofFile.Honest.K12.AtProof.jobRealW
#print axioms ProofFile.Honest.K12.AtProof.realW
#print axioms ProofFile.Honest.K12.AtProof.halfW
