-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
E2E/TreeRows.lean: the prover's messages with trees of the seven chains (Fiat-Shamir hash chains) of
the key file, a copy's file and the proof file, in the order of sending, as functions of the SIZES
that the list of rounds is computed from; and with them the tables of the three files' trees.
Definitions alone. General in the sizes.

Why. The rounds' data of the IOP as written in Lean say of a tree its depth and its width, and
nothing of the codes of the rows beneath it. The codes stand in the sizes (`Params.Sized`,
OnBytes/Params/Configure.lean), with the shapes of the oracle messages. This file puts the oracle
messages in the order in which the chains send them, so that E2E/TreeReads.lean's `along` can lay
them along the rounds.

Whose lists these are. Each list is put together from the library's own functions on shapes, as
`Johnson.G.sendsFrom` (Johnson/G/SendsFrom.lean) puts them together: `frameSends`, `ioppSends`,
`linMessageU`, `linMessageOmega`, `linMessageW`, `linkMessage`, `Wf.messageOf`. One message more
than there: the fresh mask that the first fold of Omega's test sends itself, in a round of its own,
which that file's head names as not listed. It is laid here between the code switches of the folded
row's test and those of Omega's test, as `foldMaskNotice` (OnBytes/Iop/Fold.lean) of that test's
first stage, as Johnson/G/RoundsOfPlan.lean has it.

Main names. `sentOfTest`, `sentShared`, `sentKey`, `sentProof`, `sentLink`: the lists.
`tableKey`, `tableProof`, `tableLink`: the tables of the three files' trees.

Limits.
- THE TABLE IS A READING, NOT A THEOREM. That a chain sends these oracle messages in this order,
  each under the code whose number its shape names, is a reading of the library's text, as the head
  of Johnson/G/Sends.lean says of its own lists. What holds it against the rounds' data is `along`'s
  test alone (E2E/TreeReads.lean's limits say how little that sees). So every r in a table rests on
  the code numbers in the sizes' shapes.
- Under which mask code the fold's own mask stands rests on `foldMaskNotice`: the mask code of the
  stage.
- Without a split between the folded row's group and Omega's no such mask is laid. Nothing here was
  evaluated at sizes without a split.
- No theorem is stated. Nothing on hiding follows from this file alone.


-/
import E2E.TreeReads
import Johnson.G.Sends

set_option autoImplicit false

namespace AtPublicFiles.TreeReads
open OnBytes OnBytes.Params OnBytes.Maker

/-- The prover's messages of the code switches of a proximity test. a: the answers to each OOD
sample. -/
def sentOfTest (a : ℕ) (ride : Bool) (st : List IoppStage) : List (List OracleNotice) :=
  (Johnson.G.ioppSends "" a ride 1 st).map (·.sent)

/-- The prover's messages with trees of a second chain, which a batch shares: the folded row; Omega;
the code switches of the folded row's test; with a split: the fresh mask of the first fold of
Omega's test, then that test's code switches. -/
def sentShared (S : LinShape) (a : ℕ) : Option (List (List OracleNotice)) :=
  (linMessageU S).map fun u =>
    [u.toList, (linMessageOmega S).toList] ++ sentOfTest a S.choice.masksRide S.testU ++
      (if S.sharedSplitNeeded then
        (S.testOmega.head?.map fun s => [foldMaskNotice (ioppFoldShape s {})]).toList ++
          sentOfTest a S.choice.masksRide S.testOmega
      else [])

/-- The key file's three chains. -/
def sentKey (z : Plan.KeySized) (a : ℕ) :
    Option (List (List OracleNotice) × List (List OracleNotice) × List (List OracleNotice)) :=
  match linMessageW z.once.shape, sentShared z.once.shape a with
  | some w, some s =>
    some ([[z.once.input], (Wf.messageOf z.ranges.x).toList] ++
        sentOfTest a z.ranges.x.choice.masksRide z.ranges.x.stages ++ [w.toList], s,
      sentOfTest a z.once.shape.choice.masksRide z.once.shape.testOwn)
  | _, _ => none

/-- The proof file's three chains. -/
def sentProof (z : ProofSized) (a : ℕ) :
    Option (List (List OracleNotice) × List (List OracleNotice) × List (List OracleNotice)) :=
  match linMessageW z.batch.shape, sentShared z.batch.shape a with
  | some w, some s =>
    some ((Johnson.G.frameSends z a 0 (reqGroups z.request).toList z.request.link).map (·.sent) ++
        [w.toList], s,
      sentOfTest a z.batch.shape.choice.masksRide z.batch.shape.testOwn)
  | _, _ => none

/-- The one chain of a copy's file. -/
def sentLink (z : LinkSized) (a : ℕ) : List (List OracleNotice) :=
  (linkMessage z.shape a).toList :: sentOfTest a z.shape.choice.masksRide z.shape.test

/-- **The table of the key file's trees**, at rounds' data D and sizes z. -/
def tableKey (D : WholeD) (z : Plan.KeySized) (a : ℕ) : Option (List Beneath) :=
  (sentKey z a).bind fun S => tableOf D z.codes S.1 S.2.1 S.2.2

/-- **The table of the proof file's trees.** -/
def tableProof (D : WholeD) (z : ProofSized) (a : ℕ) : Option (List Beneath) :=
  (sentProof z a).bind fun S => tableOf D z.codes S.1 S.2.1 S.2.2

/-- **The table of the trees of a copy's file.** -/
def tableLink (ds : List TypedOracleCompiler.Run.PQ.RD) (z : LinkSized) (codes : Codes) (a : ℕ) :
    Option (List Beneath) :=
  tableOne ds codes (sentLink z a)

end AtPublicFiles.TreeReads
