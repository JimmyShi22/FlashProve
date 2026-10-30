-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Test.lean: `testAll` defines, over the field, all that a prover
shows in a proximity test (`KindName.K12`): the rounds, each round's tree, and the opened columns
tree by tree. Its arguments are a job (what a caller supplies for its test), the prover's input,
what precedes the test, the coins as functions of a number, and the sampled challenges of all rounds
by the round's number. Definitions only, none marked `noncomputable`; no theorem. It imports
Mathlib.

  `TestJob`      what a caller supplies for its test: the test's parameters; who sent the group's
                 oracle messages and the first fold's fresh table; and three functions of the
                 prover's input and of what precedes the test (`Front`,
                 Johnson/Desc/ProofFile/Honest/Sum.lean): the state on entry to the test (of type
                 `T12`, the type of the verifier's state inside a test), the first stage's rows, the
                 trees that hold them
  `TestCoins`    the coins that `testAll` reads, by number
  `freshCol`     the column, as words, of a tree that holds a fresh table and nothing else
  `TestJob.laid`, `s₀`, `first`, `recB`   the test's declared rounds, each with its oracle messages;
                 the first stage; the first stage's state; the state after the batching
  `testAll`      the main definition: the round "BAT", then the stages (`stagesAll`,
                 Johnson/Desc/K12/Honest/Stages.lean)
  `depths`, `depthAt`   for each round of the test, the depth of the tree that it sends, if any,
                 computed from the list of stages
  `TestJob.freshFits`   the job and the test's parameters agree on who sends the first fresh table

The first fold's fresh table. Whether the fold sends it itself is one field of the job: it does
where `fresh` is `none`. For this question `testAll`, `depthAt` and the parts (Parts.lean) read that
field alone. The verifier's side has a field of its own for the same fact, in the test's parameters
(`TestNums.ownMask`, Johnson/Desc/K12/TestEntries.lean), from which the block's declared rounds are
computed (`roundsOfNums`). `TestJob.freshFits` checks that the two agree. Where they do not, the
round "FOLD epsilon" sends a table where the block declares no root, or none where it declares one.
At a block whose `planOk` is true, `Step.tell` (Johnson/Desc/ProofFile/Honest/Frame.lean) then
returns an error, because the message fails the check of its shape (`Sending.fits`): that check
compares the message's tables with the parameters' field `oracles`, and `planOk` asks that this
field matches the declared roots. (The parts do not branch on the test's parameters instead, because
a part's counts of coins occur in the type of its moves (`Part.moves`): Lean would have to evaluate
the parameters to check a type.)

Whoever sends it, the table that `testAll` works with is `packedN`
(Johnson/Prover/Link/BodyPack.lean) at the hiding polynomial's coefficients: the library's packing
of them, 0 at every other entry, and 0 everywhere where a mask row's message has no room for them
(h + 2 (k - h) + 1 entries).

Where another part has sent the table, that sender must have built this same table from the same
coins. Nothing in this file checks that. A sender may build the table by another definition: at the
shared chain's job the sender's table is `laid` (Johnson/Desc/ProofFile/Honest/K14/Sendings.lean),
whose mask rows' entries are those of the packing `freshRow` of Fmt/M1Fold.lean where `freshFitsU`
is true (`freshCoef_atU`, FitSharedLaw.lean). The library has a theorem on the two packings
(`fresh_packed`, Johnson/Prover/Link/FoldPairs.lean): where a mask row's message has room for the
coefficients (h + 2 (k - h) + 1 entries), the table of the rows of `freshRow` (`freshRows`), indexed
with the row's number in the low bits, is `packed` (Johnson/Prover/Link/FoldHolds.lean), which
`packedN` gives by the numbers of row and entry, at the coefficients that `coefU` decodes from the
same words. That a sender's words decode to the coefficients that `hideAt` reads from this job's
coins is not shown here; `fresh_atU` (FreshAtJob.lean) takes it as a hypothesis (`SameFresh`) and
concludes, at one job, that the sender's table, decoded entry by entry, is the test's. Toy.lean
tests the two packings against each other at two small shapes, and only indirectly: it compares the
rounds and the trees' columns that it computes with another program's.

Limits.
- `rec₀`, `rows₀` and `trees₀` are parameters that the caller supplies. Nothing here compares them
  with a description, with what the senders of the group's oracle messages have sent, or with each
  other. For a caller who supplies rows that were never sent, `testAll` shows the folds of those
  rows.
- `rec₀` may read the rounds shown before the test (`Front.seen`). It is up to whoever fills it to
  state which shown items it reads, and that the entries of the book of coins (`ProverCoinCounts.ahead`,
  Johnson/Desc/ProofFile/Honest/Frame.lean) for the coins on which these items depend are disjoint
  from the entries that the test's parts spend (`Part.spends`).
- A `Front` holds the challenges received, what was handed on and the rounds shown, but no opened
  column. Where a block before the test has read columns of trees that were sent in the run, and the
  verifier's state holds something computed from them, `rec₀` cannot compute that from the `Front`.
- There is no theorem here, in Parts.lean or in Coins.lean. `stages_eq`
  (Johnson/Desc/K12/Honest/Stages.lean) proves that `stagesAll` equals the library's `bodyAll`
  (Johnson/Prover/Link/BodyAll.lean) where each stage fits the next (`FitAll`) and one tree of the
  stage's depth holds the rows. `testAll` passes to `stagesAll` whatever `trees₀` returns: that
  `testAll` is the round "BAT" followed by `bodyAll` is stated in none of these four files, not even
  for one tree, and no statement of this library names both; near it, from the first switch on:
  `restText_body` (Sim/TreesText.lean), under `FitAll`: the switch's own pieces, at any trees, and
  then `bodyAll` from the second stage on. That the block (`proximityTestKind guardedProximityTestParts p`) accepts what `testAll`
  shows is a theorem in none of them.
- With fewer than two stages `roundsOfNums` gives no rounds, and the block `proximityTestKind guardedProximityTestParts p`
  (Johnson/Desc/K12/Frame.lean) has no round and fails its own test on the plan (`planOk`): there no
  block with rounds corresponds to `testAll`.
- No honest prover is defined. No property is claimed: nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.K12.Honest.Stages
import Johnson.Desc.ProofFile.Honest.K12.Coins
import Johnson.Desc.ProofFile.Honest.Sum

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-- **What a caller supplies for its test.** W: the prover's input. X: what the parts hand on. -/
structure TestJob (W X : Type) where
  /-- the test's parameters -/
  p : P12
  /-- the group's oracle messages: for each, the address of the part that sent it, the message's
  number in that part's sending, and how many coins it has -/
  members : List (Addr × ℕ × Due)
  /-- who sent the first fold's fresh table: the sender's address and the message's number in that
  part's sending; `none`: the fold sends it itself -/
  fresh : Option (Addr × ℕ)
  /-- the state on entry to the test, of the type of the verifier's state inside a test, computed
  from the prover's input and from what precedes the test (challenges, what was handed on, the
  rounds shown); the caller's function, compared with nothing here -/
  rec₀ : W → Front X → T12
  /-- the first stage's two tables and their rows' tails, by index, computed from the prover's
  input, what precedes the test, and the members' coins by the member's number. Of the other fields
  of `PS`, `fM` and `fT` are overwritten (`first`). `sM` and `sT` reach `trees₀` with the rest of
  the state; otherwise they are read only where the list of stages has one stage, by the last
  stage's rounds -/
  rows₀ : W → Front X → (ℕ → Stretch) → PS
  /-- the trees that the first round of positions opens, in the order of the declared openings,
  computed from the same three and from the first stage's whole state, the fresh table included -/
  trees₀ : W → Front X → (ℕ → Stretch) → PS → List Tree

/-- The coins that `testAll` reads, by number. -/
structure TestCoins where
  /-- the first fold's fresh table: the hiding polynomial's coefficients -/
  hide : ℕ → GE
  /-- that table's rows' tails: row, entry -/
  tails : ℕ → ℕ → GE
  /-- the group's oracle messages' coins, by the member's number -/
  mem : ℕ → Stretch
  /-- the switches' coins -/
  rest : ℕ → GE

/-- The column, as words, of a tree that holds a fresh table and nothing else. -/
def freshCol (s : Sg) (P : PS) (x : ℕ) : List UInt64 :=
  wordsOf (wr (2 ^ s.h) (freshSym s P.fM P.fT x))

variable {W X : Type}

/-- The test's declared rounds, each with its oracle messages, paired as `proximityTestKind` pairs them
(Johnson/Desc/K12/Frame.lean); the empty list where `roundsOfNums` gives no rounds. -/
def TestJob.laid (J : TestJob W X) : Laid :=
  ((H2U.roundsOfNums J.p.nums).getD []).zip J.p.oracles

/-- The first stage; a stage of zeros where there is none. -/
def TestJob.s₀ (J : TestJob W X) : Fmt.M1.Stage := J.p.nums.stages.headD default

/-- The first stage's state: the caller's rows, with the fresh table set to the packing of the
coefficients (`packedN` at `hideAt`) and that table's tails set to `C.tails`. -/
def TestJob.first (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) : PS :=
  { J.rows₀ w fr C.mem with
    fM := packedN (sgOf J.s₀) (hideAt ((sgOf J.s₀).h + (sgOf J.s₀).g) C.hide), fT := C.tails }

/-- The state after the batching: the state of `rec₀`, advanced by the `decide` functions of
`guardedProximityTestParts.front` and `guardedProximityTestParts.bat`. d: what the round "BAT" sampled. Where one of the two rejects,
the state before it is kept. -/
def TestJob.recB (J : TestJob W X) (w : W) (fr : Front X) (d : Fmt.Drawn) : T12 :=
  let t₀ := J.rec₀ w fr
  let tF := ((guardedProximityTestParts.front J.p).decide t₀ [] []).toOption.getD t₀
  ((guardedProximityTestParts.bat J.p ((J.laid.take 1).map (·.1))).decide tF [noDigest ⟨[], d⟩] []).toOption.getD tF

/-- **All that is shown in the test.** D: the sampled challenges, by the round's number in the test:
"BAT" is round 0. -/
def testAll (J : TestJob W X) (w : W) (fr : Front X) (C : TestCoins) (D : ℕ → Fmt.Drawn) : BOut :=
  match J.p.nums.stages with
  | [] => ⟨[], [], []⟩
  | s :: rest =>
    let P := J.first w fr C
    let B := stagesAll J.p (coinsOf J.p.nums.stages C.hide C.rest) rest 0 s (J.laid.drop 1) 1
      (J.recB w fr (D 0)) P (J.trees₀ w fr C.mem P) D
    ⟨⟨[], D 0⟩ :: B.rs,
      (fun _ => []) :: (if J.fresh.isNone then B.tr.set 0 (freshCol (sgOf s) P) else B.tr), B.gs⟩

/-- For each round of the stages: the depth of the tree that it sends, if any. own: the first fold
sends its own table. -/
def depths : Bool → List Fmt.M1.Stage → List (Option ℕ)
  | _, [] => []
  | _, [_] => [none, none]
  | own, s :: n :: rest =>
    (if own then some s.Z.a else none) :: List.replicate s.k none ++ [some n.C.a, none] ++
      depths false (n :: rest)

/-- The same for the test's round number i, "BAT" being round 0. -/
def depthAt (J : TestJob W X) (i : ℕ) : Option ℕ :=
  ((none :: depths J.fresh.isNone J.p.nums.stages).getD i none)

/-- The job's field `fresh` and the test's parameters (`ownMask`) agree on who sends the first fresh
table. -/
def TestJob.freshFits (J : TestJob W X) : Bool := J.fresh.isNone == J.p.nums.ownMask

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.TestJob
#print axioms ProofFile.Honest.K12.TestCoins
#print axioms ProofFile.Honest.K12.freshCol
#print axioms ProofFile.Honest.K12.TestJob.laid
#print axioms ProofFile.Honest.K12.TestJob.s₀
#print axioms ProofFile.Honest.K12.TestJob.first
#print axioms ProofFile.Honest.K12.TestJob.recB
#print axioms ProofFile.Honest.K12.testAll
#print axioms ProofFile.Honest.K12.depths
#print axioms ProofFile.Honest.K12.depthAt
#print axioms ProofFile.Honest.K12.TestJob.freshFits
