-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/PartsBy.lean: the prover's side of a proximity test
(`KindName.K12`) as two values of type `Part` (Johnson/Desc/ProofFile/Honest/Frame.lean), with the
function that computes the rounds as a parameter `tm`. Definitions only. It imports Mathlib.

Parts.lean defines the same two parts with `testAll` (Test.lean) in the place of `tm`. Each
definition here whose name ends in `By` is a copy of one there: `msgBy` of `msgAt`, `moveBy` of
`moveAt`, `movesBy` of `movesFrom`, `halfBy` of `proverSideOfProximityTest`; the others drop the ending. All else is
used as Parts.lean, Test.lean and Coins.lean define it. `halfBy_testAll` (PartsByLaw.lean) proves
`halfBy J (testAll J) = proverSideOfProximityTest J` for every job, which covers all that is copied.

  `Term`         the type of `tm`: from the prover's input, what precedes the test, the random
                 values and all sampled challenges to the rounds, trees and opened columns
  `halfBy`       the two parts, for any `tm`
  `runTerm`, `runHalf`   `runBy` (RunBy.lean) at `RunIn.ofTest` (RunOf.lean) as such a function; the
                 two parts with it, at `Seams.fast` (FastW.lean). `runHalf J = proverSideOfProximityTest J` where the
                 stages pass `StagesOk` (`runHalf_eq`)
  `lightHalf`    `runHalf J` where the stages pass `StagesOk`, `proverSideOfProximityTest J` elsewhere. `lightHalf J
                 = proverSideOfProximityTest J` for every job (`lightHalf_eq`)

Limits.
- As in Parts.lean: every move computes all of `tm` again and keeps one round of it; each move hands
  on what it was handed; a challenge not received so far counts as empty; no move returns an error.
- Here the random values that a part is lent become a `TestCoins` (`firstPartBy`, `restPartBy`; the
  readers `stretchOf` and `stretches` of Coins.lean give 0 beyond the count; `tailsIn` and
  `restCoins` of Parts.lean read through them). As in Parts.lean: the first part's moves give `tm` 0
  for the switches' random values and, where the fresh table was sent before the test, 0 for that
  table's tails. That the messages of the first part's rounds depend on neither is `first_reads`
  (KeptLaw4.lean): for `testAll`, where the stages pass `StagesOk`. It asks that the other fields
  agree as whole functions, which the two parts' own `TestCoins` do not: for these see
  `Spec.first_meets` (LentSpec.lean), at the job of a `ManyJob`: no statement of this library
  concludes it; in another form: `msgAt_first` (CoinsAgree.lean) has that equation at any two
  families of coins under `Agree`, at two stages or more, and `agree_of_ties` (AgreeBook.lean) has
  `Agree` at the two parts' own readers, at the coins that the frame lends, where the fresh table
  has come earlier, under a test on the book and three more premises, and `agree_of_tiesO`
  (Own/AgreeOwn.lean) has it where the first fold sends its own table, under a test on the book and
  two more premises. In the second part `restCoins` passes on, as `mem`, all stretches that the part
  carries: so `mem` at the number `J.members.length` is the first fresh table's stretch, the values
  that also stand under `hide` and `tails`. A job whose `rows₀` or `trees₀` reads `mem` at that
  number reads them a second time. That at a `ManyJob`'s job, where the stages pass `StagesOk`,
  `testAll` does not depend on `mem` at that number is `Spec.test_reads_in` (LentSpec.lean): no
  statement of this library concludes it; near it: `first_reads_in` (LentLaw3.lean), on the messages
  of the first part's rounds alone.
- `runHalf` is not for a prover's side that is used: see its docstring. It ignores the warnings of
  `runBy` (`RunOut.no`), and so does `lightHalf` where it calls `runBy`. Its input is computed over
  the field; for one computed on words see PartsByJob.lean.
- Cost is not measured. Nothing on completeness, soundness or hiding.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.ProofFile.Honest.K12.RunOf
import Johnson.Desc.ProofFile.Honest.K12.RunBy
import Johnson.Desc.ProofFile.Honest.K12.RunBySpec
import Johnson.Desc.ProofFile.Honest.K12.FastW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.Light
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link (BOut)

variable {V W X C : Type}

/-! ## 1 A move -/

/-- A function that computes all that is shown in a test, from the prover's input w, what precedes
the test, the random values, and the sampled challenges by the round's number. -/
abbrev Term (W X : Type) : Type := W → Front X → TestCoins → (ℕ → Fmt.Drawn) → BOut

/-- The message of the test's round number i, taken from what `tm` computes: the round's items, and
its table where the stages' numbers say that the round sends a tree. Beyond the computed rounds it
is the empty message. -/
def msgBy (J : TestJob W X) (tm : Term W X) (w : W) (fr : Front X) (K : TestCoins)
    (D : ℕ → Fmt.Drawn) (i : ℕ) : Sending :=
  let O := tm w fr K D
  let col := O.tr.getD i fun _ => []
  ⟨((O.rs[i]?).map fun r => r.vals.filterMap saidOf).getD [],
    (depthAt J i).toList.map fun a => ⟨a, (col 0).length, fun x k => toF ((col x).getD k.val 0)⟩⟩

/-- The move of the test's round number i; the batching round "BAT" is round 0. rd selects what `tm`
reads of the random values that the part is given. The last i challenges received are the test's
own; the challenges and shown rounds before them go to `tm` as what precedes the test. The columns
that the move is handed go on as they are (`Seen.front`), as in `moveAt`. -/
def moveBy (J : TestJob W X) (tm : Term W X) (rd : C → TestCoins) (i : ℕ) : Move C W X :=
  ⟨fun c s t => .ok (msgBy J tm t.input
      ⟨t.heard.take (t.heard.length - i), t.own, s.front i⟩ (rd c)
      (fun r => (t.lately i).getD r ⟨[], [], [], none⟩) i),
    fun t => t.own⟩

/-- The moves of the rounds a, a + 1, ..., a + n - 1. -/
def movesBy (J : TestJob W X) (tm : Term W X) (rd : C → TestCoins) (a n : ℕ) :
    List (Move C W X) :=
  (List.range n).map fun i => moveBy J tm rd (a + i)

/-! ## 2 The rounds, stage by stage -/

/-- The fold of stage number j: "FOLD epsilon" and its k rounds. -/
def foldMovesBy (J : TestJob W X) (tm : Term W X) (rd : C → TestCoins) (j : ℕ) :
    List (Move C W X) :=
  movesBy J tm rd (roundOf J.p.nums.stages j) (1 + (J.p.nums.stages.getD j default).k)

/-- The switch out of stage number j: "SEND seed" and "CS". -/
def switchMovesBy (J : TestJob W X) (tm : Term W X) (rd : C → TestCoins) (j : ℕ) :
    List (Move C W X) :=
  movesBy J tm rd (roundOf J.p.nums.stages j + 1 + (J.p.nums.stages.getD j default).k) 2

/-- The base case: "BASE lambda" and "BASE". -/
def baseMovesBy (J : TestJob W X) (tm : Term W X) (rd : C → TestCoins) : List (Move C W X) :=
  movesBy J tm rd (roundOf J.p.nums.stages (J.p.nums.stages.length - 1)) 2

/-! ## 3 The parts -/

/-- The first part: "BAT" and the first fold. -/
def firstPartBy (J : TestJob W X) (tm : Term W X) : Part V W X :=
  match J.fresh with
  | none =>
    { takes := ⟨0, dueFresh J.s₀⟩, spends := [], carries := memberRuns J ⟨J.p.place, 0⟩
      bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
      moves := movesBy J tm
        (fun c =>
          ⟨(stretchOf c.1).e, tailsIn J.s₀ (stretchOf c.1).e, stretches _ c.2.2, fun _ => 0⟩)
        0 (firstLen J.p.nums.stages) }
  | some _ =>
    { takes := ⟨0, 0⟩, spends := [spentRun J], carries := memberRuns J ⟨J.p.place, 0⟩
      bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
      moves := movesBy J tm
        (fun c => ⟨(stretchOf c.2.1.1).e, fun _ _ => 0, stretches _ c.2.2, fun _ => 0⟩) 0
        (firstLen J.p.nums.stages) }

/-- The second part, all the rest: for each stage but the last its switch, with the fold of every
stage but the first before it; then the base case. -/
def restPartBy (J : TestJob W X) (tm : Term W X) : Part V W X :=
  { takes := ⟨0, dueRest J.p.nums.stages⟩, spends := []
    carries := memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J]
    bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      ((List.range (J.p.nums.stages.length - 1)).flatMap fun j =>
        (if j = 0 then [] else foldMovesBy J tm (restCoins J) j) ++
          switchMovesBy J tm (restCoins J) j) ++
      baseMovesBy J tm (restCoins J) }

/-- The two parts with the test's address. -/
def halfBy (J : TestJob W X) (tm : Term W X) : Placed V W X :=
  ⟨J.p.place, [firstPartBy J tm, restPartBy J tm]⟩

/-! ## 4 With `runBy` -/

/-- `runBy` as a function that computes all that is shown. S: the five expensive functions of a run
(`Seams`, Run.lean). -/
def runTerm (S : Seams) (J : TestJob W X) : Term W X :=
  fun w fr K D => (runBy S (RunIn.ofTest J w fr K) D).toB

/-- The two parts with `runBy` at its fastest functions. Not for a prover's side that is used: where
`StagesOk` fails, `runBy` can send a row's end unmasked (see `stagesBy`, RunBy.lean). Use
`lightHalf`. -/
def runHalf (J : TestJob W X) : Placed V W X := halfBy J (runTerm Seams.fast J)

/-- `runHalf J` where the job's stages pass `StagesOk`, `proverSideOfProximityTest J` elsewhere. It equals `proverSideOfProximityTest
J` for every job (`lightHalf_eq`, PartsByLaw.lean). Which branch a run takes is the value of
`StagesOk J.p.nums.stages`: where it is false, the run computes with `testAll`. -/
def lightHalf (J : TestJob W X) : Placed V W X :=
  if StagesOk J.p.nums.stages then runHalf J else proverSideOfProximityTest J

end ProofFile.Honest.K12.Light

#print axioms ProofFile.Honest.K12.Light.Term
#print axioms ProofFile.Honest.K12.Light.msgBy
#print axioms ProofFile.Honest.K12.Light.moveBy
#print axioms ProofFile.Honest.K12.Light.movesBy
#print axioms ProofFile.Honest.K12.Light.foldMovesBy
#print axioms ProofFile.Honest.K12.Light.switchMovesBy
#print axioms ProofFile.Honest.K12.Light.baseMovesBy
#print axioms ProofFile.Honest.K12.Light.firstPartBy
#print axioms ProofFile.Honest.K12.Light.restPartBy
#print axioms ProofFile.Honest.K12.Light.halfBy
#print axioms ProofFile.Honest.K12.Light.runTerm
#print axioms ProofFile.Honest.K12.Light.runHalf
#print axioms ProofFile.Honest.K12.Light.lightHalf
