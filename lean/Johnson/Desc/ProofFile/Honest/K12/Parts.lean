-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Parts.lean: the prover's side of a proximity test (`KindName.K12`)
as two values of type `Part` (Johnson/Desc/ProofFile/Honest/Frame.lean), and the pair of them at the
test's place (`proverSideOfProximityTest`, of type `Placed`). Defined for every job (`TestJob`, Test.lean).
Definitions only, none marked `noncomputable`; no theorem.

The two parts. The book (`ProverCoinCounts`, Frame.lean) is public data: how many random values each part has of
its own, which stretches of one part's values another part is given too, and how many rounds each
part has. `cutsOf` (Johnson/Desc/ProofFile/Honest/BookOf.lean) computes the last of these from a
description; by `cutOfNames` it divides a proximity test's rounds into at most two parts: the round
"BAT" with the first fold, and all the rest. A part states each stretch that it is given under
`spends` or under `carries`, by name and count (for the difference see `Ahead.once`, Frame.lean).
  The first part sends nothing in "BAT", then the first fold's 1 + 2k scalars. Where the fresh table
    was sent before the test (`J.fresh` is `some _`), the part has no random value of its own and
    spends one stretch: that table's 2k + 1 coefficients. Where the fold sends the table itself
    (`J.fresh` is `none`), these coefficients and the table's tails are the part's own random
    values, and "FOLD epsilon" sends the table too. In both cases the part carries one stretch for
    each oracle message of the group: that message's random values.
  The second part has every switch, every later fold and the base case. Its own random values are
    the switches' (`dueRest`, Coins.lean). It carries the stretches of the group's oracle messages,
    in the job's order, and then, as the last stretch, the first fresh table's, whole: coefficients
    and tails.

Why the second part is not built with `Part.andThen` (Frame.lean). That function divides the joined
part's own random values between the two parts that it joins, by type, and no entry of the book can
pass values from the first of the two to the second. But the fold of stage j + 1 sends the sums of
the hiding polynomial whose coefficients the switch out of stage j put into the fresh table that
goes out with its oracle message; and the switch out of stage j + 1 folds the tails, the free
entries and the pad of that oracle message. What the parts hand on to each other (`State.own`) is
computed from the input and the challenges alone (`Move.hand`, Frame.lean), so it cannot pass on a
random value. Hence every move here takes, as the type of its random values, all that its part is
given, and computes its message from the start: the message is round number i of one value,
`testAll` (Test.lean), at the challenges received so far. A challenge that has not been received
counts as an empty one.

  `saidOf`       an item of a shown round (`Fmt.ItemValue`) as an item of a message (`Said`, Frame.lean)
  `msgAt`, `moveAt`   the message of the test's round number i, at sampled challenges for all
                 rounds; the move of that round: that message at the challenges received so far. The
                 type C of the random values and the function rd from C to `TestCoins` are
                 parameters
  `movesFrom`    the moves of n rounds in a row
  `firstLen`, `roundOf`, `foldMoves`, `switchMoves`, `baseMoves`   the first part's number of
                 rounds; the number of a stage's first round; the moves of a stage's fold, of its
                 switch, of the base case
  `memberRuns`, `freshRun`, `spentRun`   the names and counts of the stretches that the parts state;
                 the names are built by `carriedName` and `runName`
                 (Johnson/Desc/ProofFile/Honest/ForKinds.lean)
  `freshFrom`, `tailsIn`, `restCoins`   who sends the first fresh table; the tails within that
                 table's stretch; the `TestCoins` that the second part's moves read
  `firstPart`, `restPart`, `proverSideOfProximityTest`   the two parts; the pair at the test's place

No move returns an error. Beyond the rounds of `testAll` a move's message is empty.

Stops (`Part.bad`, `Part.hid`, Frame.lean: the challenges at which the prover does not go on).
Neither part has one: both functions return `none` everywhere, and both parts state the share 0 of 1
(`badShare`, `hidShare`). In support of that: in no round of a proximity test is the prover left
without a message to send, whatever was sampled. The library's honest side of a code switch
(`ldSwitchHon`, Cb/Ld/LdSwitch.lean) has a parameter for seeds at which the prover stops; a seed's
factor is sampled among the elements other than 0, by the round's declared form (`drawsMarkedNonzeroHaveNonzeroWords`,
Johnson/Desc/Block.lean, which asks that its three words are not all 0), and `orOne`
(Johnson/Desc/K12/Honest/Fold.lean) puts 1 where a list of challenges has 0 all the same. That no
stop is needed is not shown here.
Falls (checks of the verifier on values that can fail in an honest run): none is defined here. None
has been found for this kind; the kind's definition has not been searched for them.
Outside a part's scope: proof of work, nonces, roots, salts, bytes.

Limits.
- That round i of `testAll` does not depend on the challenges sampled from round i on, so that the
  rounds played one by one are the rounds of `testAll` at the whole list of sampled challenges, is
  proved in Played.lean (`testAll_causal`, `say_eq`), not here.
- The first part's moves give `testAll` 0 for the switches' random values and, where the fresh table
  was sent before the test, 0 for that table's tails. Where the stages pass `StagesOk` (RunBy.lean),
  the messages of the first part's rounds depend on neither: `first_reads` (KeptLaw4.lean), between
  two values of `TestCoins` that agree in their other fields as whole functions. The two parts' own
  `TestCoins` do not agree so; for these see `Spec.first_reads_in` (LentSpec.lean; proved:
  `first_reads_in`, LentLaw3.lean) and `Spec.first_meets` (LentSpec.lean; no statement of this
  library concludes it), at a `ManyJob`'s job. In another form: `msgAt_first` (CoinsAgree.lean) has
  that equation at any two families of coins under `Agree`, at two stages or more. `Agree` at the
  two parts' own readers, at the coins that the frame lends: `agree_of_ties` (AgreeBook.lean), where
  the fresh table has come earlier, under a test on the book and three more premises;
  `agree_of_tiesO` (Own/AgreeOwn.lean), where the first fold sends its own table, under a test on
  the book and two more premises. Where the stages do not pass `StagesOk`: not shown.
- One value stands in two fields of the second part's `TestCoins`. `restCoins` sets `mem` to all
  stretches that the part carries, so `mem` at the number `J.members.length` is the first fresh
  table's stretch: the values that also stand under `hide` and `tails`. In the first part `mem` at
  that number is `Stretch.zero`. Likewise `hide` from the number 2k + 1 on: in the second part, and
  in the first where `J.fresh` is `none`, it gives the table's tails; in the first part where
  `J.fresh` is `some _` it gives 0. `rows₀` and `trees₀` are the caller's functions of `mem`: a job
  that reads `mem` at that number puts the table's random values into its rows, and computes other
  rows in the two parts. Nothing here excludes such a job. That at a `ManyJob`'s job, where the
  stages pass `StagesOk`, `testAll` does not depend on `mem` at that number is `Spec.test_reads_in`
  (LentSpec.lean): no statement of this library concludes it; near it: `first_reads_in`
  (LentLaw3.lean), on the messages of the first part's rounds alone.
- A table's depth is computed from the stages' numbers (`depthAt`, Test.lean), and its width is the
  number of words of the column at position 0. So the check of a message's shape against what the
  sub-protocol states (`Sending.fits`, Frame.lean) can fail. A column of another length at another
  position is cut or filled with 0.
- The rounds are counted with k here and with h + (k - h) in `testAll`: the same number where h ≤ k.
- With fewer than two stages there is no sub-protocol that the two parts belong to (see the limits
  of Test.lean); both parts state a fresh table's random values all the same.
- The counts and names are compared with a book at small made-up sizes (Toy.lean).
- No simulator is defined for a part. No property is claimed: nothing on completeness, on soundness
  or on what is hidden.
Terms: RunBySpec.lean.
-/
import Johnson.Desc.ProofFile.Honest.K12.Test
import Johnson.Desc.ProofFile.Honest.ForKinds

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Slice Cb
open Johnson.Prover.Link (BOut)

variable {V W X C : Type}

/-! ## 1 A move -/

/-- An item of a shown round (`Fmt.ItemValue`) as an item of a message (`Said`); a root gives `none`. -/
def saidOf : Fmt.ItemValue → Option Said
  | .f x => some (.f (toF x))
  | .e x => some (.e (toE x))
  | .word x => some (.word x)
  | .answer x => some (.answer (toE x))
  | .root _ => none

/-- **The message of the test's round number i**, taken from what `testAll` computes at the sampled
challenges D: the round's items in the clear, and its table where the stages' numbers say that the
round sends a tree. Beyond the computed rounds it is the empty message. -/
def msgAt (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn) (i : ℕ) :
    Sending :=
  let O := testAll J w fr K D
  let col := O.tr.getD i fun _ => []
  ⟨((O.rs[i]?).map fun r => r.vals.filterMap saidOf).getD [],
    (depthAt J i).toList.map fun a => ⟨a, (col 0).length, fun x k => toF ((col x).getD k.val 0)⟩⟩

/-- **The move of the test's round number i**; the batching round "BAT" is round 0. rd selects what
`testAll` reads of the random values that the part is given. The last i challenges received are the
test's own so far. The challenges and the shown rounds before them go to `testAll` as what precedes
the test (`Front`): none of them where a list has fewer than i entries. The columns that the move is
handed beside the rounds (`Seen.opened`) go on as they are (`Seen.front`): this text reads none of
them; whether a job's letter does is the job's matter. -/
def moveAt (J : TestJob W X) (rd : C → TestCoins) (i : ℕ) : Move C W X :=
  ⟨fun c s t => .ok (msgAt J t.input
      ⟨t.heard.take (t.heard.length - i), t.own, s.front i⟩ (rd c)
      (fun r => (t.lately i).getD r ⟨[], [], [], none⟩) i),
    fun t => t.own⟩

/-- The moves of the rounds a, a + 1, ..., a + n - 1. -/
def movesFrom (J : TestJob W X) (rd : C → TestCoins) (a n : ℕ) : List (Move C W X) :=
  (List.range n).map fun i => moveAt J rd (a + i)

/-! ## 2 The rounds, stage by stage -/

/-- The number of the first part's rounds: "BAT" and the first fold; "BAT" alone where the test has
fewer than two stages. -/
def firstLen : List Fmt.M1.Stage → ℕ
  | s :: _ :: _ => 2 + s.k
  | _ => 1

/-- The number of the first round of stage number j: 1, plus k + 3 for each earlier stage. -/
def roundOf (stages : List Fmt.M1.Stage) (j : ℕ) : ℕ := 1 + ((stages.take j).map (·.k + 3)).sum

/-- The fold of stage number j: "FOLD epsilon" and its k rounds. -/
def foldMoves (J : TestJob W X) (rd : C → TestCoins) (j : ℕ) : List (Move C W X) :=
  movesFrom J rd (roundOf J.p.nums.stages j) (1 + (J.p.nums.stages.getD j default).k)

/-- The switch out of stage number j: "SEND seed" and "CS". -/
def switchMoves (J : TestJob W X) (rd : C → TestCoins) (j : ℕ) : List (Move C W X) :=
  movesFrom J rd (roundOf J.p.nums.stages j + 1 + (J.p.nums.stages.getD j default).k) 2

/-- The base case: "BASE lambda" and "BASE". -/
def baseMoves (J : TestJob W X) (rd : C → TestCoins) : List (Move C W X) :=
  movesFrom J rd (roundOf J.p.nums.stages (J.p.nums.stages.length - 1)) 2

/-! ## 3 The stretches -/

/-- The group's oracle messages' stretches, as the part at `dest` states them. -/
def memberRuns (J : TestJob W X) (dest : Addr) : List (String × Due) :=
  J.members.map fun m => (carriedName m.1 m.2.1 dest, m.2.2)

/-- Who sends the first fresh table, as an address and a message's number: the job's field `fresh`;
where that is `none` (the first fold sends the table itself): message number 0 of the first part. -/
def freshFrom (J : TestJob W X) : Addr × ℕ := J.fresh.getD (⟨J.p.place, 0⟩, 0)

/-- The first fresh table's stretch, whole, as the second part states it. -/
def freshRun (J : TestJob W X) : String × Due :=
  (carriedName (freshFrom J).1 (freshFrom J).2 ⟨J.p.place, 1⟩, ⟨0, dueFresh J.s₀⟩)

/-- The stretch that the first part spends: the hiding polynomial's coefficients. -/
def spentRun (J : TestJob W X) : String × Due :=
  (runName foldMaskRun ⟨J.p.place, 0⟩ "fold", ⟨0, 2 * J.s₀.k + 1⟩)

/-! ## 4 The parts -/

/-- The tails of a fresh table's rows, which follow its 2k + 1 coefficients in a stretch: row b,
entry q. -/
def tailsIn (s : Fmt.M1.Stage) (c : ℕ → GE) (b q : ℕ) : GE := c (2 * s.k + 1 + b * s.Z.r + q)

/-- **The first part**: "BAT" and the first fold. -/
def firstPart (J : TestJob W X) : Part V W X :=
  match J.fresh with
  | none =>
    { takes := ⟨0, dueFresh J.s₀⟩, spends := [], carries := memberRuns J ⟨J.p.place, 0⟩
      bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
      moves := movesFrom J
        (fun c =>
          ⟨(stretchOf c.1).e, tailsIn J.s₀ (stretchOf c.1).e, stretches _ c.2.2, fun _ => 0⟩)
        0 (firstLen J.p.nums.stages) }
  | some _ =>
    { takes := ⟨0, 0⟩, spends := [spentRun J], carries := memberRuns J ⟨J.p.place, 0⟩
      bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
      moves := movesFrom J
        (fun c => ⟨(stretchOf c.2.1.1).e, fun _ _ => 0, stretches _ c.2.2, fun _ => 0⟩) 0
        (firstLen J.p.nums.stages) }

/-- What the second part's moves read of what the part is given: the fresh table's stretch is the
last of those that it carries. `mem` is all carried stretches, that one included (see the limits in
the file's head). -/
def restCoins (J : TestJob W X)
    (c : Handed ⟨0, dueRest J.p.nums.stages⟩ [] (memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J])) :
    TestCoins :=
  let all := stretches _ c.2.2
  ⟨(all J.members.length).e, tailsIn J.s₀ (all J.members.length).e, all, (stretchOf c.1).e⟩

/-- **The second part**: all the rest: for each stage but the last its switch, with the fold of
every stage but the first before it; then the base case. -/
def restPart (J : TestJob W X) : Part V W X :=
  { takes := ⟨0, dueRest J.p.nums.stages⟩, spends := []
    carries := memberRuns J ⟨J.p.place, 1⟩ ++ [freshRun J]
    bad := fun _ _ => none, hid := fun _ _ _ => none, badShare := ⟨0, 1⟩, hidShare := ⟨0, 1⟩
    moves :=
      ((List.range (J.p.nums.stages.length - 1)).flatMap fun j =>
        (if j = 0 then [] else foldMoves J (restCoins J) j) ++ switchMoves J (restCoins J) j) ++
      baseMoves J (restCoins J) }

/-- **The pair**: the two parts with the test's place, `J.p.place` (`Placed`, Frame.lean). -/
def proverSideOfProximityTest (J : TestJob W X) : Placed V W X := ⟨J.p.place, [firstPart J, restPart J]⟩

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.saidOf
#print axioms ProofFile.Honest.K12.msgAt
#print axioms ProofFile.Honest.K12.moveAt
#print axioms ProofFile.Honest.K12.movesFrom
#print axioms ProofFile.Honest.K12.firstLen
#print axioms ProofFile.Honest.K12.roundOf
#print axioms ProofFile.Honest.K12.foldMoves
#print axioms ProofFile.Honest.K12.switchMoves
#print axioms ProofFile.Honest.K12.baseMoves
#print axioms ProofFile.Honest.K12.memberRuns
#print axioms ProofFile.Honest.K12.freshFrom
#print axioms ProofFile.Honest.K12.freshRun
#print axioms ProofFile.Honest.K12.spentRun
#print axioms ProofFile.Honest.K12.tailsIn
#print axioms ProofFile.Honest.K12.firstPart
#print axioms ProofFile.Honest.K12.restCoins
#print axioms ProofFile.Honest.K12.restPart
#print axioms ProofFile.Honest.K12.proverSideOfProximityTest
