-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Sims.lean: a simulator's form beside each of the two parts of
a proximity test's prover (Johnson/Desc/ProofFile/Honest/K12/Parts.lean), in the frame for the
honest side (`Sim`, Johnson/Desc/ProofFile/Honest/Frame.lean). Definitions, none marked
`noncomputable`, and three small theorems (`msgAt_eq`, `ok_bind`, `SimJob.entry_of_ok`). General in
the type `Pb` of the input's public part and in every field of the simulators' job (`SimJob`).

Terms. A part is a value of type `Part` (Frame.lean); the two parts are `firstPart`, the round "BAT"
and the first fold, and `restPart`, all other rounds (Parts.lean). A job is what a caller supplies
for its test: a `TestJob` (Johnson/Desc/ProofFile/Honest/K12/Test.lean) for the parts, a `SimJob`
for the simulators. The place's numbers are the test's parameters (`P12`,
Johnson/Desc/K12/Frame.lean). A stage is a `Fmt.M1.Stage`; k, h and r' are the first stage's `k`,
`h` and `Z.r`. A text is a function with values in `BOut` (Johnson/Prover/Link/BodyAll.lean):
rounds, each round's tree, and groups of opened columns. The front is the `Before` that a simulator
is handed. The description's own parts are another thing: the fields `front`, `bat` and `fold` of
`guardedProximityTestParts`, steps of the test's description, each with a `decide`. In front of, behind, beside:
before, after, next to. The test's door: its entry. A letter: a free parameter, or a field that the
caller fills. To lay: to put or to make. To hang on: to depend on. Heard: received as a challenge.
Rows 0: `zeroPS` as the first stage's state. The run that the first part spends: `spentRun`
(Parts.lean). The riding table: the first fold's fresh table, sent earlier in its sender's tree. The
one symbol: `none`, which `Sim.tell` returns in place of a list of rounds. The row: the two parts,
each with its simulator's form (`testPairs`, Sim/Row.lean). A member of a law: values at which all
hypotheses of a theorem on two distributions hold together.

Where the cited names are. `stretchOf`, `dueRest`, `dueFresh`, `coinsOf`:
Johnson/Desc/ProofFile/Honest/K12/Coins.lean. `shownOf`, `Before.treeCols`:
Johnson/Desc/ProofFile/Honest/Side.lean. `readsOf`, `fillCols`: Frame.lean. `guardedProximityTestParts`:
Johnson/Desc/K12/JoinGuarded.lean. `groupsAt`, `aRec1`: Johnson/Desc/K12/Honest/Stages.lean. `msgAt`:
Parts.lean.

  `firstSim`: beside the first part. Where the fresh table came earlier: 2k + 1 coins, laid as the
    fold's 2k + 1 scalars in the order in which they are shown; it reads nothing else. Where the
    fold sends the table itself: the part's own text at rows 0: it reads its challenges, its
    positions and its coins
  `zeroTextK`, `zeroText`, `restZeroText`, `restSim`: beside the second part: `restText`
    (Sim/Text.lean) at the state `entry`, at rows 0, at its own coins in the part's own order, at
    the columns that are shown in the whole front; the one item of "BASE lambda" laid anew by
    `tauSim`
  `testSims`: the two, in the row's order
  `SimJob`: what a caller says, all of it public: the place's numbers · whether the first fold sends
    its own fresh table · which trees the first round of positions opens · one letter: the
    verifier's state that the test is entered with, of the public part and of what is shown in front
    of the test
  `SimJob.trees₀`: these trees, made of the columns that are shown in front
  `SimJob.entry`, `SimJob.entry?`, `SimJob.entry_of_ok`: the verifier's state behind the first fold:
    the description's own parts (`guardedProximityTestParts`: front, the batching, the fold) run from the letter's
    state over the first part's rounds as they are shown in front; the second with a rejection where
    one of them, or the block's own question between them, rejects; `entry_of_ok`: where the second
    accepts, its state is the first's
  `tauSim`: the element that meets the base case's equation at what the last round shows: the
    claim's left side at the two shown messages, less the sampled element times the claim's target
  `sendingOf`, `msgAt_eq`, `shownAs`, `shownFrom`: a round's message cut out of a text's output: the
    cut that the parts' own moves make (`msgAt`), by unfolding; what is shown of such a message at
    given positions, as the frame's `shownOf` shows a round as played
  `Before.cut`, `lastSeen`: what is shown in front of the last n rounds; these n rounds
  `zeroPS`: a stage's state in which every entry is 0
  `firstOwnText`: the first part's text at rows 0, where the fold sends its own table
  `SimJob.recB`: the verifier's state behind the batching, as `TestJob.recB` makes it
  `SimJob.stages`, `SimJob.s₀`, `SimJob.laid`, `SimJob.depthAt`: the job's list of stages; its first
    stage; the test's rounds with their oracle messages; the depth of the tree that a round sends,
    if any. The last three are written as `TestJob.s₀`, `TestJob.laid` and `depthAt` (Test.lean)
    are, with the field `own` in the place of `fresh.isNone`
  `noDraw`: a challenge in which nothing is sampled
  `ok_bind`: where `Except.bind` returns `.ok`, its first argument is `.ok` of a value at which the
    second returns that `.ok`

What they are handed that hangs on the index or on a run, all of it as data in front (`Before`) or
as the input's public part. `restSim`: the columns that are listed in front of the trees which the
first round of positions opens · the first part's rounds as shown · and, through the one letter
`rec₀`, whatever the verifier's state at the test's door is made of: shown items, listed columns,
stored columns, the public part (a key). `firstSim`: nothing. By type neither is handed the input, a
witness, the index or a coin of the run: a simulator's arguments are the public part · `Before` ·
the challenges of its part's rounds · the positions that will be read of its part's tables · coins
of its own; and `SimJob` is typed over the public part alone. The types give less than the words "by
type neither is handed": `Sim.tell` has just these five arguments, but `Pb` is a free type parameter
of `Sim` and of `SimJob`, and a `Before` is whatever a caller supplies: either may hold the input, a
witness, the index or coins of the run.

The count, part by part. First part, the fresh table sent earlier: 2k + 1 coins, 2k + 1 scalars
shown. First part, the fold sends its table: 2k + 1 + 2^h r' coins; shown: 2k + 1 scalars and 2^h
symbols a position asked. Second part: the part's own count (`dueRest`); what is shown against it is
not counted here.

Four choices of this text. (1) Of "the verifier's state at the entry" the first two legs (the
description's step folded over the front; entering the test) are one letter here, `rec₀`. (2) "The
part's data are 0" is laid in front of the first fold's point (the first stage's whole state is 0),
not behind it. (3) "Play the text at data 0" and "compute the verifier's values" are one pass, at
the verifier's own state. (4) The groups of columns are laid by the text's own `groupsAt` over
tables made of the listed columns, not by the frame's `readsOf` and `fillCols`; the two reduce and
list the positions by one formula. The shape "the honest text at the data 0, one item laid anew by
the verifier's equation" is also that of Johnson/LinkSim/AtText/Defs.lean (`simAll`, `tauStar`),
which stands at the link proof's proximity test, as one text for the whole proof and against another
form of statement; nothing of it is imported.

By what. `msgAt_eq` holds by unfolding `msgAt`. `ok_bind` is by cases. `SimJob.entry_of_ok` unfolds
`SimJob.entry?`, takes its steps apart by `ok_bind`, and unfolds `SimJob.entry`, `SimJob.recB` and
`aRec1`.

Limits.
- `rec₀` is a letter, `opens` public numbers. Nothing here holds them against a description, against
  what the verifier's walk holds at that place, or against the part's own letters `rec₀`, `trees₀`
  (`TestJob`): Sim/Row.lean and Sim/Spec.lean name these ties as clauses and premises.
- "The verifier's state" in this file's comments names what the field `rec₀` is meant to return, and
  what the description's parts make of that. That it is the verifier's state in any run is not
  shown.
- `Pb` is a free parameter, and a `Before` is whatever the caller supplies: the type `Sim` does not
  make a simulator's arguments harmless.
- Where a part of the description rejects, `entry` and the text keep the state in hand: no move and
  no simulator here returns the one symbol for that. Below two stages `restSim` yields the one
  symbol.
- Where a default can flow. A coin beyond the count reads as 0 (`stretchOf`): that no term reads
  there is not shown here.
- A challenge that is not there reads as "nothing sampled" (`noDraw`), a column that is not listed
  as no word: both public or heard.
- `lastSeen` and `Before.cut` subtract n from the front's number of rounds, and the subtraction
  stops at 0: at a front with fewer than n rounds `lastSeen` gives all its rounds and `Before.cut`
  keeps none. No definition here asks that the front has n rounds.
- Where a front lists two columns at one position of a tree, `SimJob.trees₀` takes the first.
- `zeroPS` and the 0 for the first fold's coefficients in `zeroText` stand for data of the part (its
  rows; stretches that it carries), which a simulator is not handed; they stand for no coin of the
  simulator's own.
- What else a run shows of the same coins. Of the run that the first part spends: the riding table's
  symbols in its sender's tree, at the first round of positions; what the first switch lays of that
  table's folded row and tail into its new message. Of the second part's own coins: nothing outside
  the part's own rounds and trees. This item is by reading: no statement here says any of it. No
  definition here bars an entry of the book of coins (`Ahead`, Frame.lean) that gives coins of the
  second part to another part too.
- In "The count" the numbers of coins are the fields `takes`. The numbers of what is shown are by
  reading: no statement here says them. They are meant at two stages or more: below that `firstSim`
  yields one round, without an item. Where the fold sends its table they are also meant where h is
  at most k: `firstOwnText` counts the fold's rounds with h + (k - h).
- Where h is above k, one coin is at two places in `firstOwnText`: `hideAt` at h + (k - h) = h takes
  the coins number 0 to 2h as coefficients, and `tailsIn` (Parts.lean) begins the rows' tails at
  number 2k + 1. `firstPart` with `TestJob.first` (Test.lean) has the same. No definition here bars
  h above k.
- `firstOwnText` is written out here. For the claim's coefficients it takes the `GroupRow` whose
  fields are all defaults (`{}`), where `testAll` (Test.lean) takes `rowOf` of the state after the
  batching. That it is the first rounds of `testAll` at rows 0 is not stated here.
- No test here. A member of a law on `restText` and `zeroText`, at a small place: Sim/ToyLaw.lean
  (not in the library yet): the hypotheses of such a theorem have no value that meets them together
  in the library yet.
- No property is claimed: the two simulators are data: nothing is said here of what they are good
  for. No property of a protocol is stated: nothing on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K12.Parts
import Johnson.Desc.ProofFile.Honest.K12.Sim.Text
import Johnson.Desc.ProofFile.Honest.Side

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

/-! ## 1 What a caller says -/

/-- **What a caller says of its test to the simulators: public letters alone.** Pb: the public part
of the input. -/
structure SimJob (Pb : Type) where
  /-- the place's numbers -/
  p : P12
  /-- the first fold sends its own fresh table -/
  own : Bool
  /-- the verifier's state that the test is entered with: of the public part and of what is shown in
  front of the test -/
  rec₀ : Pb → Before → T12
  /-- the trees that the first round of positions opens, in the order of the declared openings: for
  each the number of its chain, from 0; its number among the roots that are shown of that chain, as
  `Before.treeCols` counts them; its depth -/
  opens : List (ℕ × ℕ × ℕ)

variable {Pb W X : Type}

/-- The test's list of stages. -/
def SimJob.stages (J : SimJob Pb) : List Fmt.M1.Stage := J.p.nums.stages
/-- The first stage; the type's default where the list is empty. -/
def SimJob.s₀ (J : SimJob Pb) : Fmt.M1.Stage := J.p.nums.stages.headD default

/-- The test's rounds with their oracle messages, as `TestJob.laid` (Test.lean) has them. -/
def SimJob.laid (J : SimJob Pb) : Laid := ((H2U.roundsOfNums J.p.nums).getD []).zip J.p.oracles

/-- The trees that the first round of positions opens, made of the columns that are shown in front:
at a listed position the words that are listed there; elsewhere no word. -/
def SimJob.trees₀ (J : SimJob Pb) (fr : Before) : List Tree :=
  J.opens.map fun x => (x.2.2, fun q => (((fr.treeCols x.1 x.2.1).getD []).lookup q).getD [])

/-- The depth of the tree that the test's round number i sends, if any, as `depthAt` (Test.lean) has
it, with `own` in the place of `fresh.isNone`. -/
def SimJob.depthAt (J : SimJob Pb) (i : ℕ) : Option ℕ :=
  ((none :: depths J.own J.p.nums.stages).getD i none)

/-! ## 2 From a text's output to what is shown -/

/-- A round's message, cut out of a text's output. dep: the depth of the tree that the round sends,
if any. i: the round's number in the output. -/
def sendingOf (O : BOut) (dep : Option ℕ) (i : ℕ) : Sending :=
  let col := O.tr.getD i fun _ => []
  ⟨((O.rs[i]?).map fun r => r.vals.filterMap saidOf).getD [],
    dep.toList.map fun a => ⟨a, (col 0).length, fun x k => toF ((col x).getD k.val 0)⟩⟩

/-- It is the cut that the parts' own moves make. `msgAt`: Parts.lean. -/
theorem msgAt_eq (J : TestJob W X) (w : W) (fr : Front X) (K : TestCoins) (D : ℕ → Fmt.Drawn)
    (i : ℕ) : msgAt J w fr K D i = sendingOf (testAll J w fr K D) (depthAt J i) i := rfl

/-- What is shown of a message at given positions, root by root: as the frame's `shownOf` shows a
round as played. -/
def shownAs (x : Sending) (ask : List (List ℕ)) : Shown :=
  ⟨x.vals.map Said.got,
    x.tables.zipIdx.map fun y => ((ask[y.2]?).getD []).map fun q => (q, y.1.col q)⟩

/-- The rounds number 0, 1, ..., n - 1 of a text's output, as they are shown. dep: the depths by the
round's number in the output. -/
def shownFrom (O : BOut) (dep : ℕ → Option ℕ) (n : ℕ) (asks : List (List (List ℕ))) : List Shown :=
  (List.range n).map fun i => shownAs (sendingOf O (dep i) i) ((asks[i]?).getD [])

/-- What is shown in front of the last n rounds. -/
def _root_.ProofFile.Honest.Before.cut (f : Before) (n : ℕ) : Before :=
  { f with rounds := f.rounds.take (f.rounds.length - n) }

/-- The last n rounds that are shown, as a view shows them. -/
def lastSeen (f : Before) (n : ℕ) : List Fmt.RoundView := f.seen.drop (f.seen.length - n)

/-- A challenge in which nothing is sampled. -/
def noDraw : Fmt.Drawn := ⟨[], [], [], none⟩

/-- A stage's state in which every entry is 0. -/
def zeroPS : PS :=
  ⟨fun _ => 0, fun _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ _ => 0, fun _ => 0,
    fun _ => 0⟩

/-! ## 3 Beside the first part -/

/-- The first part's text at rows 0, where the fold sends its own table. c: its coins by number: the
2k + 1 coefficients, then the table's rows' tails. -/
def firstOwnText (J : SimJob Pb) (c : ℕ → GE) (D : ℕ → Fmt.Drawn) : BOut :=
  let s := J.s₀
  let W := hideAt ((sgOf s).h + (sgOf s).g) c
  let P : PS := { zeroPS with fM := packedN (sgOf s) W, fT := tailsIn s c }
  let rf := foldShown (sgOf s) (vecG (sgOf s) {}) (μOf (sgOf s) zeroPS) W fun n => D (1 + n)
  ⟨⟨[], D 0⟩ :: rf, (fun _ => []) :: (rf.map fun _ _ => []).set 0 (freshCol (sgOf s) P), []⟩

/-- **The form of a simulator beside the first part.** -/
def firstSim (J : SimJob Pb) : Sim Pb :=
  match J.own with
  | false =>
    { addr := ⟨J.p.place, 0⟩, takes := ⟨0, 2 * J.s₀.k + 1⟩
      tell := fun _ _ _ _ c =>
        some ((⟨[], []⟩ :: ⟨[.e (ofE ((stretchOf c).e 0))], []⟩ ::
          (List.range J.s₀.k).map fun i =>
            ⟨[.e (ofE ((stretchOf c).e (1 + 2 * i))), .e (ofE ((stretchOf c).e (2 + 2 * i)))],
              []⟩).take (firstLen J.stages)) }
  | true =>
    { addr := ⟨J.p.place, 0⟩, takes := ⟨0, dueFresh J.s₀⟩
      tell := fun _ _ ds asks c =>
        some (shownFrom (firstOwnText J (stretchOf c).e fun i => ds.getD i noDraw) J.depthAt
          (firstLen J.stages) asks) }

/-! ## 4 Beside the second part -/

/-- The verifier's state behind the batching, as `TestJob.recB` makes it. fr: what is shown in front
of the test. d: what "BAT" sampled. -/
def SimJob.recB (J : SimJob Pb) (pb : Pb) (fr : Before) (d : Fmt.Drawn) : T12 :=
  let t₀ := J.rec₀ pb fr
  let tF := ((guardedProximityTestParts.front J.p).decide t₀ [] []).toOption.getD t₀
  ((guardedProximityTestParts.bat J.p ((J.laid.take 1).map (·.1))).decide tF [noDigest ⟨[], d⟩] []).toOption.getD tF

/-- The verifier's state behind the first fold: from the letter's state, over the first part's
rounds as they are shown in front of the second part. -/
def SimJob.entry (J : SimJob Pb) (pb : Pb) (front : Before) : T12 :=
  let n₀ := firstLen J.stages
  let mine := lastSeen front n₀
  aRec1 J.p 0 J.s₀ (J.laid.drop 1) (J.recB pb (front.cut n₀) ((mine.map (·.drawn)).headD noDraw))
    mine.tail

/-- The same, strictly: a rejection where one of the description's own steps in front of the second
part rejects: the front · the batching · the block's own question between the batching and the fold
(the group's two codes, k and h are the first stage's) · the first fold. -/
def SimJob.entry? (J : SimJob Pb) (pb : Pb) (front : Before) : Except String T12 :=
  ((guardedProximityTestParts.front J.p).decide (J.rec₀ pb (front.cut (firstLen J.stages))) [] []).bind fun tF =>
  ((guardedProximityTestParts.bat J.p ((J.laid.take 1).map (·.1))).decide tF
    [noDigest ⟨[], ((lastSeen front (firstLen J.stages)).map (·.drawn)).headD noDraw⟩] []).bind
    fun tB =>
  if (guardedProximityTestParts.group tB).any (firstFits J.s₀) then
    (guardedProximityTestParts.fold J.p 0 J.s₀ (((J.laid.drop 1).take (1 + J.s₀.k)).map (·.1))).decide tB
      ((lastSeen front (firstLen J.stages)).tail.map noDigest) []
  else .error "the group is not the first stage's"

theorem ok_bind {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : x.bind f = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e => cases h
  | ok a => exact ⟨a, rfl, h⟩

/-- **Where the strict text accepts, its state is the state that the simulator runs at.** -/
theorem SimJob.entry_of_ok {J : SimJob Pb} {pb : Pb} {front : Before} {t₁ : T12}
    (h : J.entry? pb front = .ok t₁) : J.entry pb front = t₁ := by
  unfold SimJob.entry? at h
  obtain ⟨tF, hF, h⟩ := ok_bind h
  obtain ⟨tB, hB, h⟩ := ok_bind h
  split at h
  · unfold SimJob.entry SimJob.recB aRec1
    simp only [hF, hB, h, Except.toOption, Option.getD]
  · cases h

/-- The element that meets the base case's equation at what the last round shows. -/
def tauSim (p : P12) (e : EndAt) (D : ℕ → Fmt.Drawn) : Fmt.M1.E :=
  let s := sgOf e.cur
  let lam := toE ((D e.o).elems.headD (0, 0, 0))
  ofE (toE (tauSW s.C s.Z (claimAtEnd p e).c (claimAtEnd p e).d
        (fun j => e.P.sM j + lam * mainOf s (μOf s e.P) j)
        fun j => e.P.fM 0 j + lam * maskOf s (μOf s e.P) j) -
      lam * toE (claimAtEnd p e).tau)

/-- The text from the first switch on at rows 0, with the one item laid anew, at coins' letters K.
t₁: the verifier's state behind the first fold. trees: the trees that the first round of positions
opens. D: the test's challenges by the round's number in the test. -/
def zeroTextK (p : P12) (K : BCoins) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid)
    (t₁ : T12) (trees : List Tree) (D : ℕ → Fmt.Drawn) : BOut :=
  let O := restText p K s next rest l 1 t₁ zeroPS trees D
  let e := restEnd p K s next rest l 1 t₁ zeroPS trees D
  { O with rs := O.rs.set (O.rs.length - 2) ⟨[.e (tauSim p e D)], D e.o⟩ }

/-- The same at coins by number, in the second part's own order. The first fold's coefficients,
which `coinsOf` takes beside c, are laid 0: the text reads them nowhere (`restText_congr`,
Sim/Text.lean). -/
def zeroText (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (t₁ : T12)
    (trees : List Tree) (c : ℕ → GE) (D : ℕ → Fmt.Drawn) : BOut :=
  zeroTextK p (coinsOf (s :: next :: rest) (fun _ => 0) c) s next rest l t₁ trees D

/-- The same at the simulators' job: at the state `entry`, at the columns that are shown in front:
of the whole front, the first part's own rounds among it: where the first fold sends its own table,
that tree's root stands there. -/
def restZeroText (J : SimJob Pb) (pb : Pb) (front : Before) (c : ℕ → GE) (D : ℕ → Fmt.Drawn) :
    Option BOut :=
  match J.stages with
  | s :: next :: rest =>
    some (zeroText J.p s next rest (J.laid.drop 1) (J.entry pb front) (J.trees₀ front) c D)
  | _ => none

/-- **The form of a simulator beside the second part.** -/
def restSim (J : SimJob Pb) : Sim Pb :=
  { addr := ⟨J.p.place, 1⟩, takes := ⟨0, dueRest J.stages⟩
    tell := fun pb front ds asks c =>
      let n₀ := firstLen J.stages
      let mine := (lastSeen front n₀).map (·.drawn)
      (restZeroText J pb front (stretchOf c).e fun i =>
          if i < n₀ then mine.getD i noDraw else ds.getD (i - n₀) noDraw).map fun O =>
        shownFrom O (fun i => J.depthAt (n₀ + i)) O.rs.length asks }

/-- The two, in the row's order. -/
def testSims (J : SimJob Pb) : List (Sim Pb) := [firstSim J, restSim J]

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.msgAt_eq
#print axioms ProofFile.Honest.K12.ok_bind
#print axioms ProofFile.Honest.K12.SimJob.entry_of_ok
#print axioms ProofFile.Honest.K12.SimJob
#print axioms ProofFile.Honest.K12.SimJob.stages
#print axioms ProofFile.Honest.K12.SimJob.s₀
#print axioms ProofFile.Honest.K12.SimJob.laid
#print axioms ProofFile.Honest.K12.SimJob.trees₀
#print axioms ProofFile.Honest.K12.SimJob.depthAt
#print axioms ProofFile.Honest.K12.sendingOf
#print axioms ProofFile.Honest.K12.shownAs
#print axioms ProofFile.Honest.K12.shownFrom
#print axioms ProofFile.Honest.Before.cut
#print axioms ProofFile.Honest.K12.lastSeen
#print axioms ProofFile.Honest.K12.noDraw
#print axioms ProofFile.Honest.K12.zeroPS
#print axioms ProofFile.Honest.K12.firstOwnText
#print axioms ProofFile.Honest.K12.firstSim
#print axioms ProofFile.Honest.K12.SimJob.recB
#print axioms ProofFile.Honest.K12.SimJob.entry
#print axioms ProofFile.Honest.K12.SimJob.entry?
#print axioms ProofFile.Honest.K12.tauSim
#print axioms ProofFile.Honest.K12.zeroTextK
#print axioms ProofFile.Honest.K12.zeroText
#print axioms ProofFile.Honest.K12.restZeroText
#print axioms ProofFile.Honest.K12.restSim
#print axioms ProofFile.Honest.K12.testSims
