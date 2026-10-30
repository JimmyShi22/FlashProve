-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Row.lean: the row of a proximity test's two parts, each with
its simulator's form, and the two letters that the frame's sentences on such a row take: `On` (what
is asked at a part's entry) and `bud` (which positions may be read). Definitions only; no theorem.
General in the two jobs J and Js and in the types `S`, `Cl`, `V`, `W`, `X`, `Pb`. No property is
claimed: these are the letters of sentences that are stated in Sim/Spec.lean and proved nowhere.
(The frame's sentence at the second member at another `On` and `bud`: Sim/ExactFree.lean; at the
first member, where the fresh table has come earlier: Sim/ExactFirst.lean.) Each of these two is
stated at a state on entry that is made of the plan's public part, not shown to be the verifier's.

Under a form owed. A part's letter for the verifier's state (`TestJob.rec₀`) is handed no coin; of
columns it is handed those that the front carries on (`Seen.opened`). Whether a job's letter reads
them is not treated in this file. At a job whose letter does not read them, the clause `same` of
`OnRest` cannot be met by an honest run at the main test of the proof file (taken here to be its
last test behind the links, `piL` | `piLFull`, Johnson/Desc/K12/Law/PlacesSmall.lean |
PlacesFull.lean: by reading; no theorem): there the verifier's state holds targets that are symbols
of opened columns of the run's own messages, and such a letter takes up neither a coin nor a column.
So at every such job whatever is stated under `OnRest` is empty there until a part can hold that
state, or the clause is narrowed to what the part's text reads of it (coefficients, codes, the
layout). Of a job whose letter does read them nothing is shown here. At the last chain's own test:
not settled. The clause waits for that choice; the other clauses do not hang on it. From which
stronger pair of ties it follows: `same_of_ties` (Sim/ExactPlan.lean).

Terms. The frame is Johnson/Desc/ProofFile/Honest/Frame.lean, with Side.lean next to it. A part is a
`Part` (Frame.lean); the test's two are `firstPart`, the round "BAT" and the first fold, `firstLen`
rounds in all, and `restPart`, all other rounds (Johnson/Desc/ProofFile/Honest/K12/Parts.lean). A
simulator's form is a term of type `Sim` (Frame.lean): `firstSim` and `restSim` (Sim/Sims.lean). A
side is a `Side` (Side.lean): a description's sub-protocol (`block`) with a row. A member is a
`Member` (Side.lean): a part with its number in the row, its declared rounds and its simulator's
form. `On` and `bud` are the two last parameters of `Good` (Side.lean). A job is what a caller
supplies for its test: J, a `TestJob` (Johnson/Desc/ProofFile/Honest/K12/Test.lean), for the parts,
and Js, a `SimJob` (Sim/Sims.lean), for the simulators. The job's text is the functions that J
supplies (`rec₀`, `rows₀`, `trees₀`); the part's text is `testAll` (Test.lean), of which each move
of a part sends one round. Each job has a field `rec₀` for the state that the test is entered with,
of type `T12` (Johnson/Desc/K12/Join.lean): the part's own letter is that of J, the simulators'
letter that of Js. That state's book and count of roots are its fields `book`, a book of trees, and
`roots`. The public numbers are the field `opens` of Js. The place is the field `p` of a job (`P12`,
Johnson/Desc/K12/Frame.lean): the test's parameters, among them its place in the description and its
list of stages. A stage is a `Fmt.M1.Stage`, with its main code `C` and its mask code `Z`. The
switch number j, from 0, is the two rounds "SEND seed" and "CS" after the fold of stage number j;
tree number j is the tree that its "SEND seed" sends. A reading round is a round that samples
positions at which trees are read: each "CS", and "BASE" for the last tree; the first round of
positions is the "CS" of switch number 0. For tree number j the codes are those of stage number
j + 1, for a first fold's own table those of the first stage: r and r' are `C.r` and `Z.r` there, a
tree's range is the numbers below 2 ^ `C.a`, and the table's range those below 2 ^ `Z.a`. The points
under a code are the positions reduced modulo 2 ^ `a`, at the code's field `a`. m is a `Mid`
(Frame.lean): the state of a chain's run between two rounds, here before the second part's first
round (the part's entry). The front is what is shown before. The argument `front`, a `Before`
(Frame.lean), is what a simulator is handed; the whole front is all of it, the first part's rounds
included. The test's front, a `Front` (Johnson/Desc/ProofFile/Honest/Sum.lean), is what the
functions of J are given. What the front lists of a tree is what `Before.treeCols` (Side.lean)
returns: pairs of a position and a column. A stretch is a `Stretch`
(Johnson/Desc/ProofFile/Honest/K12/Coins.lean): a run of coins, by number. mem gives the stretches
that the second part carries (`Part.carries`), by number: those of the group's oracle messages
(`TestJob.members`), then the first fresh table's. The rows are the first stage's state (`PS`,
Johnson/Prover/Link/BodyState.lean). The first fresh table is the fields `fM` and `fT` of that state
as `TestJob.first` (Test.lean) sets them: the packing of the first fold's coefficients, and its
rows' tails. The description's own steps in front of the second part are those of `SimJob.entry?`
(Sim/Sims.lean): `front`, `bat` and `fold` of `guardedProximityTestParts` (Johnson/Desc/K12/JoinGuarded.lean), and a
question on the group between the last two. They pass single rows where the field `pass` of the
state that they return is `.single R n`.

Words. A sentence: a proposition. A letter: a free parameter, or a field that the caller fills. A
tie: a condition that relates two things. A form owed: a wording that is not settled. Empty:
vacuous. To hang on, to move with: to depend on. To hand: to give. To lay: to put or to make. Heard:
received as a challenge. Made anew: computed again. In front of, behind: before, after. A premise: a
hypothesis. Spent by a step, under (On-0): used by it.

  `testPairs`, `testSide`, `firstMember`, `restMember`: the row, as a list of two pairs; the side:
    the row with the description's own sub-protocol at the test's place, taken from a list of
    sub-protocols by `Side.seated` (Side.lean), `none` if the list has none at the place; the two
    members written out
  `OnRest`: what is asked at the second part's entry: four ties:
    (On-0) the state is there, and the front is whole. Three clauses. (A fourth that one could ask,
    "the front holds a column for every read that the rounds in front make", would be spent by no
    step beyond the first, and lies inside the letter `rec₀`.)
    `heard`: the first part's challenges, as shown in front, are those that the part's state has
    heard last, and they are as many as the first part has rounds;
    `listed`: the front lists a root for every tree that the first round of positions opens;
    `there`: the description's own steps in front of the second part accept, from the simulators'
    letter, over the first part's rounds as shown, and pass single rows. That the state's codes,
    layout, book and count of roots are the place's is asked by these steps' own guards, as their
    text is read here; no statement says so.
    (On-1) the entry's claim is true on the rows:
    `claim`: the single rows that are passed, as a statement (`stmS`, OnBytes/Slice/BlkRead.lean),
    hold of the first stage's three folded messages (`foldMsg`, Johnson/Prover/Link/FoldEnc.lean) at
    the first fold's point.
    (On-2) the front's columns are the job's trees':
    `cols`: the trees that the first round of positions opens are as many and as deep as the public
    numbers say, and every column that is listed of them in the whole front is the job's own tree's
    column there. That the job's trees hold the job's rows is no clause here: it is a premise on the
    job's text (`treesOwn`, Sim/Spec.lean).
    (On-3) in the form that waits (above):
    `same`: the state behind the first fold as the part's text makes it is the simulators'.
  `testOn`: the value for `On`, by the member's number: `OnRest` at number 1, the second part's, at
    the input's public part (`Face.pub`, Frame.lean) and at the stretches that the member's part
    carries, by number (`stretches`, Coins.lean); at every other number it asks nothing
  `seedAt`, `readAt`, `different`, `budRest`, `budFirst`, `testBud`: the numbers, among the second
    part's rounds, of the round that sends tree number j and of the round that reads it · for each
    tree that the second part sends: the positions asked lie in the tree's range, and, together with
    the positions that the part's own next reading round samples (but for the last tree), they are
    at most r different points under the main code and at most r' under the mask code · for a first
    fold's own table: at most r' points. `different` counts the different numbers in a list.
    `budFirst` also asks that the positions asked lie in the table's range. `testBud` is the value
    for `bud`, by the part's number: `budFirst` at number 0 where `Js.own` is `true`, `budRest` at
    number 1, and nothing else
  `carriedCoins`, `restFront`, `rowsAt`, `heardIn`, `partEntry`: what the second part's own moves
    make of what it is handed, at its entry: the coins that it carries, as the text reads them · the
    test's front · the first stage's state · the first part's challenges · the verifier's state
    behind the first fold as the part's text makes it (of its own letter and of the first fold's
    rounds made anew at the carried coins)

Which clauses tie a carried coin to the front: `claim` (the group's rows, the first fresh table;
against a target that the shown scalars and columns have made) · `cols` (rows, the fresh table, all
tails; against listed columns) · `same` (through the first fold's rounds made anew). Each is meant
as an identity that holds at every value of the carried coins of a real run, whose front moves with
these coins; for `same` that is refuted at the main test (above); for the two others it is shown
nowhere. No clause reads the part's own coins, a stretch that is spent, or the part's own
challenges: by the frame's type of `On`.

Limits.
- The clause `same` of `OnRest`: see "Under a form owed".
- All clauses are hypotheses of whatever is stated with them; who has to prove which is not said
  here.
- The challenges further in front than the first part's are tied by no clause of their own: the
  simulators read them through `rec₀` alone.
- `bud` reads the challenges: it relates the positions asked to the positions sampled; it is meant
  to be sufficient for the sentence that takes it, and is not meant to be necessary: neither is
  shown.
- `budRest` can shut out a list of challenges. Where, for a tree that is not the last, the part's
  own next reading round samples more than r different points under the main code, or more than r'
  under the mask code, `budRest` is `false` at every list of positions asked. That no such round
  samples more is not stated here; `Spec.budDue` (Sim/Spec.lean) takes a bound on the number of
  sampled positions as a hypothesis.
- Below two stages `budRest` is empty: it is `true` at all challenges and positions.
- `OnRest` counts the first part's rounds by `firstLen` at the stages of J, while `Js.entry?` and
  `Js.entry` cut the front by `firstLen` at the stages of Js. No clause of `OnRest` says that the
  two jobs have the same parameters: that is `PublicTies.place` (Sim/Spec.lean).
- No theorem names `OnRest`, `budRest`, `seedAt` or `readAt`: outside this file they occur in the
  propositions of Sim/Spec.lean only. `OnRest` has no value that meets it in the library.
- "The verifier's state" in this file's comments names what a job's field `rec₀` is meant to return,
  and what the description's steps make of that. That it is the verifier's state in any run is not
  shown.
- `firstMember` and `restMember` are the members as written out. That a side which `testSide`
  returns has these two as its members is not shown here: `members_of_seat` (Sim/ExactSide.lean),
  under its hypotheses.
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Sims
import Johnson.Prover.Link.FoldEnc

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)

variable {S Cl V W X Pb : Type}

/-! ## 1 The row -/

/-- The row: each part with its simulator's form. -/
def testPairs (J : TestJob W X) (Js : SimJob Pb) : List (Part V W X × Sim Pb) :=
  [(firstPart J, firstSim Js), (restPart J, restSim Js)]

/-- The side: the row with the description's own sub-protocol at the test's place: the first element
of bs whose place is `J.p.place` (`Side.seated`, Honest/Side.lean); `none` if there is none. fs: the
chain's falls (`Fall`), of which those at this place are used. -/
def testSide (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb)
    (fs : List (Fall S) := []) : Option (Side S Cl V W X Pb) :=
  Side.seated bs J.p.place (testPairs J Js) fs

/-- The first member, written out: number 0; the test's first `firstLen` declared rounds, each with
its oracle messages; the first part; its simulator's form. -/
def firstMember (J : TestJob W X) (Js : SimJob Pb) : Member V W X Pb :=
  ⟨0, J.laid.take (firstLen J.p.nums.stages), firstPart J, firstSim Js⟩

/-- The second member, written out: number 1; all the other declared rounds; the second part; its
simulator's form. -/
def restMember (J : TestJob W X) (Js : SimJob Pb) : Member V W X Pb :=
  ⟨1, J.laid.drop (firstLen J.p.nums.stages), restPart J, restSim Js⟩

/-! ## 2 What the second part's moves make of what it is handed, at its entry -/

/-- The coins that the second part carries, as its text reads them (`restCoins`), its own coins 0.
mem: the carried stretches by number. `restCoins`: Parts.lean. -/
def carriedCoins (J : TestJob W X) (mem : ℕ → Stretch) : TestCoins :=
  ⟨(mem J.members.length).e, tailsIn J.s₀ (mem J.members.length).e, mem, fun _ => 0⟩

/-- The test's front, as a move of the second part lays it at the part's entry. It is what `moveAt`
(Parts.lean) builds at the round number `firstLen`: the challenges heard and the rounds seen, each
without its last `firstLen` entries, what was handed on, and the columns `m.opened` as they are. So
whatever is made of this front (`rowsAt`, `partEntry`, the fields of `OnRest`) can depend on these
columns where a letter of the job reads them. -/
def restFront (J : TestJob W X) (m : Mid W X) : Front X :=
  let n₀ := firstLen J.p.nums.stages
  ⟨m.st.heard.take (m.st.heard.length - n₀), m.st.own, m.shown.front n₀⟩

/-- The first stage's state, of the input, the front and the carried coins. It is `TestJob.first`
(Test.lean) at `restFront` and `carriedCoins`. -/
def rowsAt (J : TestJob W X) (mem : ℕ → Stretch) (m : Mid W X) : PS :=
  J.first m.st.input (restFront J m) (carriedCoins J mem)

/-- The first part's challenges, by the round's number in the test: the last `firstLen` challenges
that the state has heard; beyond them `noDraw` (Sim/Sims.lean). -/
def heardIn (J : TestJob W X) (m : Mid W X) (i : ℕ) : Fmt.Drawn :=
  (m.st.lately (firstLen J.p.nums.stages)).getD i noDraw

/-- The verifier's state behind the first fold, as the part's text makes it: of its own letter, and
of the first fold's rounds made anew at the carried coins. `recB`: Test.lean. `aFold`, `aRec1`:
Johnson/Desc/K12/Honest/Stages.lean. -/
def partEntry (J : TestJob W X) (mem : ℕ → Stretch) (m : Mid W X) : T12 :=
  let tB := J.recB m.st.input (restFront J m) (heardIn J m 0)
  aRec1 J.p 0 J.s₀ (J.laid.drop 1) tB
    (aFold (coinsOf J.p.nums.stages (carriedCoins J mem).hide fun _ => 0) 0 J.s₀ 1 (rowsAt J mem m)
      (rowOf tB) (heardIn J m))

/-! ## 3 On -/

/-- What is asked at the second part's entry. pb: the input's public part. mem: the stretches that
the part carries, by number. m, front: as the frame's `On` takes them. -/
structure OnRest (J : TestJob W X) (Js : SimJob Pb) (pb : Pb) (mem : ℕ → Stretch) (m : Mid W X)
    (front : Before) : Prop where
  /-- (On-0) the first part's challenges, as shown, are the last that the part's state has heard -/
  heard : (lastSeen front (firstLen J.p.nums.stages)).map (·.drawn) =
      m.st.lately (firstLen J.p.nums.stages) ∧
    (lastSeen front (firstLen J.p.nums.stages)).length = firstLen J.p.nums.stages
  /-- (On-0) the front lists a root for every tree that the first round of positions opens -/
  listed : ∀ x ∈ Js.opens, (front.treeCols x.1 x.2.1).isSome = true
  /-- (On-0) the description's own steps in front of the second part accept and pass single rows -/
  there : ∃ t₁ R n, Js.entry? pb front = .ok t₁ ∧ t₁.pass = .single R n
  /-- (On-1) the entry's claim is true on the rows -/
  claim : ∀ t₁ R n, Js.entry? pb front = .ok t₁ → t₁.pass = .single R n →
    (Slf.idf (E := GE) (J := (sgOf J.s₀).cMid.J)).Holds (stmS (sgOf J.s₀) R)
      (foldMsg (sgOf J.s₀) (μOf (sgOf J.s₀) (rowsAt J mem m)) (φOf (sgOf J.s₀) (rowsAt J mem m))
        (aPoint J.s₀ 1 (heardIn J m)))
  /-- (On-2) the columns that are listed in front are the text's own trees' -/
  cols : (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m)).map (·.1) =
      Js.opens.map (·.2.2) ∧
    ∀ (i : ℕ) (x : ℕ × ℕ × ℕ) (T : Tree), Js.opens[i]? = some x →
      (J.trees₀ m.st.input (restFront J m) mem (rowsAt J mem m))[i]? = some T →
      ∀ q ∈ (front.treeCols x.1 x.2.1).getD [], q.2 = T.2 q.1
  /-- (On-3), in the form that waits: the state behind the first fold as the part's text makes it is
  the simulators' -/
  same : partEntry J mem m = Js.entry pb front

/-- On: nothing at the first part; `OnRest` at the second. φ: the chain's face. It goes by the
member's number: nothing is asked at any number but 1. ca: what the member's part carries. -/
def testOn (φ : Face V W Pb) (J : TestJob W X) (Js : SimJob Pb) (u : Member V W X Pb)
    (ca : CsAll u.part.carries) (m : Mid W X) (front : Before) : Prop :=
  u.number = 1 → OnRest J Js (φ.pub m.st.input) (stretches _ ca) m front

/-! ## 4 bud -/

/-- The number, among the second part's rounds, of "SEND seed" of switch number j, from 0. That
round sends tree number j. -/
def seedAt (stages : List Fmt.M1.Stage) (j : ℕ) : ℕ :=
  roundOf stages j + 1 + (stages.getD j default).k - firstLen stages

/-- The number, among the second part's rounds, of the round that reads the tree which switch number
j sends: "CS" of switch j + 1. -/
def readAt (stages : List Fmt.M1.Stage) (j : ℕ) : ℕ := seedAt stages (j + 1) + 1

/-- How many different numbers a list holds. -/
def different (l : List ℕ) : ℕ := l.eraseDups.length

/-- The second part's bound on the positions that may be read, an executable test. ds: the part's
challenges. asks: the positions asked, by round and by root. For each switch number j: A is the
positions asked of the tree that the switch sends; N is the positions that the round number
`readAt stages j` samples, and is empty for the last tree; `C` and `Z` are the codes of stage number
j + 1. The test: every element of A is below 2 ^ `C.a`; A ++ N reduced modulo 2 ^ `C.a` has at most
`C.r` different elements; reduced modulo 2 ^ `Z.a` it has at most `Z.r`. -/
def budRest (stages : List Fmt.M1.Stage) (ds : List Fmt.Drawn) (asks : List (List (List ℕ))) :
    Bool :=
  (List.range (stages.length - 1)).all fun j =>
    let st := stages.getD (j + 1) default
    let A := (((asks[seedAt stages j]?).getD [])[0]?).getD []
    let N := if j + 2 < stages.length then (ds.getD (readAt stages j) noDraw).poss else []
    A.all (fun x => decide (x < 2 ^ st.C.a)) &&
      decide (different ((A ++ N).map (· % 2 ^ st.C.a)) ≤ st.C.r) &&
      decide (different ((A ++ N).map (· % 2 ^ st.Z.a)) ≤ st.Z.r)

/-- The first part's, where the first fold sends its own table. A is the positions asked of the
table that the part's round number 1 sends. The test: every element of A is below 2 ^ `Z.a`, and A
has at most `Z.r` different elements; `Z` is the mask code of s. -/
def budFirst (s : Fmt.M1.Stage) (asks : List (List (List ℕ))) : Bool :=
  let A := (((asks[1]?).getD [])[0]?).getD []
  A.all (fun x => decide (x < 2 ^ s.Z.a)) && decide (different A ≤ s.Z.r)

/-- bud, by the part's number: `budFirst` at number 0 where `Js.own` is `true`; `budRest` at number
1; nothing else is asked. -/
def testBud (Js : SimJob Pb) (n : ℕ) (ds : List Fmt.Drawn) (asks : List (List (List ℕ))) : Prop :=
  (n = 0 → Js.own = true → budFirst Js.s₀ asks = true) ∧ (n = 1 → budRest Js.stages ds asks = true)

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.testPairs
#print axioms ProofFile.Honest.K12.testSide
#print axioms ProofFile.Honest.K12.firstMember
#print axioms ProofFile.Honest.K12.restMember
#print axioms ProofFile.Honest.K12.carriedCoins
#print axioms ProofFile.Honest.K12.restFront
#print axioms ProofFile.Honest.K12.rowsAt
#print axioms ProofFile.Honest.K12.heardIn
#print axioms ProofFile.Honest.K12.partEntry
#print axioms ProofFile.Honest.K12.OnRest
#print axioms ProofFile.Honest.K12.testOn
#print axioms ProofFile.Honest.K12.seedAt
#print axioms ProofFile.Honest.K12.readAt
#print axioms ProofFile.Honest.K12.different
#print axioms ProofFile.Honest.K12.budRest
#print axioms ProofFile.Honest.K12.budFirst
#print axioms ProofFile.Honest.K12.testBud
