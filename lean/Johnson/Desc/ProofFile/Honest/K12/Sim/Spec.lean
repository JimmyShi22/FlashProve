-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K12/Sim/Spec.lean: the sentences that are meant to be shown of the row
of a proximity test's two parts with their simulators' forms (Sim/Row.lean), each as a proposition
with a name. Definitions alone: not one of them is proved here or anywhere. No property is claimed.
The file also names the hypotheses that these propositions take. The types `S`, `Cl`, `V`, `W`, `X`,
`Pb` and the two jobs J and Js are free parameters.

Under a form owed: `Spec.exactRest` is empty at the main test of the proof file as long as
`OnRest`'s clause `same` stands as it does (Sim/Row.lean's head). `Spec.core` and `Spec.claimTrue`
do not read that clause. `Spec.fresh` is empty of content: under its premise both of its sides
sample the same coins alone; it holds of every part by the frame's own general law. (That law:
`fresh_of_nil` with `spentBy_nil`, Johnson/Desc/ProofFile/Honest/Law/ToyLaw.lean.)

Terms. The frame: Johnson/Desc/ProofFile/Honest/Frame.lean, and Side.lean next to it. A part is a
`Part` (Frame.lean); the test's two are `firstPart`, the round "BAT" and the first fold, and
`restPart`, all other rounds (Johnson/Desc/ProofFile/Honest/K12/Parts.lean). The row is the two
parts, each with its simulator's form (`testPairs`, Sim/Row.lean). A side is a `Side` (Side.lean): a
description's sub-protocol (`block`) with a row; `testSide` (Sim/Row.lean) takes the sub-protocol at
the test's place from a list. A member is a `Member` (Side.lean): a part with its number, its rounds
and its simulator; the first and the second member are `firstMember` and `restMember`
(Sim/Row.lean). A job is what a caller supplies for its test: a `TestJob`
(Johnson/Desc/ProofFile/Honest/K12/Test.lean) for the parts, a `SimJob` (Sim/Sims.lean) for the
simulators. The place's numbers are the test's parameters (`P12`), the field `p` of both jobs; the
plan is the public data from which a caller takes them. The group's members are the oracle messages
under test (`TestJob.members`). A stage is a `Fmt.M1.Stage`, with its main code `C`, its mask code
`Z` and its numbers `k` and `h`. The first round of positions, or first reading round, is the round
"CS" of the first switch, number `firstLen` + 1 in the test. A text is a function with values in
`BOut`: here `restText` (Sim/Text.lean) and `zeroText` (Sim/Sims.lean). The front is what is shown
before a part or a test (`Before`, Frame.lean; `Front`, Johnson/Desc/ProofFile/Honest/Sum.lean). The
book is a `ProverCoinCounts` (Frame.lean). An entry is an `Ahead`: a run of its owner's coins that one other
part, its spender, is handed, marked as spent or as carried. A stretch is a `Stretch`
(Johnson/Desc/ProofFile/Honest/K12/Coins.lean): a run of coins, by number. `On` and `bud` are the
two last parameters of `Good` (Side.lean): what is asked at a part's entry, and which positions may
be read.

Words. A sentence: a proposition. The spender's sentence: the frame's `ExactMember`. The owner's
sentence: the frame's `FreshMember`. A letter: a free parameter, or a field that the caller fills. A
premise: a hypothesis. Owed, a debt: has to be proved, and is proved nowhere. To pay: to prove. A
form owed: a wording that is not settled. Empty at a test: vacuous there. Idle: read by no term. To
stand: to be, to be stated. To lay: to put or to make. To hand: to give. In front of, behind:
before, after. Alone: only. A seat: where in a description a side or a member is placed. A kind: a
kind of sub-protocol. The law of a value: its distribution. The fresh table: the fields `fM` and
`fT` of the first stage's state, as `TestJob.first` (Test.lean) sets them: the packing of the hiding
polynomial's 2k + 1 coefficients, and its rows' tails. The riding table, the riding message: the
first fold's fresh table, sent earlier in its sender's tree. The real rows and trees: the arguments
P₀ and treesR of `restText`; the real text: `restText` at them. (On-1): the clause `claim` of
`OnRest` (Sim/Row.lean); `cols` and `same` are clauses of `OnRest` too.

The sentences. `ExactMember`, `FreshMember`, `noneSpent`
(Johnson/Desc/ProofFile/Honest/Small/Field.lean): the frame's own fields of `Good` at one member,
and a test on the book.
  `Spec.exactFirst`: the spender's sentence at the first member, written out. Where the fresh table
    came earlier it is the spender's half alone: the run that is spent is taken as uniform and apart
    from all else; that it is so is `OwnerDebt`, another kind's to pay; the run is carried behind by
    the second part
  `OwnerDebt`: the owner's sentence, with a seat: the book's entry by which the first part spends
    the 2k + 1 coefficients · the frame's `FreshMember` at the owner's member · no other entry hands
    a coin of the riding table's rows' tails to the first part or to a part in front of it · the
    entry by which the second part carries the whole message begins at the same coin. It is read by
    no sentence yet: the joint sentence of the two halves is owed
  `EndTrue`, `Spec.core`: the core, at the texts, at one letter t₁ for both sides. It is an equation
    of two texts' laws and no sentence on a simulator: t₁ and the trees in front are letters in it:
    nothing in it says that they are made of public things. If `same` is narrowed to "but for
    targets", a congruence is owed besides (what `restText` shows does not move with t₁'s targets,
    through the description's switch, batching and fold), and `EndTrue` is then asked at the
    verifier's state. What it says: over the second part's coins, what is shown of `restText` at the
    real rows and trees has the law of what is shown of `zeroText` at the columns in front: where
    the two lists of trees give the same groups at the first round of positions, the positions asked
    are within `budRest`, and at every coin the claim that is left at the real text's last stage is
    true
  `Spec.claimTrue`: that last premise, from (On-1) and from "the trees hold the rows"
  `Spec.exactRest`: the spender's sentence at the second member, written out, where the fresh table
    came earlier
  `Spec.fresh`: the owner's sentence at both members (empty: above)
  `Spec.budDue`, `Spec.budDueFirst`: the row's clause of the frame's debt on `bud`, the tie of the
    positions asked to the positions sampled being a premise that is the frame's
  `Spec.members`, `Spec.fits`: the side's members are the two that are written out; row and
    sub-protocol fit

Hypotheses, by name, and who has to prove each. All are on public letters. `Spec.exactFirst` takes
`PublicTies`, `rowsRead` and `SeatTies`; `Spec.exactRest` takes these three, `treesOwn` and
`Js.own = false`; `Spec.members` takes `SeatTies`; `Spec.fits` takes `PublicTies` and two equations
of lengths; `Spec.core` and `Spec.claimTrue` take `SizeTies`.
  `PublicTies J Js`: on the two jobs; whoever places the test has to prove it, from the plan.
    `place`: both jobs have the same parameters · `own`, `word`: both jobs and the parameters
    (`ownMask`) say the same on who sends the first fresh table · `stages`: two stages or more, each
    fits the next (`FitAll`, Johnson/Desc/K12/Honest/Stages.lean) · `short`: no stage's mask code is
    longer than its main code · `low`: h ≤ k at each stage · `room`: at each stage that is folded
    the mask code's message has room for the packing of the hiding polynomial's coefficients
  `SizeTies`: the clauses `stages`, `short`, `low` and `room` of `PublicTies`, on a list of stages
    `s :: next :: rest` that is a parameter
  `rowsRead`: on the part's job's text: the caller's rows read the carried stretches of the group's
    members alone: not the first fresh table's stretch, which the second part is handed under the
    next number and the first part spends: whoever writes the job
  `treesOwn`: on the part's job's text: the trees that the job lays for the first round of positions
    hold the job's own rows, at every input, front and carried stretches: without it `cols` ties the
    front to a mere letter: whoever writes the job. What "hold" has to say is a free parameter
    (`TreesHold`)
  `SeatTies σ J Js chain`: on the side; whoever places the test has to prove it. `laid`: the rounds
    and oracle messages of the side's sub-protocol are those that the job's parameters declare
    (`TestJob.laid`) · `plan`: that sub-protocol's field `planOk`, its test on the plan, is true ·
    `opens`: the trees that the simulators look up are the first reading round's declared openings,
    by the frame's own `srcOf` at the chain's number, each with its declared depth. `plan` reads no
    field of J or Js: `laid` is the only clause that ties the sub-protocol to a job

Limits.
- `Spec.exactFirst` and `Spec.exactRest` are `ExactMember` at a state on entry that is made of the
  plan's public part, not shown to be the verifier's: the job's state function (`TestJob.rec₀`) is a
  letter, and what the parts show is computed from it.
- The two members are made of the parts `firstPart` and `restPart` of `proverSideOfProximityTest` (Parts.lean), not
  of the guarded halves (PartsByJob.lean).
- The statements may still be false as they stand.
- `Spec.members` may be false as stated: it asks neither two stages or more nor that the place has
  as many declared rounds as the two parts have moves, both of which `members_of_seat`
  (Sim/ExactSide.lean) takes as hypotheses. No theorem reads it.
- `Spec.core` may be false as stated: `SizeTies` does not ask h = 0 and g = 0 at the last stage,
  which `FitsBody` (Johnson/LinkSim/AtText/SpecShift.lean) does; and t₁ and the two lists of trees
  are free parameters, where the theorems of Sim/CoreText.lean have one tree on each side and a t₁
  that the description's fold returns over the first fold's rounds. No theorem reads it.
- `Spec.claimTrue` may be false as stated: l and t₁ are free parameters, and no hypothesis says that
  the description's steps from the first switch on accept. Where one of them rejects, the state in
  hand is kept while the prover's state goes on. No theorem reads it.
- `OwnerDebt` asks neither that uo is one of `σo.members` nor that σo is taken off a description's
  list: `seat` ties the place and the number only, so `fresh` could be shown at a member that no
  side has. No clause ties `start` to where the owner's text reads the riding message's coins, and μ
  is read by `said` only. No theorem reads it.
- Where `claimAtEnd` (Sim/Text.lean) finds no stage or no claim, `EndTrue` reads 0 + 0 = 0: it
  holds there whatever the prover's state is.
- That the file compiles shows that the statements are well-typed over the frame's definitions, and
  nothing more.
- `TreesHold` is a letter of `Spec.claimTrue`: what "the trees hold the rows" has to say at a group
  of any layout is not worded here. It is a parameter of `treesOwn` and `Spec.exactRest` too.
- Where the first fold sends its own table: `Spec.exactRest` is not stated; `Spec.exactFirst` is,
  and leans on `rowsRead` for "the summand reads no coin of the part's own". The Lean does not bear
  that out: `firstPart` (Parts.lean) gives `rows₀` the carried stretches only, never a coin of its
  own, so it is not `rowsRead` that keeps the part's own coins out of the rows. `exact_first_own`
  (Sim/ExactFirstOwn.lean) does not take it, and takes `J.s₀.Z.a ≤ 32` (`FirstPubOwn.points`), which
  is no clause of `PublicTies`: what is proved there is not `Spec.exactFirst`.
- No premise is shown met at any policy file. `rowsRead` holds at the job of every `ManyJob`
  (`rowsRead_many`, Sim/ExactFirstAtU.lean); that such a job is played is not shown.
- In `Spec.fits` two of the three tests of `Side.fits` (Side.lean), the two on lengths, are
  hypotheses.
- No thin set of challenges is shut out: none is known to be needed but a seed's factor 0, which the
  text answers as 1. (That answer: `orOne`, Johnson/Desc/K12/Honest/Fold.lean.)
- Nothing on completeness or on soundness.
-/
import Johnson.Desc.ProofFile.Honest.K12.Sim.Row
import Johnson.Desc.ProofFile.Honest.Small.Field

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12
open OnBytes OnBytes.Params OnBytes.Slice Cb
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.Prover.Link
open H2K.Pub (sgOf)
open ProofFile.Honest.Small (ExactMember FreshMember noneSpent)

variable {S Cl V W X Pb : Type}

/-! ## 1 The public hypotheses -/

/-- What is asked of the two jobs' public letters. The clauses read the fields `p` and `fresh` of J
and `p` and `own` of Js, and no other field. -/
structure PublicTies (J : TestJob W X) (Js : SimJob Pb) : Prop where
  place : Js.p = J.p
  own : Js.own = J.fresh.isNone
  word : J.freshFits = true
  stages : ∃ s next rest, J.p.nums.stages = s :: next :: rest ∧ FitAll s (next :: rest)
  short : ∀ st ∈ J.p.nums.stages, st.Z.a ≤ st.C.a
  low : ∀ st ∈ J.p.nums.stages, st.h ≤ st.k
  room : ∀ st ∈ J.p.nums.stages.dropLast, (sgOf st).h + 2 * (sgOf st).g + 1 ≤ (sgOf st).Z.l

/-- The caller's rows read the carried stretches of the group's members alone. As stated: `rows₀`
returns the same state at two families of stretches that agree at every number below
`J.members.length`. -/
def rowsRead (J : TestJob W X) : Prop :=
  ∀ w fr (mem mem' : ℕ → Stretch), (∀ i, i < J.members.length → mem i = mem' i) →
    J.rows₀ w fr mem = J.rows₀ w fr mem'

/-- **The job's trees hold the job's rows**: at every input, front and carried stretches: a premise
on the job's text, which picks among no coins. TreesHold: a letter: what "hold" has to say. -/
def treesOwn (TreesHold : Fmt.M1.Stage → PS → List Tree → Prop) (J : TestJob W X) : Prop :=
  ∀ w fr (C : TestCoins), TreesHold J.s₀ (J.first w fr C) (J.trees₀ w fr C.mem (J.first w fr C))

/-- What is asked of the seat: of a side σ and the two jobs. chain: the chain's number, from 0, as
the frame's `srcOf` takes it. -/
structure SeatTies (σ : Side S Cl V W X Pb) (J : TestJob W X) (Js : SimJob Pb) (chain : ℕ) :
    Prop where
  laid : σ.block.rounds.zip σ.block.oracles = J.laid
  plan : σ.block.planOk = true
  opens : Js.opens = ((J.laid.getD (firstLen J.p.nums.stages + 1) default).1.opens.map fun o =>
    ((srcOf chain o.2).1, (srcOf chain o.2).2, o.1.a))

/-! ## 2 The members, and that row and sub-protocol fit -/

/-- The side's members are the two that are written out (`firstMember`, `restMember`), at every side
that `testSide` returns and that meets `SeatTies`. -/
def Spec.members (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb) (chain : ℕ) : Prop :=
  ∀ σ : Side S Cl V W X Pb, testSide bs J Js = some σ → SeatTies σ J Js chain →
    σ.members = [firstMember J Js, restMember J Js]

/-- Row and sub-protocol fit (`Side.fits`). Two of that test's three conjuncts, the two on lengths,
are hypotheses here; the third says that each simulator names its part's address. -/
def Spec.fits (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb) : Prop :=
  ∀ σ : Side S Cl V W X Pb, testSide bs J Js = some σ → PublicTies J Js →
    σ.half.rounds = σ.block.rounds.length →
    σ.block.oracles.length = σ.block.rounds.length → σ.fits = true

/-! ## 3 The first member -/

/-- **The spender's sentence at the first member, written out.** It is the frame's `ExactMember` at
`firstMember J Js`, with `testOn` for `On` and `testBud` for `bud`, at a state on entry that is made
of the plan's public part, not shown to be the verifier's. chain, firstTree: the chain's number,
from 0, and the number in the label of its first own tree, as the frame's `readsOf` takes them. -/
def Spec.exactFirst (φ : Face V W Pb) (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb)
    (chain firstTree : ℕ) : Prop :=
  ∀ σ : Side S Cl V W X Pb, testSide bs J Js = some σ → PublicTies J Js → rowsRead J →
    SeatTies σ J Js chain →
    ExactMember φ σ chain firstTree (testOn φ J Js) (testBud Js) (firstMember J Js)

/-- **What the first member's sentence is worth nothing without, where the fresh table came earlier:
the owner's sentence, and three clauses on the book.** o, μ: the sender's part and the riding
message's number, as the job says them. σo, uo, budo: the owner's side, member and bound. start: the
riding message's first coin among the owner's. The fields `said` and `seat`: the job's field `fresh`
is (o, μ); the address of uo in σo is o. What no clause asks: that `start` is that coin; that uo is
one of `σo.members`; that σo is taken off a description's list. μ is read by `said` only. -/
structure OwnerDebt {So Clo Xo : Type} (φ : Face V W Pb) (J : TestJob W X) (Bk : ProverCoinCounts)
    (ord : List VerifiableInference.Desc.Place) (o : Addr) (μ : ℕ) (σo : Side So Clo V W Xo Pb)
    (uo : Member V W Xo Pb) (budo : ℕ → List Fmt.Drawn → List (List (List ℕ)) → Prop)
    (start : Due) : Prop where
  said : J.fresh = some (o, μ)
  seat : (⟨σo.block.place, uo.number⟩ : Addr) = o
  /-- the entry by which the first part spends the coefficients -/
  spent : (⟨(spentRun J).1, o, start, (spentRun J).2, ⟨J.p.place, 0⟩, true⟩ : Ahead) ∈ Bk.ahead
  /-- the entry by which the second part carries the whole message begins at the same coin -/
  carried : (⟨(freshRun J).1, o, start, (freshRun J).2, ⟨J.p.place, 1⟩, false⟩ : Ahead) ∈ Bk.ahead
  /-- the frame's own sentence at the owner's member -/
  fresh : FreshMember φ σo Bk ord budo uo
  /-- no other entry hands a coin of the riding table's rows' tails to the first part or to a part
  in front of it -/
  tails : ∀ e ∈ Bk.knownBy ord o ⟨J.p.place, 0⟩,
    e.start.e + e.count.e ≤ start.e + (2 * J.s₀.k + 1) ∨ start.e + dueFresh J.s₀ ≤ e.start.e

/-! ## 4 The second member -/

/-- The claim that is left at the last stage is true at the prover's last message. e: the values at
the last stage (`EndAt`, Sim/Text.lean). The claim is `claimAtEnd p e`; the message is `μOf` at the
state `e.P`. Where `claimAtEnd` finds no stage or no claim it returns a claim without a coefficient
and with the target 0: the equation then reads 0 + 0 = 0 and holds whatever the state is. -/
def EndTrue (p : P12) (e : EndAt) : Prop :=
  formG (sgOf e.cur).C.l (claimAtEnd p e).c (mainOf (sgOf e.cur) (μOf (sgOf e.cur) e.P)) +
      formG (sgOf e.cur).Z.l (claimAtEnd p e).d (maskOf (sgOf e.cur) (μOf (sgOf e.cur) e.P)) =
    toE (claimAtEnd p e).tau

/-- The sizes that `Spec.core` and `Spec.claimTrue` ask of a list of stages: as in `PublicTies`. -/
structure SizeTies (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) : Prop where
  fit : FitAll s (next :: rest)
  short : ∀ st ∈ s :: next :: rest, st.Z.a ≤ st.C.a
  low : ∀ st ∈ s :: next :: rest, st.h ≤ st.k
  room : ∀ st ∈ (s :: next :: rest).dropLast,
    (sgOf st).h + 2 * (sgOf st).g + 1 ≤ (sgOf st).Z.l

/-- **The core, at the texts, at one letter t₁ for both sides.** An equation of two texts' laws; no
sentence on a simulator: t₁ and treesF are letters: nothing here says that they are made of public
things. hide: the first fold's coefficients (idle: `restText_congr`). P₀, treesR: the first stage's
state, and the trees that the part's text lays for the first round of positions. treesF: the trees
that are made of the columns in front. dep: the depth of the tree that a round sends, by the round's
number from the first switch on. ds: the challenges from the first switch on, as `budRest` reads
them; D: all the test's, by number. -/
def Spec.core : Prop :=
  ∀ (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (t₁ : T12) (P₀ : PS)
    (hide : ℕ → GE) (treesR treesF : List Tree) (D : ℕ → Fmt.Drawn) (ds : List Fmt.Drawn)
    (dep : ℕ → Option ℕ) (asks : List (List (List ℕ))),
    SizeTies s next rest →
    (∀ i, D (firstLen (s :: next :: rest) + i) = ds.getD i noDraw) →
    aGroups s 1 treesF D = aGroups s 1 treesR D →
    budRest (s :: next :: rest) ds asks = true →
    (∀ c : Cs ⟨0, dueRest (s :: next :: rest)⟩, EndTrue p
      (restEnd p (coinsOf (s :: next :: rest) hide (stretchOf c).e) s next rest l 1 t₁ P₀ treesR
        D)) →
    (Prob.unif (Cs ⟨0, dueRest (s :: next :: rest)⟩)).map (fun c =>
        let O := restText p (coinsOf (s :: next :: rest) hide (stretchOf c).e) s next rest l 1 t₁ P₀
          treesR D
        shownFrom O dep O.rs.length asks) =
      (Prob.unif (Cs ⟨0, dueRest (s :: next :: rest)⟩)).map fun c =>
        let O := zeroText p s next rest l t₁ treesF (stretchOf c).e D
        shownFrom O dep O.rs.length asks

/-- **The claim that is left at the real text's last stage is true at every coin**: from (On-1) at
the state behind the first fold, and from "the trees hold the rows". TreesHold: a letter: what the
second has to say. l and t₁ are free parameters, and no hypothesis says that the description's steps
from the first switch on accept: it may be false as stated; no theorem reads it. -/
def Spec.claimTrue (TreesHold : Fmt.M1.Stage → PS → List Tree → Prop) : Prop :=
  ∀ (p : P12) (s next : Fmt.M1.Stage) (rest : List Fmt.M1.Stage) (l : Laid) (t₁ : T12)
    (R : SingleRows) (n : ℕ) (P₀ : PS) (K : BCoins) (trees : List Tree) (D : ℕ → Fmt.Drawn),
    SizeTies s next rest → t₁.pass = .single R n →
    (Slf.idf (E := GE) (J := (sgOf s).cMid.J)).Holds (stmS (sgOf s) R)
      (foldMsg (sgOf s) (μOf (sgOf s) P₀) (φOf (sgOf s) P₀) (aPoint s 1 D)) →
    TreesHold s P₀ trees → EndTrue p (restEnd p K s next rest l 1 t₁ P₀ trees D)

/-- **The spender's sentence at the second member, written out, where the fresh table came
earlier.** It is the frame's `ExactMember` at `restMember J Js`, with `testOn` for `On` and
`testBud` for `bud`, at a state on entry that is made of the plan's public part, not shown to be the
verifier's. It is empty at the main test of the proof file as long as `OnRest`'s clause `same`
stands as it does (Sim/Row.lean's head). -/
def Spec.exactRest (TreesHold : Fmt.M1.Stage → PS → List Tree → Prop) (φ : Face V W Pb)
    (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb) (chain firstTree : ℕ) : Prop :=
  ∀ σ : Side S Cl V W X Pb, testSide bs J Js = some σ → PublicTies J Js → rowsRead J →
    treesOwn TreesHold J → SeatTies σ J Js chain → Js.own = false →
    ExactMember φ σ chain firstTree (testOn φ J Js) (testBud Js) (restMember J Js)

/-! ## 5 The owner's sentence at this row; bud -/

/-- **The owner's sentence at both members**, where no entry that is spent names one of them as its
owner. Empty of content. -/
def Spec.fresh (φ : Face V W Pb) (bs : List (Block S Cl)) (J : TestJob W X) (Js : SimJob Pb)
    (Bk : ProverCoinCounts) (ord : List VerifiableInference.Desc.Place) : Prop :=
  ∀ σ : Side S Cl V W X Pb, testSide bs J Js = some σ →
    noneSpent Bk ⟨J.p.place, 0⟩ = true → noneSpent Bk ⟨J.p.place, 1⟩ = true →
    FreshMember φ σ Bk ord (testBud Js) (firstMember J Js) ∧
      FreshMember φ σ Bk ord (testBud Js) (restMember J Js)

/-- **bud at what a run's own rounds read**: where, for each tree that the second part sends but the
last, the positions asked are just those that the part's own next reading round samples, in the
tree's range, and for the last tree those that "BASE" samples; each such list has at most as many
positions as the stage's two codes have entries of encoding randomness; and no stage's mask code is
longer than its main code. -/
def Spec.budDue (Js : SimJob Pb) : Prop :=
  ∀ (ds : List Fmt.Drawn) (asks : List (List (List ℕ))),
    (∀ st ∈ Js.stages, st.Z.a ≤ st.C.a) →
    (∀ j, j + 1 < Js.stages.length →
      (((asks[seedAt Js.stages j]?).getD [])[0]?).getD [] =
        Fmt.listOf (((ds.getD (if j + 2 < Js.stages.length then readAt Js.stages j
          else seedAt Js.stages j + 3) noDraw).poss).map
            (· % 2 ^ (Js.stages.getD (j + 1) default).C.a))) →
    (∀ j, j + 1 < Js.stages.length →
      (ds.getD (if j + 2 < Js.stages.length then readAt Js.stages j
        else seedAt Js.stages j + 3) noDraw).poss.length ≤
          min (Js.stages.getD (j + 1) default).C.r (Js.stages.getD (j + 1) default).Z.r) →
    budRest Js.stages ds asks = true

/-- The same for a first fold's own table. poss: the positions that the first reading round, which
is the second part's, samples. -/
def Spec.budDueFirst (Js : SimJob Pb) : Prop :=
  ∀ (poss : List ℕ) (asks : List (List (List ℕ))),
    (((asks[1]?).getD [])[0]?).getD [] = Fmt.listOf (poss.map (· % 2 ^ Js.s₀.Z.a)) →
    poss.length ≤ Js.s₀.Z.r → budFirst Js.s₀ asks = true

end ProofFile.Honest.K12

#print axioms ProofFile.Honest.K12.PublicTies
#print axioms ProofFile.Honest.K12.rowsRead
#print axioms ProofFile.Honest.K12.treesOwn
#print axioms ProofFile.Honest.K12.SeatTies
#print axioms ProofFile.Honest.K12.Spec.members
#print axioms ProofFile.Honest.K12.Spec.fits
#print axioms ProofFile.Honest.K12.Spec.exactFirst
#print axioms ProofFile.Honest.K12.OwnerDebt
#print axioms ProofFile.Honest.K12.EndTrue
#print axioms ProofFile.Honest.K12.SizeTies
#print axioms ProofFile.Honest.K12.Spec.core
#print axioms ProofFile.Honest.K12.Spec.claimTrue
#print axioms ProofFile.Honest.K12.Spec.exactRest
#print axioms ProofFile.Honest.K12.Spec.fresh
#print axioms ProofFile.Honest.K12.Spec.budDue
#print axioms ProofFile.Honest.K12.Spec.budDueFirst
