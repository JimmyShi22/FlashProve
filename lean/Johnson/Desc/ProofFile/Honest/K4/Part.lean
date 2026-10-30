-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K4/Part.lean: the honest side of the kind "the layers' own rounds"
(K4), in the form of Honest/Frame.lean and Honest/Side.lean. The kind's own text does not hold what
the prover sends (Johnson/Desc/First/K4/Block.lean): this file holds it, up to one public parameter
(`look`), for which Honest/K4/Look.lean has a text (`k4LookAt`). Definitions with code, and one
equation between two names.

NOT SHOWN HERE.
  * Nothing here holds a summand against the verifier's text. Tests beside this file (no part of
    the library yet) do, at fixed synthetic data at one small plan: ToyCube*.lean play each sort of
    part against the function that hears it; Toy2.lean plays the row `k4RowIn` against K4's own
    sub-protocol and values the claims that the sub-protocol leaves.
  * WHAT TIES THE ROW TO A REAL DESCRIPTION IS EVALUATED BY NOTHING: `k4PubOf`, `k4Half`, `k4HLot`,
    `k4Tokens` stand by reading alone: that "‹segment›.2.call" is the step of K4's stretch, so that
    `r0` is the number of rounds in front of the place; the segment's number; the tokens.
  * `k4Shapes` types the seven calls' numbers a second time beside the verifier's table of rounds
    (OnBytes/Desc/First/K4/Rounds.lean); what holds the two together is a test's line at one plan.
  * NO MOVE RETURNS AN ERROR, AND A MOVE MAY PAD IN SILENCE. Every summand's maker yields an
    option. Where it yields nothing, where its lists have other lengths than the call states, or
    where a shown round lacks, the part sends its mask entries over zeros or over values of no
    meaning. WHAT STANDS AGAINST THAT IS ONE PUBLIC TEST WITH CODE, `k4Fits`, OF FOUR: `k4TableFits`
    (the row's cut and counts are those of the verifier's table of rounds), `k4LookFits` (what the
    lookup has sampled has the layout's sizes), `k4TokensFit` (the request's tokens are as many as
    the plan says, each below the size of the vocabulary) and `k4MakersFit` (at the zero input and
    the zero challenges in front of its part every maker returns a job of its call's shape, and each
    claim that the merge joins has the sizes that the weights' layout asks; dear: all the makers'
    work; not measured). `k4Side` is none where `k4Fits` is false. `k4HLot`, which is handed neither
    a challenge nor a request, asks `k4TableFits` alone and lays no half where that is false.
    EVERY STATEMENT ON WHAT THE VERIFIER ACCEPTS OF THESE PARTS, OR ON WHAT THEIR MESSAGES ARE
    WORTH, IS TO TAKE `k4Fits` AS A NAMED HYPOTHESIS. The statements of exact and fresh
    (`Good.exact`, `Good.fresh`, Honest/Side.lean) at one part by itself (Honest/K4/Law/ExactFresh/)
    take their own named public hypotheses and are stated at shapes that
    do not fit too.
    THAT `k4Fits` GIVES «EVERY MAKER RETURNS A JOB OF ITS CALL's SHAPE AT A RUN's OWN INPUT AND
    CHALLENGES» IS NOT SHOWN IN THIS FILE. Two statements to that end stand in the folder
    Honest/K4/Law/, among statements on these parts: `k4MakersAt_skel`
    (MakersAt.lean): the clauses of `k4MakersFit` give one answer at two inputs and two lists of
    sampled values that agree in what its hypotheses name: in the first group the tokens' number,
    and whether one lies beyond the vocabulary; the sampled values' lengths; the lookup's public
    numbers; `k4Makers_run` (PtsFullOf.lean): so where `k4MakersFit` is true its clauses hold at a
    run, under hypotheses on the shape of K4's own challenges in front of each part, on what the
    lookup has sampled, and on the tokens. THE TEXT DOES BRANCH ON SAMPLED VALUES: whether a point's
    token coordinates are all 0 or 1 (`cornerOf`, `fewOf`, Johnson/Desc/K4/Honest/Cells.lean),
    whether a coefficient is 0 (`StackData.val`, Stack.lean; Units.lean). By reading, these arms
    choose the road by which a VALUE is reckoned, and no test: at a family with a named point
    `Reads.has` reads names, lengths and public numbers alone (`wtsFit`); at the three families on
    the lookup's planes it asks the verifier's own function for the weights; the test in
    `StackData.val` is on every entry, whatever its coefficient (`affFits`). ONE TEST OF A MAKER
    DOES COMPARE VALUES: `jobTermsOn` (Johnson/Desc/K4/Honest/Terms.lean) yields nothing where a
    product's weight is not the same at all tokens; by reading, the weights are made of public
    numbers and of what the lookup has sampled alone (`tripsOf`, Sides.lean; `panelT`,
    OnBytes/Model/LayerPanels.lean) and are the same at every token. At the zero challenges at which
    `k4MakersFit` asks, every point of K4's own is such a corner; and `k4JobFits` counts a job's end
    values at challenges 0.
  * ONE JOB READS THE ROUNDS SHOWN IN FRONT OF ITS PART BY A ROUND's NUMBER (`k4SentAt`). Where
    fewer rounds have been shown it reads an empty list, and no move says so. A statement's
    hypothesis on a state is to hold that as many rounds have been shown as challenges have been
    heard.
  * EVERY VALUE THAT THE PARTS READ OF THE CHALLENGES IS READ BY ITS NUMBER, counted from
    `K4Pub.r0`. With another number of rounds in front these numbers would name other rounds, and no
    move would say so; a challenge that holds fewer elements than its round samples reads as 0, as
    an empty list of powers, or as a point that is too short. A statement's hypothesis on a state is
    to hold that the challenges heard have the shape of the chain's rounds. `k4Side` is none unless
    the rounds in front of the place in the chain's own list are as many as `r0`, and the rounds of
    the sub-protocol at the place are the entries of the verifier's table at the plan; `k4HLot` is
    handed no such list.
  * Nothing is said of `Good` (Honest/Side.lean) at this side. The simulators are data.

What is sent (docs/format/11-2-feed-forward-segment.md, steps 2 to 16). The rounds are those of the
verifier's own table. The row has 19 parts in the first group of layers and 17 in every other:
  seven masked sumchecks, each one part: the squares' product layer; the two sumchecks over the
  tokens; the batched inner products; the two product layers of the gated products; the merge of the
  claims on the weights. Their moves are `sumPart`'s (Honest/Sum.lean); what is summed is laid by
  the files of Johnson/Desc/K4/Honest/;
  rounds "BAT-sigma" whose message holds hidden scalars, each sent as the value plus a mask entry:
  the sums of limb products; the row products; and, in the first group alone, the embedding's value;
  rounds in which nothing is sent: 9 in the first group, 8 in every other.

The coins. No part takes a coin of its own, and none carries one. A part spends runs: stretches of
another part's coins, each by a name and a count (`Part.spends`, Honest/Frame.lean). By the format's
page every scalar that is sent has a number in the segment, and the segment's mask row has an entry
under each number: so a part spends as many entries as it sends scalars. HOW AN ENTRY IS USED
DIFFERS: a lone scalar and a claimed sum are sent as value + entry; an end value as value + beta
times entry; the entries under a sumcheck's other numbers are its hiding polynomial's coefficients,
and each of these scalars is made of many of them. One exception to the count: the merge's end value
is laid under an entry of the index-mask message, and the mask row's entry under that scalar's own
number is spent by nobody. HERE EACH RUN HAS A NAME AND A COUNT ALONE: which entries they are is the
book's to say (`ProverCoinCounts`, Honest/Frame.lean).
ONE SUMMAND READS WHAT WAS SENT. The batched inner products have, as factors, the end values of the
second sumcheck over the tokens AS THEY WERE SENT. The job reads them off the rounds shown in front
of the part (`Front.seen`, Honest/Sum.lean).
By the format's numbering the entries under these end values and the entries that the batched
sumcheck spends are apart (the numbers run on without a gap); what holds that in code are two of
the book's tests ("a coin stands in two entries that spend it"; "a coin that a part spends is handed
to a part in front of it, or to itself as carried"; `ProverCoinCounts.word`, Honest/Frame.lean); nothing here
does.
The stops. None of either sort. THAT IS NOT TO SAY THAT THE VERIFIER ACCEPTS AT EVERY LIST OF
CHALLENGES: see the next paragraph.
The verifier's tests on sampled values. `hear` has three. One rejects if the element that joins the
second token sumcheck's hiding polynomial to its claim was sampled as 0 ("coin-zero"); the
sub-protocol's acceptance is owed outside that event alone. The prover plays on there: its moves
divide by no sampled value.
`k4CoinZero` is that test as a function of K4's own challenges; `k4Fall` lays it as a fall (`Fall`,
Honest/Side.lean) at K4's own member. The second compares the ends of the lookup's points with each
other and reads nothing of K4's own. The third reads a sampled point and tests an equation that
holds at every point. One more test of K4's text, "free-slot", runs behind the segment's batching,
in a member without a round: `k4FreeSlotFall` lays it as a fall at that member. What is read of the
input: see `k4Wit`.

  `k4Place`, `k4Addr`          the place; a part's address
  `k4Quiet`, `k4Scalars`, `k4Sum`, `k4SentAt`, `k4TermsEnds`, `k4SumSeen`   the sorts of part
  `K4Sort`, `k4Shapes`, `k4Sorts`, `k4RowIn`   the row at the small input
  `k4TableFits`, `k4JobFits`, `k4ZeroOwn`, `k4ZeroIn`, `k4ZeroHeard`, `k4ZeroPts`, `k4MakersFit`,
  `k4LookFits`, `k4TokensFit`, `k4Fits`
                               the public test: do the public data fit these parts
  `k4Owner`, `k4Wit`, `k4Row`, `k4Half`   whose a matrix is; the small input, of the input; the row
                               seated; at its place
  `k4ReadsHeard`                the reads' entries, of the input and the challenges heard
  `k4Tokens`, `k4PubOf`, `k4HLot`, `k4HLot_name`   under the name of K4's lot (`HLot`,
                               Honest/Frame.lean; `k4Lot`, Johnson/Desc/ProofFile/Lot/K4.lean)
  `k4Sims`, `k4Sided`, `k4Side`   a simulator beside each part; the side (`Side`, Honest/Side.lean)
  `k4CoinZero`, `k4CoinZeroShare`, `k4Fall`   the verifier's test on a sampled value; a stated
                               share; the fall
  `k4FreeSlotFall`              K4's test behind the batching, as a fall at the member where it runs

Limits. `look` IS A PARAMETER: the function that makes, of the challenges heard in front of the
place, the lookup's sampled values as `Forest.Heard` holds them. It is public: it reads no input.
Honest/K4/Look.lean has a text for it (`k4LookAt`); NOTHING HERE TIES THE PARAMETER TO THAT TEXT.
`cells` and `weights`, the readers of witness and index, are parameters too, as the frame asks.
Nothing on any property.
No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.ForKinds
import Johnson.Desc.ProofFile.Honest.K4.CubeJob
import Johnson.Desc.ProofFile.Lot.K4
import Johnson.Desc.K4.Honest.Norms
import Johnson.Desc.K4.Honest.Terms
import Johnson.Desc.K4.Honest.Stack
import Johnson.Desc.K4.Honest.Gated
import Johnson.Desc.K4.Honest.Merge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (ledNS ledNP ledNO)
open OnBytes.Model.Layer (nEndT)
open OnBytes.Desc.First.K4.Honest
open VerifiableInference.Desc (Place Block)
open VerifiableInference.Desc.Part.MaskedSum (Call)

/-- The kind's place. -/
def k4Place (Q : K4Pub) : Place := ⟨1, some Q.link, Q.piece, .K4⟩

/-- The address of the row's part number i, from 0. -/
def k4Addr (Q : K4Pub) (i : Nat) : Addr := ⟨k4Place Q, i⟩

/-! ## The sorts of part, at the small input -/

/-- A round in which nothing is sent. -/
def k4Quiet : Part Unit K4In Unit := quietPart

/-- A round whose message holds n hidden scalars, each plus its mask entry. i: the part's number. -/
def k4Scalars (Q : K4Pub) (n : Nat) (f : K4Pub → K4In → Pts → List E) (i : Nat) :
    Part Unit K4In Unit :=
  scalarsPart (runName maskRowRun (k4Addr Q i) "scalars") n fun w fr => f Q w (ptsOf Q w fr.heard)

/-- A masked sumcheck. endOwner: whose message holds the end values' mask entries. -/
def k4Sum (Q : K4Pub) (shape : Call) (endOwner : String)
    (job : K4Pub → K4In → Pts → Option Job) (i : Nat) : Part Unit K4In Unit :=
  sumPart (runName maskRowRun (k4Addr Q i) "sum") (runName endOwner (k4Addr Q i) "ends")
    (k4SumJob shape fun w fr => job Q w (ptsOf Q w fr.heard))

/-- The elements that round number i of a list of shown rounds holds. The empty array where the list
has no such round; an item that is no element of the extension field is left out: neither with a
word. -/
def k4SentAt (rv : List Fmt.RoundView) (i : Nat) : Array E :=
  (((rv[i]?).map (·.vals)).getD []).toArray.filterMap fun
    | .e x => some (E.ofTriple x)
    | _ => none

/-- The number, in the first chain, of the round that holds the second token sumcheck's end
values. -/
def k4TermsEnds (Q : K4Pub) : Nat := Q.r0 + (starts Q).getD 2 0 + Q.P.y.h.lt + 2

/-- The masked sumcheck whose summand holds the second token sumcheck's end values as sent. -/
def k4SumSeen (Q : K4Pub) (shape : Call)
    (job : K4Pub → K4In → Pts → Array E → Option Job) (i : Nat) : Part Unit K4In Unit :=
  sumPart (runName maskRowRun (k4Addr Q i) "sum") (runName maskRowRun (k4Addr Q i) "ends")
    (k4SumJob shape fun w fr =>
      job Q w (ptsOf Q w fr.heard) (k4SentAt fr.seen.rounds (k4TermsEnds Q)))

/-! ## The row -/

/-- One sort of part: how the part is made of its number; a simulator beside it, of its number. -/
structure K4Sort (Pb : Type) where
  part : Nat → Part Unit K4In Unit
  sim : Nat → Sim Pb

variable {Pb : Type}

/-- The seven calls' public shapes. The numbers are those of the verifier's table of rounds, typed a
second time. -/
def k4Shapes (Q : K4Pub) : List Call :=
  let P := Q.P
  let y := P.y
  let h := y.h
  let e0 := if Q.g == 0 then 1 else 0
  [k4LevelShape P.rd.muV,
   k4TokenShape h.lt 2 (ledNO h.xl * y.NI),
   k4TokenShape h.lt 1 (nEndT y),
   k4PlainShape Q.hp.lamS 2 (2 + (1 + y.LamM) + (Q.hp.NCL - e0)),
   k4LevelShape P.rd.muH,
   k4LevelShape P.rd.muH2,
   k4PlainShape P.wsLay.lk 1 1]

/-- **The row's sorts, in order.** -/
def k4Sorts (Q : K4Pub) : List (K4Sort Pb) :=
  let y := Q.P.y
  let h := y.h
  let first := Q.g == 0
  let sh (k : Nat) : Call := (k4Shapes Q).getD k ⟨0, [], none⟩
  let quiet : K4Sort Pb := ⟨fun _ => k4Quiet, fun i => quietSim (k4Addr Q i)⟩
  let scal (n : Nat) (f : K4Pub → K4In → Pts → List E) : K4Sort Pb :=
    ⟨k4Scalars Q n f, fun i => scalarsSim (k4Addr Q i) n⟩
  let sum (k : Nat) (owner : String) (job : K4Pub → K4In → Pts → Option Job) : K4Sort Pb :=
    ⟨k4Sum Q (sh k) owner job, fun i => sumSim (k4Addr Q i) (sh k)⟩
  [quiet] ++ (if first then [quiet, quiet] else []) ++
  [scal (ledNS h.xl * y.NI) wSums, quiet, sum 0 maskRowRun jobSquares, quiet,
   scal (ledNP h.xl * y.NI) rowProducts, sum 1 maskRowRun jobRows,
   sum 2 maskRowRun jobTerms, quiet,
   ⟨k4SumSeen Q (sh 3) jobStack, fun i => sumSim (k4Addr Q i) (sh 3)⟩,
   sum 4 maskRowRun jobGated, quiet, quiet, sum 5 maskRowRun jobGated2, quiet,
   (if first then scal 1 (fun Q w p => [embValue Q w p]) else quiet),
   sum 6 indexMaskRun jobMerge]

variable {W₀ Rc Xi Tr X : Type}

/-- **The row at the small input** (`K4In`), before it is seated in the chain's input. -/
def k4RowIn (Q : K4Pub) : List (Part Unit K4In Unit) :=
  (k4Sorts (Pb := Unit) Q).zipIdx.map fun s => s.1.part s.2

/-! ## Do the public data fit these parts: the public test -/

/-- A list of numbers, added up stretch by stretch. -/
def k4SumsBy : List Nat → List Nat → List Nat
  | _, [] => []
  | l, k :: ks => (l.take k).foldl (· + ·) 0 :: k4SumsBy (l.drop k) ks

/-- **The row is cut and counted as the verifier's table of rounds is.** K4 covers the plan; the
table has seven masked sumchecks, and as many rounds of the three other names by whose ordinals the
sampled values are found (`ptsOf`) as are read; the plan has this group's list of matrices, and each
matrix of it that an earlier sub-proof has committed to names an earlier group and a matrix of that
group's list (`k4Owner` reads the cells there); the round that holds the second token sumcheck's end
values stands in front of the batched sumcheck's first; each part has as many moves as the table's
cut gives it rounds; and each part spends as many coins as the table has the prover send elements in
these rounds. It reads public numbers alone, and is cheap. The clauses behind the first hold what is
typed here a second time (`k4Shapes`; the ordinals; how an owner is named) against the verifier's
table and plan in hand; no plan is known at which they are false, and a test beside this file
shows the first clause alone to be false at a plan. -/
def k4TableFits (Q : K4Pub) : Bool :=
  let row := k4RowIn Q
  OnBytes.Desc.First.K4.covers Q.P &&
    (starts Q).length == 7 && (k4Shapes Q).length == 7 &&
    (rowsNamed Q .zero).length == (if Q.g == 0 then 3 else 1) &&
    (rowsNamed Q .batSigma).length == 4 && (rowsNamed Q .join).length == 2 &&
    decide (Q.g < Q.P.tails.size) &&
    ((Q.P.tails.getD Q.g {}).mats.all fun M =>
      M.kind != 1 || (decide (256 ≤ M.aId) && decide (M.aId / 256 - 1 < Q.g) &&
        decide (M.aId % 256 < (Q.P.tails.getD (M.aId / 256 - 1) {}).mats.size))) &&
    decide ((starts Q).getD 2 0 + Q.P.y.h.lt + 2 < (starts Q).getD 3 0) &&
    row.map (·.moves.length) == cutOf Q &&
    row.map (fun p => (p.spends.map (·.2.e)).foldl (· + ·) 0) ==
      k4SumsBy ((OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).map (·.sent)) (cutOf Q)

/-- K4's own challenges with every sampled element 0: as many elements in each round as the
verifier's table says. -/
def k4ZeroOwn (Q : K4Pub) : List Fmt.Drawn :=
  (OnBytes.Desc.First.K4.rounds Q.P Q.hp Q.g).map fun d =>
    ⟨List.replicate d.drawn zeroE.triple, [], [], none⟩

/-- **A job has its call's public shape**: the cube's sizes fit (`Cube.fits`); it has the call's
number of variables, summed in the call's way, each with the three coefficients a round that
`Cube.round` yields; the lead, the degree in the further variable and the end values are as many as
the call states. The end values are counted at challenges 0. -/
def k4JobFits (sh : Call) (j : Job) : Bool :=
  let plain (v : VerifiableInference.Desc.Part.MaskedSum.Var) : Bool :=
    match v with
    | .plain _ => true
    | .point _ _ => false
  j.cube.fits && j.cube.n == sh.vs.length && j.lead.length == sh.lead &&
    (sh.vs.all fun v => v.d == 3) &&
    (match j.cube.way with
     | .plain => sh.vs.all plain
     | .point _ => sh.vs.all fun v => !plain v) &&
    (match sh.ends with
     | some e => j.dY == e.dY && (j.ends (List.replicate sh.vs.length zeroE)).length == e.n
     | none => false)

/-- **The zero input**, at which `k4MakersFit` asks the makers: every cell, weight and token is 0.
fo: what the lookup in front has sampled: `look` returns it at every list. -/
def k4ZeroIn (Q : K4Pub) (fo : OnBytes.Model.Forest.Heard) : K4In :=
  { cell := fun _ _ _ => 0, w := fun _ _ => 0, tokv := Array.replicate Q.P.y.T 0
    look := fun _ => fo }

/-- **The zero challenges**, at which `k4MakersFit` asks the makers: as many empty challenges as
rounds stand in front of the place, which `look` alone would read; then `k4ZeroOwn`. -/
def k4ZeroHeard (Q : K4Pub) : List Fmt.Drawn :=
  List.replicate Q.r0 ⟨[], [], [], none⟩ ++ k4ZeroOwn Q

/-- **The sampled values where the first n of K4's own rounds have been heard**, at the zero input
and the zero challenges. A part's maker is handed the sampled values of the challenges in front of
the part (`k4Scalars`, `k4Sum`, `k4SumSeen`): with n the number of K4's rounds in front of that part
these have the lengths of what it is handed in a run, where the run's challenges hold as many
elements as the verifier's table says and `look` returns values of fo's sizes. -/
def k4ZeroPts (Q : K4Pub) (fo : OnBytes.Model.Forest.Heard) (n : Nat) : Pts :=
  ptsOf Q (k4ZeroIn Q fo) ((k4ZeroHeard Q).take (Q.r0 + n))

/-- **Every maker returns, and what it returns has the shape that the row states, at the zero input
and zero challenges.** fo: what the lookup in front has sampled: its sizes matter here. All cells,
weights and tokens are 0; K4's challenges are `k4ZeroOwn`; the second token sumcheck's end values as
sent are 0. EACH MAKER IS ASKED WHERE ITS PART STANDS: at the challenges in front of that part and
no more (`k4ZeroPts`). How many of K4's rounds these are is taken off the verifier's table: a masked
sumcheck's part begins at its round "PSC epsilon" (`starts`); the two long lists of hidden scalars
go in the messages of the first two rounds "BAT-sigma" (`rowsNamed`). Each list of powers is asked
in front of the sumcheck whose summand reads it. Of the two long lists less is asked than of the
jobs: the first's length is right at every input by the way it is made, and the second's hangs, of
the sampled values, on the lookup's alone: the point by whose equality weights both are weighed is
asked by no clause at these two stands, but at the first token sumcheck's. The embedding's value,
which is 0 where no claim on the embedding is made, is asked with the merge's claims, at the merge's
stand, not at the round in whose message it goes. Asked: each of the seven summands' makers returns
a job that fits its call (`k4JobFits`), and the two long lists of hidden scalars (the sums of limb
products; the row products) have the lengths at which the row states them. The third list, the
embedding's value, has one entry by the way it is made. Of the four lists of powers of a sampled
element, which the summands read as weights, EACH IS COMPARED WITH THE NUMBER BY WHICH `ptsOf`
ITSELF MAKES IT (Johnson/Desc/K4/Honest/Front.lean): such a clause is false only where that round,
or its element, lacks among the challenges at which it is asked. THAT NO SUMMAND READS A LIST BEYOND
THAT NUMBER IS BY READING: `gp`, of 2 xl - 1 powers, is read at a limb's number, below xl; `omV`, of
7 powers for each norm at a plan that K4 covers, at 7 i + r for norm i and r below 7; `om`, of 2, at
a panel's field `claim`, which the verifier's list of panels lays as 0 or 1; `rhoW` at a claim's
number, and that the merge joins as many claims as the plan counts is asked here. Last: each of
these claims passes the verifier's own test on a claim's sizes (`wsClaimShape`,
OnBytes/Model/Weights.lean): one factor for each group of the claim's unit, each of the sizes that
its group asks. By reading, the rotation factor is the factor on the group "cd" of the queries' and
keys' units: so it has as many members as that group's extent, up to which `Sides.weights`
(Johnson/Desc/K4/Honest/Sides.lean) reads it index by index. NOT ASKED HERE: that the two summands
on given end values are there. A job's `atEnds` takes 0 where `Sides.summand` or
`StackData.summandOn` yields nothing, and `k4JobFits` does not call it. Where the two jobs' clauses
hold and there is a token, these two yield something at all end values, the first at every point of
lt coordinates, the second at every list of lamS challenges: `terms_atEnds`, `stack_atEnds`
(Honest/K4/Law/AtEnds.lean). DEAR: ALL THE MAKERS' WORK AT THE ZERO
INPUT. Not measured. -/
def k4MakersFit (Q : K4Pub) (fo : OnBytes.Model.Forest.Heard) : Bool :=
  let y := Q.P.y
  let w := k4ZeroIn Q fo
  -- in front of masked sumcheck number k; in front of the round "BAT-sigma" number k
  let s (k : Nat) : Pts := k4ZeroPts Q fo ((starts Q).getD k 0)
  let b (k : Nat) : Pts := k4ZeroPts Q fo ((rowsNamed Q .batSigma).getD k 0)
  let fits (k : Nat) (j : Option Job) : Bool :=
    j.any (k4JobFits ((k4Shapes Q).getD k ⟨0, [], none⟩))
  (wSums Q w (b 0)).length == ledNS y.h.xl * y.NI &&
    (rowProducts Q w (b 1)).length == ledNP y.h.xl * y.NI &&
    fits 0 (jobSquares Q w (s 0)) && fits 1 (jobRows Q w (s 1)) && fits 2 (jobTerms Q w (s 2)) &&
    fits 3 (jobStack Q w (s 3) (Array.replicate (nEndT y) zeroE)) &&
    fits 4 (jobGated Q w (s 4)) && fits 5 (jobGated2 Q w (s 5)) && fits 6 (jobMerge Q w (s 6)) &&
    ((mergeClaimsAt Q w (s 6)).any fun l => l.length == Q.hp.NCL) &&
    (s 0).gp.size == ledNS y.h.xl && (s 1).omV.size == ledNP y.h.xl * y.NI &&
    (s 3).om.size == 2 && (s 6).rhoW.size == Q.hp.NCL &&
    ((mergeClaimsAt Q w (s 6)).any fun l =>
      l.all fun c => (OnBytes.Model.wsClaimShape Q.P.wsLay c).isOk)

/-- **What the lookup has sampled has the layout's sizes.** The verifier's own test on the lookup's
numbers (`shapeFits`, OnBytes/Desc/First/K4/Hear.lean); its own on the depth (la is at most dT);
and, of the three fields that K4's parts read, the sizes with which the lookup's own text makes them
(`Forest.pad`, OnBytes/Model/Look.lean): the place in a tree has dT coordinates; each call has a
weight, and a point of as many coordinates as the call's key vector has variables. THE SIZES ALONE:
that each call's point ends in the last la coordinates of the lookup's point, which the verifier
tests on the values, is asked of `look` by nothing. -/
def k4LookFits (Q : K4Pub) (fo : OnBytes.Model.Forest.Heard) : Bool :=
  let h := Q.P.y.fo
  OnBytes.Desc.First.K4.shapeFits Q.P fo && decide (Q.P.y.h.la ≤ h.dT) &&
    fo.zx.size == h.dT && fo.e.size == h.NC && fo.zk.size == h.NC &&
    (List.range h.NC).all fun c => (fo.zk.getD c #[]).size == ((h.calls[c]?).map (·.n)).getD 0

/-- **The request has the plan's number of tokens, each below the size of the vocabulary**: the
verifier's own test where it makes the embedding's claim (`claimE`,
OnBytes/Model/LayerPanels.lean). The tokens are read in the first group of layers alone. -/
def k4TokensFit (Q : K4Pub) (tokv : Array Nat) : Bool :=
  Q.g != 0 || (tokv.size == Q.P.y.T && tokv.all fun t => decide (t < Q.P.V))

/-- **THE PUBLIC DATA FIT THESE PARTS**: the four tests as one. fo: what `look` returns at any list
of challenges of the shape that stands in front of the place. tokv: the request's tokens. All that
it reads is public. WHERE IT IS FALSE A PART MAY SEND ITS MASK ENTRIES OVER ZEROS, OR OVER VALUES OF
NO MEANING, AND NO MOVE SAYS SO. The dear test stands last. -/
def k4Fits (Q : K4Pub) (fo : OnBytes.Model.Forest.Heard) (tokv : Array Nat) : Bool :=
  k4TableFits Q && k4LookFits Q fo && k4TokensFit Q tokv && k4MakersFit Q fo

/-- Where matrix number mu of this segment's list is read: (segment, name, first column): its
owner's. The plan's own entry for the matrix says whose it is (`TMat`, OnBytes/Model/Frame.lean):
kind 1: an earlier sub-proof has committed to it; aId: 256 times the owning sub-proof's number,
which is the owner's group plus 1, plus the matrix's number in the owner's list; ttOff: its first
column there. In the plans that `tailsOf` makes the one such matrix is the stream that comes in,
from the second group on: the outgoing stream of the group before. The owner's segment is counted as
`K4Pub.seg` is: two segments a group. A number mu beyond the segment's list reads as an empty entry:
a padding of public data alone, which no test asks; that the group and each owner stand in their
lists `k4TableFits` asks. -/
def k4Owner (Q : K4Pub) (mu : Nat) : Nat × String × Nat :=
  let M := (Q.P.tails.getD Q.g {}).mats.getD mu {}
  if M.kind == 1 then
    let og := M.aId / 256 - 1
    (2 * og, ((Q.P.tails.getD og {}).mats.getD (M.aId % 256) {}).name, M.ttOff)
  else (Q.seg, M.name, 0)

/-- **The small input, of the chain's input.** cells, weights: how witness and index are read.
tokens: the request's tokens, of the public instance. look: see the head. OF THE WITNESS it reads
the cells of this segment's list of matrices, each under its owner's segment and name (`k4Owner`).
OF THE INDEX: the entries of the committed matrix. OF THE INSTANCE: the tokens. -/
def k4Wit (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (i : Local W₀ Rc Xi Tr) : K4In :=
  { cell := fun mu r c =>
      let at_ := k4Owner Q mu
      OnBytes.Slice.ofF ((cells i.trace).cell at_.1 at_.2.1 r (at_.2.2 + c))
    w := fun r c => OnBytes.Slice.ofF ((weights i.w₀).entry r c)
    tokv := tokens i.x
    look := look }

/-- **The entries of the committed vector of reads (U3) at this segment**, of the chain's input and
of all challenges heard so far in the first chain: `readsHeard` (Johnson/Desc/K4/Honest/Cells.lean)
at the small input: `Reads.u3 e` is entry number e, from 0; `Reads.has e` says whether that entry's
family has its weights: WHERE IT IS FALSE WHAT u3 READS IS NO ENTRY. No part of K4 sends these
entries. It is the one function here that reads the cells of the lookup's own matrix. WHERE `look`
LEAVES THE LOOKUP's TWO POINTS ON ITS PLANES EMPTY (zb0, zb1: no part of K4 reads them), TWO OF THE
THREE TABLES ON THAT MATRIX HAVE NO WEIGHTS: `has` is false at their entries: whoever calls this for
all of U3 carries «`has` is true at every entry» as a public hypothesis on `look`. None where the
verifier's own laying of the tables returns none. -/
def k4ReadsHeard (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard)
    (i : Local W₀ Rc Xi Tr) (heard : List Fmt.Drawn) : Option Reads :=
  readsHeard Q (k4Wit Q cells weights tokens look i) heard

/-- **The row.** -/
def k4Row (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X) :=
  (k4RowIn Q).map fun p =>
    p.lift (fun _ => ()) (k4Wit Q cells weights tokens look) (fun _ => ()) fun x _ => x

/-- **The kind's half.** -/
def k4Half (cells : Tr → Cells) (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    KindHalf K4Pub (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X :=
  fun Q => ⟨k4Place Q, k4Row Q cells weights tokens (look Q)⟩

/-- The request's tokens, of the instance: all words of the request file but the last two, as the
verifier's state has them (`S.tokv`, Johnson/Desc/First/State.lean). A request of fewer than two
words gives no token: public data alone. -/
def k4Tokens (x : Inst) : Array Nat :=
  let req := OnBytes.Model.Verify.words32 x.pub.request
  (req.extract 0 (req.size - 2)).map (·.toNat)

/-- A place's public data, of the parameters at which the lot lays K4's sub-protocol. The rounds in
front are counted off the public part's table of `verify-on-bytes`'s named steps (`Pub.cuts`), up
to the step of K4's stretch, "‹segment›.2.call"; nothing if the table has no such step. The
segment's number is twice the group's: the count in which each group of layers has a feed-forward
segment and then an attention segment. THAT IS THE LINK's NUMBER ONLY WHERE THE PROOF COVERS
ATTENTION. The segment's name is what stands in front of the first ":" of the parameters' name; the
empty word behind `headD` is a padding of public data alone. -/
def k4PubOf (Z : Pub) (p : OnBytes.Desc.First.K4.Par) : Option K4Pub :=
  (Z.roundsBefore? ((p.name.splitOn ":").headD "" ++ ".2.call")).map fun r0 =>
    { P := p.P, hp := p.hp, g := p.g, link := p.link, piece := p.piece, r0, seg := 2 * p.g }

/-- **The lot's honest side**: a half at each place at which the lot lays a sub-protocol (`k4From`,
Johnson/Desc/ProofFile/Lot/K4.lean), for which `k4PubOf` yields the public data and `k4TableFits`
is true; every other place is left without a half. The lot's own Bool at a place is not read: where
it is false the lot's sub-protocol rejects the plan. THE NAME IS WRITTEN A SECOND TIME HERE: the
lot's own takes the public part as an argument; `k4HLot_name` holds the two together. -/
def k4HLot (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    HLot (Local W₀ Rc Inst Tr) (Local W₀ Rc Inst Tr) X :=
  { name := "K4"
    halves := fun Z G => (k4From Z G G.built.toList 0 none).filterMap fun x =>
      ((k4PubOf Z x.2).filter k4TableFits).map (k4Half cells weights k4Tokens (look Z G)) }

/-- The name that is written above is the lot's own, at every public part. -/
theorem k4HLot_name (cells : Tr → Cells) (weights : W₀ → Weights)
    (look : Pub → Ground → K4Pub → List Fmt.Drawn → OnBytes.Model.Forest.Heard) (Z : Pub) :
    (k4HLot (Rc := Rc) (X := X) cells weights look).name = (k4Lot Z).name := rfl

/-! ## A simulator beside each part -/

/-- A simulator beside each part. Each takes as many coins of its own as its part sends scalars and
reads nothing that it is handed. -/
def k4Sims (Q : K4Pub) : List (Sim Xi) := (k4Sorts (Pb := Xi) Q).zipIdx.map fun s => s.1.sim s.2

/-- The row, each part with its simulator. -/
def k4Sided (Q : K4Pub) (cells : Tr → Cells) (weights : W₀ → Weights)
    (tokens : Xi → Array Nat) (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) :
    List (Part (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X × Sim Xi) :=
  (k4Row Q cells weights tokens look).zip (k4Sims Q)

/-! ## The verifier's test on a sampled value -/

/-- **"coin-zero"**, of K4's own challenges: the element sampled in the "PSC epsilon" of the second
token sumcheck is 0. The verifier's own Bool is `!isZeroE tT.p.eps`
(OnBytes/Desc/First/K4/Hear.lean, `hearTerms`); K4's sub-protocol rejects there under the one name
"K4.hear". It reads no sent value and no coin. None while that round's challenge has not been heard.
None too where that challenge holds no element: it is read as 1 here, and as 0 by the part's own
moves (`drawnE`, Honest/Sum.lean). -/
def k4CoinZero (Q : K4Pub) (own : List Fmt.Drawn) : Option String :=
  match own[(starts Q).getD 2 0]? with
  | some d =>
    if OnBytes.isZeroE ((d.elems.head?.map E.ofTriple).getD OnBytes.oneE) then
      some ("the verifier rejects (K4.hear): the challenge that joins the second token " ++
        "sumcheck's hiding polynomial to its claim was sampled as 0")
    else none
  | none => none

/-- A stated share for it: 1 of the number of elements of the extension field. A stated number; no
bound is shown. -/
def k4CoinZeroShare : Odds := ⟨1, (2 ^ 64 - 2 ^ 32 + 1) ^ 3⟩

/-- **The fall at K4's own member** (`Fall`, Honest/Side.lean): the element is sampled in a round of
that member, and that member rejects. The test reads the member's own challenges alone. -/
def k4Fall {S : Type} (Q : K4Pub) : Fall S :=
  ⟨k4Place Q, fun _ ds => k4CoinZero Q ds, k4CoinZeroShare⟩

/-- **K4's own test behind the batching, "free-slot", as a fall at the member in which it runs.**
seat: where in the verifier's state K4's ledger and what K4 heard lie. quiet: the place of that
member: the sub-protocol without a round behind the round in which the segment's batching element is
sampled; whoever seats this fall lays it. The test is the verifier's own Bool (`freeSlotOk`,
OnBytes/Desc/First/K4/Plain.lean), as K4's run asks it (`freeSlot`,
Johnson/Desc/First/K4/Block.lean), at the state in front of that member. IN THAT MEMBER K4's RUN
STANDS BEHIND THE LINK's TESTS AND ANOTHER KIND's RUN, "K8.lsTail" (`Link.runBehind`,
Johnson/Desc/Block.lean; `orderAfterOf`, Johnson/Desc/First/Driver/Chain.lean): that these leave the
ledger and what K4 heard as they stand in front of the member is shown by nothing here (what that
run writes: `sits_lsTail`, Johnson/Desc/First/TailClaims/K8Sits.lean). Where nothing was heard it
says nothing: the run rejects there under another name, and that rejection is excused by no fall.
share: A STATED NUMBER, the seater's. By reading, the batching's own test on the free slots at that
member asks the same Bool of the same ledger where its plan is K4's. THE NUMBER TO STATE HERE IS THE
ONE THAT IS STATED FOR THAT TEST AT THAT MEMBER, and not one that would say that this test never
speaks (what a share stands for: `Fall.share`, Honest/Side.lean). That one event is not counted
twice where two falls speak of it is the business of whoever adds the shares. -/
def k4FreeSlotFall {S : Type} (seat : OnBytes.Desc.First.K4.Seat S) (Q : K4Pub) (quiet : Place)
    (share : Odds) : Fall S :=
  { place := quiet
    test := fun s _ => (seat.own s).bind fun o =>
      if OnBytes.Desc.First.K4.freeSlotOk Q.hp.used o.wo.sFv (seat.fork s) then none
      else some ("the verifier rejects (K4.free-slot): behind the batching a slot that a scalar " ++
        "of this segment took has the coefficient 0, or the slot of the merge's end value has a " ++
        "coefficient other than 0")
    share := share }

/-! ## The side -/

/-- **The side**: that row beside the member of a description's first chain that stands at the
place, with the fall at that member. bs: that chain's list. fo, tokv: for the test alone: see
`k4Fits`. NOTHING HERE TIES THEM TO `look` AND `tokens`: a statement's hypothesis is `k4Fits` at
what `look` returns of the challenges in front and at the instance's tokens. `none` if no member
stands there, if the rounds in front of the place in that list are not as many as `Q.r0` says, if
the member's rounds are not the entries of the verifier's table at Q's plan (`entries`,
Johnson/Desc/First/K4/Block.lean): so that each round samples as many elements as that table says;
or if `k4Fits` is false. -/
def k4Side {S Cl : Type} (bs : List (Block S Cl)) (Q : K4Pub) (cells : Tr → Cells)
    (weights : W₀ → Weights) (tokens : Xi → Array Nat)
    (look : List Fmt.Drawn → OnBytes.Model.Forest.Heard) (fo : OnBytes.Model.Forest.Heard)
    (tokv : Array Nat) : Option (Side S Cl (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X Xi) :=
  if roundsInFront bs (k4Place Q) == some Q.r0 &&
      ((bs.find? fun b => b.place == k4Place Q).any fun b =>
        b.rounds.map (·.entry) == OnBytes.Desc.First.K4.entries Q.P Q.hp Q.g) &&
      k4Fits Q fo tokv then
    Side.seated bs (k4Place Q) (k4Sided Q cells weights tokens look) [k4Fall Q]
  else none

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.k4HLot_name
