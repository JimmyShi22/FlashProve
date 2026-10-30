-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Side.lean: One structure for the honest side of one sub-protocol: the
sub-protocol, the prover's side as a list of parts, and one candidate simulator for each part. The
types are in Honest/Frame.lean. The file also has functions that cut a part's share out of a run,
and one structure, `Good`, of four conditions on such a side. Definitions only: no theorem is
stated, and no side of any sub-protocol of the protocol is defined here.

  1  `Run.partAt`, `Run.shownAt`, `Run.askedAt`, `Run.drawnAt`, `Run.seenAt`, `Run.beforeAt`,
     `Run.storedAsked`, `storedShown`, `Before.treeCols`, `Before.holds`, `Before.colAt`,
     `Before.opened`, `Before.drawnOf`, `readsBefore`   a part's share of a run: what is shown of
     its rounds; at which positions its tables are read; its rounds' challenges; what has been shown
     before it, as the part is given it (the rounds alone: see `Run.seenAt`), and as its simulator
     is; the columns that a `Before` holds for the reads of declared rounds
  2  `Fall`, `fallOf`, `Side`, `Side.seated`, `Side.half`, `Side.fits`, `Member`, `Side.members`   a
     fall: a named event at which the verifier may reject an honest run (see Limits, "Falls");
     the structure `Side`; its sub-protocol taken from a description's list; its prover's side; that
     list and sub-protocol fit; a part with what belongs to it; the list cut into such members
  3  `shownOf`, `Side.shows`, `Member.tells`, `Part.stopAt`, `Side.stopAt`   what a part shows,
     played alone at its own rounds; what its simulator outputs there; whether a part stops, and a
     list of parts
  4  `Env`, `Env.add`   the tables that are available before a place, and after it
  5  `Good`   a check, `fits`, and the four conditions: `plays`, `acc`, `exact`, `fresh`

What each condition speaks of. `plays` and `acc` speak of the whole list of parts, because a
sub-protocol has one decision, which a cut of the prover's side does not cut. A and B are parameters
of `Good`: a condition before the place and one after it. `plays`: from A, the list's rounds are
played without an error and the columns that are read are available, fall or not; and where the
sub-protocol's own step (`Block.step`) accepts, B holds after it, at the state with the columns read
laid in (`Mid.took`). `acc`: outside the fall that step accepts. `exact` and `fresh` speak of each
part alone: a part is the unit that gets coins, and `Side.row` pairs it with a candidate simulator.

What a side cannot choose. `Face` fixes which field of the input is public and goes to a simulator,
and whether a second stop may read the input. (The types of these fields stay parameters: see
Limits.) A simulator's type has no argument beyond the five of `Sim.tell`. The coins at which
`plays` and `acc` are stated are what the book lends (`lendRow`) of a whole run's coins, typed by
the book.

Relation to the library's conditions. The library's structure `IOR.GoodT` (Ior/KnowCollGood.lean)
bundles, for one honest side `H : R.Honest Wi Wo` of a typed reduction R, among others `acc`,
`prBad`, `cover`, `prCov` and `exact`. The library has a block as such a reduction: `Piece.ior`
(Johnson/Desc/Sound/ChainRule.lean), by `stageIOR` (OnBytes/Maker/Stage.lean). Its honest side is a
strategy over the written rounds, whose challenges hold the bits of proof of work, which `stageIOR`
tests first. A `Placed` is no such strategy: it works at the level of the views, where no such bit
occurs, and no function from a `Placed` to a `p.ior.Honest` is defined. `Good` is stated at the
level of the views, and its fields follow the library's single conditions, not its bundles: `plays`
with `acc` follows `Honest.Acc`; `exact` follows `Honest.ExactWith` (Ior/Honest.lean) and, where a
part spends, the field `law` of `Honest.MM` (Ior/Masked.lean); `fresh` follows `Honest.Fresh`
(Ior/KnowCollRulesMask.lean). No field measures a set of challenges: each condition is stated at a
fixed list of challenges (`exact` and `fresh` compare two distributions over coins), and the
challenges at which a part stops are given by the part's own two stops.

`plays` with `acc` beside `Honest.Acc`, clause by clause. Each line has the library's clause, a
colon, and its counterpart here.
  x, the explicit input: s, the verifier's state before the place.
  y, the implicit input: E, the available tables.
  w, the input witness: m, the state of the prover's run.
  `Ri x y w`: `A k s m E`.
  `ρ ∉ H.withheld w x`, a hypothesis: `σ.stopAt … = none`, a hypothesis.
  the verifier's output is the explicit part with which the prover ends: `Block.step` returns ok:
    `acc`, outside the place's fall, which the library does not have.
  `Ro` of that part, the new implicit instance and the new witness:
    `B k s' (y.2.took cols) (E.add y.1)`: `plays`, wherever the step returns ok.
What differs. (1) There the statement is for all coins c of the one reduction; here it is for all
coins k of a whole run, of which the book lends the list its own, and A and B read k. In the library
a mask that was sent in advance is part of the input witness (Ior/Masked.lean, its head). Here the
state that parts pass on holds no coin of a run, by type (`Move.hand`), so a condition that ties a
borrowed block to the table that holds it has to read the run's coins. (2) There the prover ends
with an explicit part of its own; here a part passes on X and no copy of S, and B ties s' to the
state. (3) A challenge here is a raw `Fmt.Drawn`: hence the hypothesis `drawsFit`. (4) The available
tables are options: hence the clause with `fillCols`.

Borrowed coins. `exact` is a condition on one part and its candidate simulator; it is not a theorem.
It asks that what the part shows has the same distribution as what the simulator outputs. The part's
side is taken over its own coins and its spent blocks of borrowed coins, all drawn uniformly and
independently of everything before the part. The simulator's side is taken over the simulator's own
coins. The condition `On`, at the part's start, is given the carried blocks, `m` and `front`; by its
type it is given neither the spent blocks nor the part's own coins. `fresh` is a condition on one
part, the owner, once for each part p; it is not a theorem. It asks that, over the owner's own
coins, the blocks that p spends are uniform and independent of two things taken together. The two
things are what the owner shows, and the owner's other coins that the book gives to p or to a part
before p. In Lean it is one equation: the three have the same distribution when the first is
replaced by fresh uniform coins. In a real run the spent blocks are not fresh: their owner may
already have shown values that depend on them. `fresh` is the condition on that owner, and this file
states no rule that joins the two. What is held fixed on both sides, and where each condition is
asked, is told in the docstrings of `Good.exact` and `Good.fresh`. Two tests of `ProverCoinCounts.clauses`
belong to the two conditions: "a coin that a part spends is handed to a part in front of it, or to
itself as carried" and "a coin stands in two entries that spend it".
In the library, at its own level, a block whose masks were sent in advance does not have the field
`exact` over its own coins alone. That is `masked_not_exact` (Ior/Masked.lean), under its premises;
such a block has a condition of its own instead, `Honest.MM`, in the bundle `GoodM`. The rule that
takes such a block through a chain uses `ExactWith` of everything before it, `Fresh` and `MM`, with
`Blind` for the links between (`exact_seq_masked`, `fresh_seq`: Ior/KnowCollRulesMask.lean). What
differs: `MM` asks that the block sends no oracle and withholds nothing (its fields `noOrc` and
`free`). Neither is asked here: a part may spend and also send a table, or have a stop. The
library's `Fresh` speaks of everything before the spender; `fresh` speaks of the owner alone. Its
clause on the parts before p is this file's counterpart of the library's `Blind`; that it does the
same work is not proved. No rule for a list of sides is stated here.

Limits.
  * `Good` is a list of conditions with free parameters; this file proves it of no side. A theorem
    elsewhere that concludes it of a side says at which A, B, On and `bud`: at an A that never
    holds, `plays` and `acc` hold vacuously (the next limit). The rule that joins lists of parts
    (Honest/Law/Rule/Row.lean) takes `Owed` (Honest/Owed.lean) and `G.owns`; of `Good` its proof
    uses `fits`, `exact` and `fresh` alone.
  * Free parameters: the conditions A, B and On, the bound `bud` on the positions that may be read,
    the book, the order of places, `chain`, `firstTree` and `pre`. So A := False, On := False or bud
    := False make a field hold vacuously. `fresh` reads the entries of whatever book, and the order
    of whatever list, is supplied; those of `run` are the run's book and `orderOf`. A `pre` that is
    not the rounds whose columns the player has handed makes `exact` idle at that player's states,
    or puts it at `opened = none`; `goodAt` takes the earlier chains' rounds from its caller, and
    `Owed` lays them by `earlierOf`.
  * The stops. All four conditions are stated outside them: `plays` and `acc` where no part stops,
    `exact` and `fresh` where the part is not stopped by its second stop (`Part.stopAt` is not
    `some .hid`). Where the first stop fires at the same point or earlier, `stopAt` reports the
    first, and the condition is still asked. A side of which one part always stops meets `plays` and
    `acc`, and a part that its second stop always stops meets the two others. No field measures the
    challenges at which a part stops: the library's `prBad`, `cover` and `prCov` have no counterpart
    here. That measure is needed alongside any statement on a list of sides; `silentAt`
    (Honest/Rule.lean) names the lists, from the stops alone, without a coin.
  * `Good` names no description and no prover. Only `run` and `runC` (Honest/Walk.lean) set the
    public field to a description's own instance, or to the key made of it. If the whole input, the
    index included, is chosen for the type `Xi` or `Ky`, a simulator is given all of it. `exact`
    then no longer separates what is public from what is private, so a statement on a list of sides
    must name one description and one prover. Nothing here ties `Side.half` to the side that a
    prover plays.
  * Parameters that read challenges. Every parameter of `Good` that reads a challenge or a position
    (On, through `front`; `bud`) can be false at some lists of challenges. At such a list `exact`
    says nothing, as where a second stop stops the part. So a statement on a list of sides has to
    prove On and `bud` at every list outside the one named set (`silentAt`, Honest/Rule.lean), as
    conclusions, not as hypotheses on the given list. A bound on positions is meant to count
    distinct positions.
  * Falls. A test of the verifier's can read a value that was sent in the clear and that depends on
    a coin of the run. Then the honest prover's own coins can make it fail, and no stop can express
    that, since a stop is given no coin. Such a test is a fall (`Fall`), and it is why the condition
    on the whole list is cut into `plays` and `acc`. Only `acc` reads the field `fall`. No move,
    stop or simulator is given it. A fall names a rejection, so that it can be measured. What the
    honest prover does where the verifier rejects, for whatever reason, is defined in
    Honest/Walk.lean: it puts substitutes after the sub-protocol that rejects.
  * Where a fall belongs. It belongs to the sub-protocol whose own step it excuses, which is the one
    that rejects, not the one that draws the challenge on which the test depends. Its test reads the
    verifier's state before that sub-protocol, which holds what was sent and drawn, and that
    sub-protocol's own challenges. No earlier sub-protocol has "no fall" among its hypotheses:
    between the draw and the rejection, parts are played at coins that lead to the fall, and their
    conditions apply there. A sub-protocol without a round has no side: its fall is in the chain's
    list (`Sides`, Honest/Rule.lean) and is read by whoever states something of such sub-protocols.
  * A fall that is too wide. A fall whose test covers more than the verifier's test makes `acc` hold
    vacuously there (test := "the step rejects" would do so everywhere). No type prevents that; what
    it costs is a larger share (`Fall.share`). So each fall's test names the verifier's own tests
    that it covers, and a proof of `acc` has to exclude every other reason for which the
    sub-protocol rejects. By type the verifier's state can also hold what came out of opened
    columns: that a fall reads plain messages and challenges alone has to be proved separately.
  * Which lists of challenges. The four conditions are stated at every list that the side's own
    rounds can draw (`drawsFit`). `Draws.due` asks one thing more, of the first chain's sealing
    round: the empty challenge. `drawsFit` allows a sealed digest at every sealing round. So at the
    sub-protocol that holds that round the conditions are also stated at lists at which `due` is
    false and `run` and `runC` return an error: they ask more there, never less.
  * What On has to tie. `exact` itself ties `front` to m by its rounds' items and challenges, by the
    columns for the reads of `pre` (`m.opened`), and to the part's own challenges by `Before.holds`:
    that a column is listed for every read of the part's own rounds, not what the column holds, nor
    which other positions are listed. On also has to tie how many trees of this chain `front` lists:
    an earlier tree that `front` leaves out counts as the part's own, and the test passes. And On
    has to tie each round's chain number in `front`, which `Before.seen` drops. On also has to tie
    how many rounds of each chain `front` lists: with fewer than `pre` has, fewer columns count as
    opened. `fresh` has no `front`: the columns that its owner is handed are `m.opened`, fixed at
    any value. A part's `Seen` holds the columns opened before its place, or `none` (`Seen.opened`);
    `exact` ties them to `front` (`Before.opened`).
  * Only the condition `On` ties the columns in `front`, `Before.stored`, `Mid.opened`, `Mid.loc`
    and `State.heard` to each other and to the input (`Mid.opened` is tied to `front` by the premise
    of `exact`; to the input by On alone). So whatever `On` allows in `front` reaches the simulator,
    private data included. The frame's own `front` is `Run.beforeAt`. Where a part is stopped by its
    first stop (`Part.stopAt` is `some .bad`), `exact` asks the simulator to output `none` too. That
    stop reads `Mid.loc`, which the simulator can recover from `front`'s challenges only where `On`
    ties the two.
  * Who proves On. No field here leads from A to On. Whoever states something of a list of sides has
    to prove On over real runs, at a part inside a list as at a place's first part (`Owed`,
    Honest/Owed.lean).
  * Who proves the premise on `opened`. No field here leads to it. At the states of `run`, `midAt`
    and `midSharedAt` the field is `none`, and `exact` is asked there only where `front` lacks a
    column of `pre`. That `runC`'s state before a part meets it at `Run.beforeAt` has to be proved
    by whoever states something of a list of sides.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Frame

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Place Oracle OpenedColumn)

variable {S Cl V W X Pb : Type}

/-! ## 1 A part's share of a run -/

/-- A chain's played rounds, each with the number of its first table in the chain's order of
sending. -/
def numbered : List Played → Nat → List (Played × Nat)
  | [], _ => []
  | p :: l, n => (p, n) :: numbered l (n + p.tables.length)

/-- The round is listed under this address. -/
def Played.isAt (p : Played) (a : Addr) : Bool := p.place == a.place && p.part == a.part

/-- The rounds of chain number `ch` (from 0) that the part at `a` played. With each round, for each
of its roots: the reads in `qs` of the tree under that root. -/
def partIn (ch : Nat) (l : List Played) (qs : List Read) (a : Addr) :
    List (Played × List (List Read)) :=
  ((numbered l 0).filter fun x => x.1.isAt a).map fun x =>
    (x.1, (List.range x.1.tables.length).map fun i =>
      qs.filter fun q => q.src == some (ch, x.2 + i))

/-- **A part's share of a run**: the rounds that it played. With each round, for each of its roots:
the reads of that tree in any round of the three chains, in the order of the views. -/
def Run.partAt (r : Run) (a : Addr) : List (Played × List (List Read)) :=
  let qs := r.reads.1 ++ r.reads.2.1 ++ r.reads.2.2
  partIn 0 r.played.1 qs a ++ partIn 1 r.played.2.1 qs a ++ partIn 2 r.played.2.2 qs a

/-- What a run shows of a part's rounds. -/
def Run.shownAt (r : Run) (a : Addr) : List Shown :=
  (r.partAt a).map fun x =>
    ⟨x.1.vals, x.2.map fun l => l.filterMap fun q => q.words.map fun w => (q.pos, w)⟩

/-- The positions at which a part's tables are read, by round and by root. -/
def Run.askedAt (r : Run) (a : Addr) : List (List (List Nat)) :=
  (r.partAt a).map fun x => x.2.map fun l => l.map (·.pos)

/-- The challenges of a part's rounds. -/
def Run.drawnAt (r : Run) (a : Addr) : List Fmt.Drawn := (r.partAt a).map (·.1.drawn)

/-- The rounds that have been shown before a part, as `run` and `runC` give them to the part at its
first round. THE OPENED COLUMNS ARE NOT IN IT: it is `.bare`, as `run` hands it; `runC` hands the
part `some` columns besides (`Mid.shown`). At an address at which no round was played it is all the
rounds of the run. -/
def Run.seenAt (r : Run) (a : Addr) : Seen :=
  let front (l : List Played) : List Fmt.RoundView := roundsOf (l.takeWhile fun p => !p.isAt a)
  if r.played.1.any (·.isAt a) then .bare (front r.played.1)
  else if r.played.2.1.any (·.isAt a) then .bare (front r.played.2.1)
  else .bare (roundsOf r.played.1 ++ roundsOf r.played.2.1 ++ front r.played.2.2)

/-- A chain's played rounds, each with what is shown of it: its items in the clear and, for each of
its roots, the columns of that tree that the reads in `qs` read. `ch`: the chain's number, from 0.
-/
def shownIn (ch : Nat) (l : List Played) (qs : List Read) : List (Played × Shown) :=
  (numbered l 0).map fun x =>
    (x.1, ⟨x.1.vals, (List.range x.1.tables.length).map fun i =>
      (qs.filter fun q => q.src == some (ch, x.2 + i)).filterMap fun q =>
        q.words.map fun w => (q.pos, w)⟩)

/-- The reads that a run makes of stored tables: the statement's item and the position. -/
def Run.storedAsked (r : Run) : List (Nat × Nat) :=
  (r.reads.1 ++ r.reads.2.1 ++ r.reads.2.2).filterMap fun q => q.item.map fun i => (i, q.pos)

/-- **The stored tables' columns at given reads**: the statement's item, the position, the words. It
is the one function for whoever supplies `Before.stored`. `stored` computes a column from an item
and a position, as `Prover.storedWords` does at the index and the stored tables' pads and encoding
randomness. -/
def storedShown (stored : Nat → Nat → Option (List UInt64)) (asked : List (Nat × Nat)) :
    List (Nat × Nat × List UInt64) :=
  asked.filterMap fun q => (stored q.1 q.2).map fun w => (q.1, q.2, w)

/-- **What a simulator for the part at `a` is given of a run**: the rounds that `Run.seenAt` has,
each with its tables' columns at all positions that the run reads of them. `st`: the stored tables'
columns, which the caller supplies, by `storedShown` at `Run.storedAsked`. At an address at which no
round was played: as for `Run.seenAt`. -/
def Run.beforeAt (r : Run) (st : List (Nat × Nat × List UInt64)) (a : Addr) : Before :=
  let qs := r.reads.1 ++ r.reads.2.1 ++ r.reads.2.2
  let out (ch : Nat) (l : List Played) : List (Played × Nat × Shown × Fmt.Drawn) :=
    (shownIn ch l qs).map fun x => (x.1, ch, x.2, x.1.drawn)
  let whole (ch : Nat) (l : List Played) : List (Nat × Shown × Fmt.Drawn) := (out ch l).map (·.2)
  let front (ch : Nat) (l : List Played) : List (Nat × Shown × Fmt.Drawn) :=
    ((out ch l).takeWhile fun x => !x.1.isAt a).map (·.2)
  if r.played.1.any (·.isAt a) then ⟨front 0 r.played.1, st⟩
  else if r.played.2.1.any (·.isAt a) then ⟨front 1 r.played.2.1, st⟩
  else ⟨whole 0 r.played.1 ++ whole 1 r.played.2.1 ++ front 2 r.played.2.2, st⟩

/-- The columns that `f` holds of tree number `n` (from 0) that chain number `ch` has sent; `none`
if it holds fewer trees of that chain. -/
def Before.treeCols (f : Before) (ch n : Nat) : Option (List (Nat × List UInt64)) :=
  ((f.rounds.filter fun r => r.1 == ch).flatMap fun r => r.2.1.cols)[n]?

/-- The column that `f` holds for one read, in the form in which a view has it; `none` if it holds
none. Of the read it takes the key, the position, the item and the source. Its width is not tested;
of two at one position the first is taken. -/
def Before.colAt (f : Before) (q : Read) : Option OpenedColumn :=
  match q.item, q.src with
  | some i, _ =>
    (f.stored.find? fun c => c.1 == i && c.2.1 == q.pos).map fun c => (q.key, q.pos, c.2.2)
  | none, some (ch, n) =>
    (f.treeCols ch n).bind fun cols =>
      (cols.find? fun c => c.1 == q.pos).map fun c => (q.key, q.pos, c.2)
  | none, none => none

/-- **The columns that `f` holds for a list of reads**, in the reads' order; `none` if one is
lacking. It reads `f` and the list and nothing else. -/
def Before.opened (f : Before) (qs : List Read) : Option (List OpenedColumn) := qs.mapM f.colAt

/-- The challenges of the rounds of chain number `ch` in `f`. -/
def Before.drawnOf (f : Before) (ch : Nat) : List Fmt.Drawn :=
  (f.rounds.filter fun r => r.1 == ch).map (·.2.2)

/-- **The reads that declared rounds make at the challenges in `f`.** `pre`: for each chain whose
columns are handed, its number (from 0), the number in the label of its first own tree, and the
declared rounds of the sub-protocols before the place. The reads' words are left empty, as in
`Before.holds`. `readsOf` stops at the shorter of its two lists: so the challenges in `f` beyond
these rounds, such as those of earlier rounds of the part's own sub-protocol, are dropped; and
rounds of `pre` beyond the challenges in `f` are dropped with their reads. -/
def readsBefore (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (f : Before) : List Read :=
  pre.flatMap fun x =>
    readsOf x.1 x.2.1 (fun _ _ => none) (fun _ => none) x.2.2 (f.drawnOf x.1)

/-- **`f` has a column for every read that these rounds make at these challenges**, of a stored
table or of an earlier tree. An executable test, by `readsOf`. `chain`, `firstTree`: as in
`readsOf`. A tree of this chain of which `f` lists no root (its number is not below the number of
roots that `f` lists of the chain) counts as sent by these rounds themselves, so `f` need not hold
its columns. -/
def Before.holds (f : Before) (chain firstTree : Nat) (decls : List Fmt.DeclaredRound)
    (ds : List Fmt.Drawn) : Bool :=
  (readsOf chain firstTree (fun _ _ => none) (fun _ => none) decls ds).all fun q =>
    match q.item, q.src with
    | some i, _ => f.stored.any fun c => c.1 == i && c.2.1 == q.pos
    | none, some (ch, n) =>
      match f.treeCols ch n with
      | some cols => cols.any fun c => c.1 == q.pos
      | none => ch == chain
    | none, none => true

/-! ## 2 The structure `Side` -/

/-- **A fall**: an executable test for an event at which the sub-protocol at a place may reject an
honest run. It reads the verifier's state before the place, which holds what was sent in the clear,
and the place's own challenges. It is given no coin and no input; the set of lists of challenges at
which a run falls depends on both, through what was sent. It is a structure of its own, so that it
can be written for a prover's side without a `Side`. -/
structure Fall (S : Type) where
  /-- the place of the sub-protocol whose own step it excuses: the one that rejects -/
  place : Place
  test : S → List Fmt.Drawn → Option String
  /-- a stated number, no bound. What it is meant to be: fix an input of the relation and the run's
  coins, and draw all challenges as the written rounds draw them; the share is the probability that
  the run falls here. (It is not the fraction of lists of `Fmt.Drawn`: two of the library's typed
  challenges can give the same `Fmt.Drawn`, so the two numbers can differ.) Nothing compares it with
  the test -/
  share : Odds

/-- The falls of a list at one place, as one: the answer of the first of them that answers; `none`
if there is none at the place or none answers. So one sub-protocol can have several falls. -/
def fallOf {S : Type} (fs : List (Fall S)) (a : Place) (s : S) (ds : List Fmt.Drawn) :
    Option String :=
  (fs.filter fun f => f.place == a).findSome? fun f => f.test s ds

/-- **The honest side of one sub-protocol at its place**: one structure for every statement on it.
-/
structure Side (S Cl V W X Pb : Type) where
  /-- the description's own sub-protocol at the place, as the functions that build the description
  have wrapped it (guarded, joined, retyped), not the kind's or the lot's definition: `plays` and
  `acc` speak of this block's step. `Side.seated` takes it from a description's list -/
  block : Block S Cl
  /-- The list of parts, each paired with a term of type `Sim`. The type asks nothing more of that
  term. -/
  row : List (Part V W X × Sim Pb)
  /-- the fall at this place, from the verifier's state before it and the place's own challenges.
  `Good.acc` alone reads it. Most places have none -/
  fall : S → List Fmt.Drawn → Option String := fun _ _ => none

/-- **A side whose sub-protocol is taken from a description's own list, by its place**: the first
sub-protocol at that place; `none` if there is none. (That no two are at one place is the
description's test `FileDescription.placesOk`, which `ready` runs, for `run` and `runC` alike.) `fs`: the
chain's falls, of which those at this place are used (`fallOf`). -/
def Side.seated (bs : List (Block S Cl)) (a : Place) (row : List (Part V W X × Sim Pb))
    (fs : List (Fall S) := []) : Option (Side S Cl V W X Pb) :=
  (bs.find? fun b => b.place == a).map fun b => { block := b, row := row, fall := fallOf fs a }

/-- **The prover's side**: the list's parts, at the sub-protocol's own place. -/
def Side.half (σ : Side S Cl V W X Pb) : Placed V W X := ⟨σ.block.place, σ.row.map (·.1)⟩

/-- The list has exactly one move for each of the sub-protocol's rounds, each simulator names its
part's address, and the sub-protocol has as many lists of oracle messages as rounds. -/
def Side.fits (σ : Side S Cl V W X Pb) : Bool :=
  σ.row.zipIdx.all (fun s => s.1.2.addr == ⟨σ.block.place, s.2⟩) &&
    σ.half.rounds == σ.block.rounds.length && σ.block.oracles.length == σ.block.rounds.length

/-- **A part with what belongs to it**: its number in the list; the rounds of the sub-protocol that
are its own, each with its oracle messages; the part; its simulator. -/
structure Member (V W X Pb : Type) where
  number : Nat
  rounds : List (Fmt.DeclaredRound × List Oracle)
  part : Part V W X
  sim : Sim Pb

/-- A list of parts cut into members, as `rowSteps` cuts it: each part gets as many rounds as it has
moves. Every part of the list is a member. -/
def membersOf : List (Part V W X × Sim Pb) → Nat → List (Fmt.DeclaredRound × List Oracle) →
    List (Member V W X Pb)
  | x :: l, j, rs =>
    ⟨j, rs.take x.1.moves.length, x.1, x.2⟩ :: membersOf l (j + 1) (rs.drop x.1.moves.length)
  | [], _, _ => []

/-- A side's members. -/
def Side.members (σ : Side S Cl V W X Pb) : List (Member V W X Pb) :=
  membersOf σ.row 0 (σ.block.rounds.zip σ.block.oracles)

/-! ## 3 A part played alone -/

/-- What played rounds show at given positions, by round and by root. It goes over the rounds and
their roots and looks the positions up by index: so a round's items in the clear are shown whatever
`asks` is, and a missing list of positions counts as empty. -/
def shownOf (ps : List Played) (asks : List (List (List Nat))) : List Shown :=
  ps.zipIdx.map fun x =>
    ⟨x.1.vals, x.1.tables.zipIdx.map fun y =>
      match y.1 with
      | some t => ((((asks[x.2]?).getD [])[y.2]?).getD []).map fun p => (p, t.col p)
      | none => []⟩

/-- **What a part shows**, played alone at its own rounds by `play`: from the state of the chain's
run before the part, at given coins, at the challenges of its rounds and at the positions that will
be read. `none` if it stops or returns an error. -/
def Side.shows (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (u : Member V W X Pb) (c : u.part.Coins)
    (m : Mid W X) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) : Option (List Shown) :=
  (play (u.part.steps σ.block.name ⟨σ.block.place, u.number⟩ u.rounds (φ.sees m.st.input) c) ds []
    m).toOption.map fun y => shownOf y.1 asks

/-- What the part's candidate simulator outputs there. Of the input it is given the public field
alone (`Face.pub`). `front`, `ds` and `asks` are the caller's arguments, and nothing in this
definition ties `front` to a run. -/
def Member.tells (u : Member V W X Pb) (φ : Face V W Pb) (c : Cs u.sim.takes) (w : W)
    (front : Before) (ds : List Fmt.Drawn) (asks : List (List (List Nat))) : Option (List Shown) :=
  u.sim.tell (φ.pub w) front ds asks c

/-- **Whether a part stops**, and by which of its two stops: at what its second stop may read, at
the challenges before the part that its stops are given, and at those of its own rounds. It is
computed from the two stops alone, as `play` asks them: before each round and once more after the
last, the first stop first. A part without a round is not asked. No coin is among its arguments. -/
def Part.stopAt (p : Part V W X) (v : Option V) (loc ds : List Fmt.Drawn) : Option Why :=
  let n := p.moves.length
  (if n == 0 then [] else List.range (n + 1)).findSome? fun j =>
    if (p.bad loc (ds.take j)).isSome then some .bad
    else if (v.bind fun u => p.hid u loc (ds.take j)).isSome then some .hid
    else none

/-- Whether a list of parts stops: the first part that stops, in the list's order. -/
def rowStopAt (v : Option V) : List (Part V W X) → List Fmt.Drawn → List Fmt.Drawn → Option Why
  | [], _, _ => none
  | p :: ps, loc, ds =>
    (p.stopAt v loc (ds.take p.moves.length)).or
      (rowStopAt v ps (loc ++ ds.take p.moves.length) (ds.drop p.moves.length))

/-- **Whether the prover's side stops**: at an input, at the challenges before the place, and at
those of the sub-protocol's rounds. -/
def Side.stopAt (σ : Side S Cl V W X Pb) (φ : Face V W Pb) (w : W) (loc ds : List Fmt.Drawn) :
    Option Why :=
  rowStopAt (φ.sees w) σ.half.parts loc ds

/-! ## 4 The available tables -/

/-- The tables from which a sub-protocol's columns are read. -/
structure Env where
  /-- the stored tables' columns, by the statement's item and the position -/
  stored : Nat → Nat → Option (List UInt64)
  /-- the table behind a source, as in `readsOf` -/
  tree : Fmt.TreeSource → Option (Place × Table)
  /-- how many trees this chain has sent so far -/
  sent : Nat

/-- The same after rounds that were played: their tables are this chain's next own trees. -/
def Env.add (E : Env) (ps : List Played) : Env :=
  { E with
    tree := fun s =>
      match s with
      | .own n => if n < E.sent then E.tree (.own n) else ((tablesOf ps)[n - E.sent]?).bind id
      | .taken ch k => E.tree (.taken ch k)
    sent := E.sent + (tablesOf ps).length }

/-! ## 5 The four conditions -/

/-- **A check and four conditions on one honest side**, each at every fixed list of challenges that
the rounds can draw (`drawsFit`). It is a definition; whatever is proved of it is named where it is
proved; nothing is claimed here; and it is none of the library's goals. This file proves it of no
side, and states no rule for a list of sides (Honest/Law/Rule/Row.lean has one: it takes `Owed`,
Honest/Owed.lean). If the whole input, the index included, is chosen for the type `Xi` or
`Ky`, a simulator is given all of it. Only the condition `On` ties the columns in `front`,
`Before.stored`, `Mid.opened`, `Mid.loc` and `State.heard` to each other and to the input
(`Mid.opened` is tied to `front` by the premise of `exact`; to the input by On alone). So whatever
`On` allows in `front` reaches the simulator, private data included.

`φ`: the chain's face. `Bk`: the book. `ord`: the order of places (`ProverCoinCounts.clauses` uses `orderOf`).
`chain`, `firstTree`: the chain's number, from 0, and the number in the label of its first own tree,
as in `readsOf`. `A`, `B`: a condition before the place and one after it, on a whole run's coins,
the verifier's state, the state of the prover's run, and the available tables. `On`: for each part,
a condition at its start, on the blocks that it carries, on the state of the prover's run before it,
and on `front`, a `Before`; by type it reads no block that the part spends and no coin of the part's
own. `bud`: for each part, by its number, which positions may be read at given challenges. The
conditions can hold vacuously: a side of which one part always stops meets `plays` and `acc`, and a
part that its second stop always stops meets `exact` and `fresh`. What else the parameters leave
free is in this file's Limits.

`plays` says `B` at `y.2.took cols` (`Mid.took`, Frame.lean): the state after the rounds, with the
columns that the sub-protocol has read laid behind those opened so far. Where no columns are handed
(`opened = none`) none are laid. `ChainProgress.settle` (Walk.lean) lays the same into the walk's state.
`pre`: the declared rounds whose reads are handed, as `readsBefore` takes them. `Lettered.goodAt`
(Rule.lean) makes it from the chain's own list (`preOf`) and from the earlier chains' rounds, which
its caller lays. -/
structure Good (pre : List (Nat × Nat × List Fmt.DeclaredRound)) (φ : Face V W Pb)
    (σ : Side S Cl V W X Pb)
    (Bk : ProverCoinCounts) (ord : List Place)
    (chain firstTree : Nat) (A B : Coins Bk → S → Mid W X → Env → Prop)
    (On : (u : Member V W X Pb) → CsAll u.part.carries → Mid W X → Before → Prop)
    (bud : Nat → List Fmt.Drawn → List (List (List Nat)) → Prop) : Prop where
  /-- the list and the sub-protocol fit. Otherwise a part with a move too many would have that move
  dropped unseen, and its stops would never be asked after its last round, where `ready` rejects
  such a prover's side -/
  fits : σ.fits = true
  /-- Of the whole list, the playing. From A, at every run's coins k at which A holds, at every list
  of challenges at which no part stops, fall or not: the book lends the list its coins, no part
  returns an error, and the columns that the sub-protocol reads are available; and wherever the
  sub-protocol's own step accepts the rounds and these columns, B holds after it. Whether it accepts
  is not stated here. This is meant to carry the conditions before the places up to the first
  sub-protocol that rejects, whatever rejects. That no part stops is a hypothesis, as
  `ρ ∉ H.withheld w x` is in the library's `Honest.Acc`. So nothing is asked at a list at which a
  part stops: an error before that stop is not excluded (Ior/Honest.lean: "What it sends on the
  withheld set is not constrained in this file") -/
  plays : ∀ k s m E ds, A k s m E → drawsFit σ.block.rounds ds = true →
    σ.stopAt φ m.st.input m.loc ds = none →
    ∃ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c ∧
      play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y ∧
      fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds) [] =
        .ok cols ∧
      ∀ s' n, σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n) →
        B k s' (y.2.took cols) (E.add y.1)
  /-- Of the whole list, the verifier's acceptance. From A, where no part stops and the place's fall
  returns `none`: the sub-protocol's own step accepts what the list has played and the columns that
  it reads. By itself it holds vacuously where the lending, the playing or the columns fail: `plays`
  excludes that. With `plays` and a fall that always returns `none` this is what the library's
  `Honest.Acc` asks at one sub-protocol -/
  acc : ∀ k s m E ds, A k s m E → drawsFit σ.block.rounds ds = true →
    σ.stopAt φ m.st.input m.loc ds = none → σ.fall s ds = none →
    ∀ (c : RowCoins σ.half.parts) (y : List Played × Mid W X) (cols : List OpenedColumn),
      lendRow Bk (Bk.rowsOf chain) (k.look chain) σ.block.place σ.half.parts 0 = .ok c →
      play (σ.half.steps σ.block (φ.sees m.st.input) c) ds [] m = .ok y →
      fillCols (readsOf chain firstTree (E.add y.1).stored (E.add y.1).tree σ.block.rounds ds) [] =
        .ok cols →
      ∃ s' n, σ.block.step firstTree s (roundsOf y.1) cols = .ok (s', n)
  /-- `exact` is a condition on one part and its candidate simulator; it is not a theorem. It asks
  that what the part shows has the same distribution as what the simulator outputs. The part's side
  is taken over its own coins and its spent blocks of borrowed coins, all drawn uniformly and
  independently of everything before the part. The simulator's side is taken over the simulator's
  own coins. Fixed on both sides: the prover's input and state before the part (`m`), `front`, the
  carried blocks (`ca`), the part's challenges (`ds`) and the read positions (`asks`). The simulator
  is given five things: the input's public field, `front`, `ds`, `asks` and its own coins; it is
  given neither `ca` nor the rest of `m`. `front` holds earlier messages, earlier challenges and
  opened columns, those of the stored tables among them; in a real run these depend on the index.
  The condition is asked only where `On`, `bud`, `drawsFit` and `Before.holds` hold, and `front` and
  `m` agree on the earlier rounds and on the opened columns (below). It is not asked where the part
  is stopped by its second stop (`Part.stopAt` is `some .hid`). Where the first stop fires at the
  same point or earlier, `stopAt` reports the first, and the condition is still asked.
  `Before.holds` asks that `front` has a column for every read that the part's own rounds make, at
  `ds`, of a stored table or an earlier tree. In a real run the spent blocks are not fresh: their
  owner may already have shown values that depend on them. `fresh` is the condition on that owner,
  and this file states no rule that joins the two. All challenges are fixed in advance, as in the
  library's `Honest.ExactWith` (Ior/Honest.lean), which is the honest-verifier form. `m.opened` is
  what `front` holds for the reads of `pre`. Where `front` lacks one of these columns
  `Before.opened` is `none`: the condition is then asked at a state with `opened = none`, and a part
  that returns an error there shows `none`, so its simulator has to return `none` there too. -/
  exact : ∀ u ∈ σ.members, ∀ ca m front ds asks, On u ca m front → m.seen = front.seen →
    m.opened = front.opened (readsBefore pre front) →
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    front.holds chain firstTree (u.rounds.map (·.1)) ds = true →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes × CsAll u.part.spends)).map
        (fun c => σ.shows φ u (c.1, c.2, ca) m ds asks) =
      (Prob.unif (Cs u.sim.takes)).map fun c => u.tells φ c m.st.input front ds asks
  /-- `fresh` is a condition on one part, the owner, once for each part p; it is not a theorem. It
  asks that, over the owner's own coins, the blocks that p spends are uniform and independent of two
  things taken together. The two things are what the owner shows, and the owner's other coins that
  the book gives to p or to a part before p. In Lean it is one equation: the three have the same
  distribution when the first is replaced by fresh uniform coins. Everything else that the owner is
  given is fixed at any value: its input and state (`m`) and its own borrowed blocks (`sp`, `ca`).
  It is asked only at challenges that the owner's rounds can draw and at positions within `bud`. It
  is not asked where the owner is stopped by its second stop (`Part.stopAt` is `some .hid`). It is
  also asked at earlier challenges that no round can draw, and at values of `m` that no run reaches.
  -/
  fresh : ∀ u ∈ σ.members, ∀ (p : Addr) sp ca m ds asks,
    drawsFit (u.rounds.map (·.1)) ds = true → bud u.number ds asks →
    u.part.stopAt (φ.sees m.st.input) m.loc ds ≠ some .hid →
    (Prob.unif (Cs u.part.takes)).map (fun c =>
        (cutAll c (Bk.spentBy ⟨σ.block.place, u.number⟩ p), σ.shows φ u (c, sp, ca) m ds asks,
          cutAll c (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))) =
      (Prob.unif (CsAll ((Bk.spentBy ⟨σ.block.place, u.number⟩ p).map Ahead.named) ×
          Cs u.part.takes)).map fun a =>
        (some a.1, σ.shows φ u (a.2, sp, ca) m ds asks,
          cutAll a.2 (Bk.knownBy ord ⟨σ.block.place, u.number⟩ p))

end ProofFile.Honest

#print axioms ProofFile.Honest.numbered
#print axioms ProofFile.Honest.Played.isAt
#print axioms ProofFile.Honest.partIn
#print axioms ProofFile.Honest.Run.partAt
#print axioms ProofFile.Honest.Run.shownAt
#print axioms ProofFile.Honest.Run.askedAt
#print axioms ProofFile.Honest.Run.drawnAt
#print axioms ProofFile.Honest.Run.seenAt
#print axioms ProofFile.Honest.shownIn
#print axioms ProofFile.Honest.Run.storedAsked
#print axioms ProofFile.Honest.storedShown
#print axioms ProofFile.Honest.Run.beforeAt
#print axioms ProofFile.Honest.Before.treeCols
#print axioms ProofFile.Honest.Before.colAt
#print axioms ProofFile.Honest.Before.opened
#print axioms ProofFile.Honest.Before.drawnOf
#print axioms ProofFile.Honest.readsBefore
#print axioms ProofFile.Honest.Before.holds
#print axioms ProofFile.Honest.Fall
#print axioms ProofFile.Honest.fallOf
#print axioms ProofFile.Honest.Side
#print axioms ProofFile.Honest.Side.seated
#print axioms ProofFile.Honest.Side.half
#print axioms ProofFile.Honest.Side.fits
#print axioms ProofFile.Honest.Member
#print axioms ProofFile.Honest.membersOf
#print axioms ProofFile.Honest.Side.members
#print axioms ProofFile.Honest.shownOf
#print axioms ProofFile.Honest.Side.shows
#print axioms ProofFile.Honest.Member.tells
#print axioms ProofFile.Honest.Part.stopAt
#print axioms ProofFile.Honest.rowStopAt
#print axioms ProofFile.Honest.Side.stopAt
#print axioms ProofFile.Honest.Env
#print axioms ProofFile.Honest.Env.add
#print axioms ProofFile.Honest.Good
