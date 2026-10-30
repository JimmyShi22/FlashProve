-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Block.lean: the format in which a file's protocol is written, as an interactive oracle
proof: blocks, links, chains, a file's description; and the one general way from such a text to the
verifier's decision. Definitions, all with code, and four equations that hold by unfolding. It
imports Fmt/ and Decl/ alone, Johnson/Desc/Oracle.lean and Johnson/Desc/BookPlan.lean, which do the
like, and of Johnson/Desc/Step.lean the type `OpenedColumn`: no hash function is named.

A BLOCK SAYS SIDE BY SIDE who sends what, what is drawn, what is read, and what the verifier asks. A
protocol is a list of blocks: its schedule of rounds and its verifier come OUT OF ONE TEXT.

Beside the record `IOP` of the target document (its section 3): the document's field: ours.

  rounds: `Block.rounds`: the word is kept; its number is the list's length.

  logLength: `Block.oracles`; as a reading: `Block.logLength`.

  challengeBlocks: a reading of a round's entry: `Block.challengeBlocks`.

  verifierDecision, "read oracle position": data of a round: what it opens, at the positions drawn
  in it; as a reading: `Block.reads`.

  verifierDecision, "decide": `Block.decide`, block by block, with a carried record; then
  `FileDescription.fin`.

  the honest prover: absent here; three are written in Lean: E2E/TheHonestProver.lean (GAPS.md).

A `FileDescription` stands for the document's IOP for one file. `FileDescription.run` is its verifier's decision
ON THE VIEWS THAT THE COMPILER HANDS; the way into the compiler, and what ties the two, is
Johnson/Desc/BlockSlot.lean's.

The file's order: 1 the records · 2 the general functions on a block · 3 links and chains as flat
lists · 4 the tests on the plan · 5 the decision · 6 limits. Controls: Johnson/Desc/BlockToy.lean.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Step
import Johnson.Desc.BookPlan
import Fmt.Rules6Draws
import Decl.Declared

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc

/-! ## 1 The records -/

/-- The kinds of block, and what is the fold's own. -/
inductive KindName where
  | K1 | K2 | K3 | K4 | K5 | K6 | K7 | K8 | K9 | K10 | K11 | K12 | K13 | K14 | K15
  /-- no kind: a row of the fold's own text (a link's frame; a chain's end) -/
  | frame
  deriving DecidableEq, Repr, Inhabited

/-- Where a block stands: three storeys. -/
structure Place where
  /-- 1, 2 or 3 -/
  chain : Nat
  /-- `none`: in front of, or behind, the links -/
  link : Option Nat
  /-- its number inside the link, or at the chain's end -/
  piece : Nat
  kind : KindName
  deriving DecidableEq, Repr, Inhabited

/-- **A block at one place.** S: the carried record. Cl: the type of a claim. -/
structure Block (S Cl : Type) where
  /-- for a refusal's words -/
  name : String
  place : Place
  /-- TESTS ON THE PLAN ALONE: no view, no record -/
  planOk : Bool
  /-- ROUNDS, and with them READS: for each round its entry of the plan (its name; what the message
  holds; what is drawn), and the parts of stored tables and the trees that are opened at the
  positions drawn in it -/
  rounds : List Fmt.DeclaredRound
  /-- ROUNDS: for each round, for each root that it sends: the oracle message beneath it -/
  oracles : List (List Oracle)
  /-- FIXED BEFORE THE DRAW: the oracle messages that must have been sent, and where they are
  sampled have had their sample answered, before this block's first draw: (the chain: 1, 2 or 3; the
  message's number in its chain's order of sending, from 0). IT IS THE BLOCK THAT DRAWS A CHALLENGE
  THAT NAMES THE MESSAGES WHICH ANY TEST HOLDS AGAINST THAT CHALLENGE, also a later block's test.
  A BLOCK THAT SENDS A SAMPLED MESSAGE DOES NOT NAME IT HERE FOR THE DRAW OF ITS OWN SEEDS: the
  answers come behind the seeds, so the test would refuse an honest plan; inside one block the order
  "root, then seeds, then answers" is that of its own rounds -/
  before : List (Nat × Nat)
  /-- DECIDES: from the record, its own rounds as a view shows them (no root; no sealed digest),
  and just the columns that it is owed, grouped as the openings are (one group for each stored part,
  then each tree, of each round), each column with its position: the next record, or a refusal
  under the name of the test that refused -/
  decide : S → List Fmt.RoundView → List (List (Nat × List UInt64)) → Except String S
  /-- CLAIMS: named runs: each from the number of claims that the link has gathered so far and the
  record, which holds what was heard, to claims and the record behind them, or a refusal. THERE IS
  NO DEFAULT: a kind that has none writes []; one that forgets its run does not compile -/
  claims : List (String × (Nat → S → Except String (List Cl × S)))
  /-- BEHIND THE BATCHING: named runs of a second sort: tests on, and writings into, the batched
  form as it stands in the record behind the adding: the record handed on, or a refusal. No default
  either -/
  after : List (String × (S → Except String S))

/-- A kind: a place's public parameters to the block there. P HOLDS NUMBERS OF THE PLACE, NEVER
ENTRIES OR DECLARED ROUNDS: else the test of the blocks' rounds against the plan's is idle. -/
abbrev Kind (P S Cl : Type) : Type := P → Block S Cl

/-- A host: a kind that draws a point at which other kinds' identities are tested too: it takes
these, its guests, as a list. G: the type of a guest identity: a letter here: a polynomial in values
that are sent or fixed before the first of the host's rounds that draws a coordinate which the guest
borrows (the point may be drawn over several rounds, and a guest may borrow some of its coordinates
alone). -/
abbrev KindWithGuestIdentities (P G S Cl : Type) : Type := P → List G → Block S Cl

/-- **A link**: the second storey. A maker of a flat list (`Link.blocksInOrder`). -/
structure Link (S Cl : Type) where
  name : String
  chain : Nat
  number : Nat
  /-- what is laid at the link's first place -/
  lay : S → Except String S
  /-- the places in front of the batching draw -/
  hear : List (Block S Cl)
  /-- which block's which run of claims, in order; blocks of `hear` from 0. IT IS MEANT TO BE THE
  PROTOCOL's ORDER, LAID WHOLE: `orderOk` holds it against what the blocks of `hear` state, and
  nothing here holds it against the protocol (see the Limits, THE ORDER) -/
  order : List (Nat × String)
  /-- A TEST BEHIND EACH RUN OF CLAIMS: it is handed the run as the order names it, that run's own
  list of claims, and the record behind the run. NO DEFAULT: a link that has none writes
  `fun _ _ _ => .ok ()` with its own hand -/
  each : Nat × String → List Cl → S → Except String Unit
  /-- the like for the runs behind the batching. NO DEFAULT: a link that has
  none writes [] with its own hand -/
  orderAfter : List (Nat × String)
  /-- the batching: it is handed the link's claims, as one function -/
  batch : (S → Except String (List Cl × S)) → Block S Cl
  /-- THE TESTS BEHIND THE ADDING: tests on the record as it stands behind the batching's block. The
  frame's block "behind the batching" asks them, IN FRONT OF the runs of `orderAfter`. THEY CANNOT
  TURN THE RECORD, BY TYPE: what must write is a run of `orderAfter`, and so is a test that reads
  what such a run has written. NO DEFAULT: a link cannot be
  made without them; one that has none writes `fun _ => .ok ()` with its own hand -/
  tests : S → Except String Unit
  /-- the closing -/
  close : List (Block S Cl)
  /-- the link's part of the record ends here -/
  clear : S → Except String S

/-- **A chain**: a maker of a flat list (`Chain.blocksInOrder`). ITS FIRST AND ITS LAST
BLOCK ARE FIELDS WITHOUT A DEFAULT: a chain cannot be made without them. The type shuts forgetting,
not emptiness: a block that asks nothing still fits either field. -/
structure Chain (S Cl : Type) where
  /-- the chain's front: its public tests, in a block without a round; or the chain's first working
  block, if that has no round. A chain that has neither lays a quiet block here, and its maker says
  so: three fronts need not be three sets of tests. It may be of the kind `frame`. Nothing asks that
  it has no round -/
  first : Block S Cl
  /-- what else stands in front of the links -/
  front : List (Block S Cl)
  links : List (Link S Cl)
  /-- what else stands behind the links -/
  back : List (Block S Cl)
  /-- the chain's end. Of a sealed chain it declares the sealing round; of an unsealed one it may be
  without a round -/
  last : Block S Cl

/-- **A file's description.** Xi: the instance. EACH CHAIN HAS A STATE OF ITS OWN: so a block of one
chain cannot read what another chain laid, by type; and the chains are held as chains: so no flat
list is typed by hand. -/
structure FileDescription (Xi : Type) where
  S₁ : Type
  S₂ : Type
  S₃ : Type
  Cl : Type
  /-- THE PLAN's OWN DECLARED ROUNDS of the three chains, WHOLE: each round's entry, the stored
  parts and the trees that it opens, each tree with its source: made of the public files where the
  description is made (Johnson/G/RoundsOfPlan.lean: `declPOf` | `declKOf`) -/
  plans : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound
  /-- the stored table's depth, off the plan -/
  tableDepth : Nat
  /-- THE TABLE OF PLACES, OFF THE PLAN: for every block of the three flat lists, in their order,
  its place and its number of rounds; a block without a round has a row too, with 0. IT IS WORTH ITS
  FIELD ONLY IF IT IS MADE OF THE PUBLIC FILES BY ANOTHER FILE THAN THE ONE THAT WRITES THE BLOCKS,
  INDEPENDENTLY OF IT: else `wantedOk` holds a list against itself. Blocks that are joined by
  `andThen` have one row, with both blocks' rounds, at the joint's place: the first one's, unless
  the maker stamps another. No default -/
  wanted : List (Place × Nat)
  /-- WHICH MESSAGES A BLOCK MUST NAME IN `before`, OFF THE PLAN: (the block's place, the messages
  as in `before`). Made as `wanted` is, independently of the block's file. A ROW THAT NAMES
  A MESSAGE OF AN EARLIER CHAIN THAN THE BLOCK's IS IDLE AS A TEST OF THE ORDER: `beforeOk` asks of
  such a message only that it is sent (see the Limits). Blocks that are joined by `andThen` stand at
  one place alone (the first one's, unless the maker stamps another): the table's maker must know
  the joints. A block is held at its FIRST draw: a message that it sends itself behind that draw
  cannot be owed by it. No default -/
  owed : List (Place × List (Nat × Nat))
  /-- the tests on the plan that tie chains to each other -/
  fileOk : Bool
  /-- the test on the instance alone -/
  okStart : Xi → Bool
  /-- the instance without what is asked of the proof (the next token) -/
  XiPub : Type
  pub : Xi → XiPub
  /-- the first and the shared chain's first states: of the instance's public part alone -/
  start₁ : XiPub → S₁
  start₂ : XiPub → S₂
  /-- the second chain's first state: what it takes of the two earlier chains' ends; it may
  refuse -/
  start₃ : XiPub → S₁ → S₂ → Except String S₃
  first : Chain S₁ Cl
  shared : Chain S₂ Cl
  second : Chain S₃ Cl
  /-- the last test: it is handed the instance and the three ends, and compares what was heard with
  what is asked -/
  fin : Xi → S₁ → S₂ → S₃ → Bool

variable {Xi S Cl : Type}

/-! ## 2 The general functions on a block: written once, for all kinds -/

/-- A value that must be there, under the name of the test that it is. By it a text that is typed
with `Option` is laid under one name: `decide := fun s rs gs => named "K4" (inner s rs gs)`. -/
def named {α : Type} (name : String) : Option α → Except String α
  | some x => .ok x
  | none => .error name

/-- A test, under its name. -/
def need (name : String) (b : Bool) : Except String Unit := if b then .ok () else .error name

/-- What declared rounds read, of what they drew: a group for each stored part, then each tree, of
each round: the columns' key, position and width; at the list of the drawn positions in the tree's
own range, by the shape that the round itself states; each position once, in increasing order.
firstTree: the number in the label of the chain's first own tree: a tree's key is its own number
less that, cut off at 0. -/
def groupsOf (firstTree : Nat) :
    List Fmt.DeclaredRound → List Fmt.Drawn → List (List (Nat × Nat × Nat))
  | d :: ds, R :: Rs =>
    (d.stored.map fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (Fmt.storedKey s.item, x, s.sh.W)) ++
    (d.opens.map fun o =>
      (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x => (o.1.tree - firstTree, x, o.1.W)) ++
    groupsOf firstTree ds Rs
  | _, _ => []

/-- READS: a reading of ROUNDS: key, position and width of every column that the block is owed,
group by group. -/
def Block.reads (firstTree : Nat) (b : Block S Cl) (draws : List Fmt.Drawn) :
    List (List (Nat × Nat × Nat)) :=
  groupsOf firstTree b.rounds draws

/-- Which item of a message a value is. -/
def itemOf : Fmt.ItemValue → Fmt.Item
  | .f _ => .f
  | .e _ => .e
  | .word _ => .word
  | .root _ => .root
  | .answer _ => .answer

/-- The drawn elements that a round's entry marks as never 0 are not 0, AS RAW WORDS: the three
words are not all 0. That such an element is not 0 IN THE FIELD follows only where its words are
below the prime: `viewWordsBelowPrime`, which `runCore` asks first; a law over `roundsFit` or `Block.step` that
wants "not 0 in the field" carries `viewWordsBelowPrime` as a premise. WHICH they are is the
format's own word: `Fmt.dsElems e k` lists a round's drawn elements in the order of the view's
record, each as plain or as never 0, from the entry and the round's kind (in a round of seeds each
seed's factor; in every other kind the last so many); the kind follows from the entry's name
(`Fmt.kindOf`). A round whose name the format does not know is refused. -/
def drawsMarkedNonzeroHaveNonzeroWords (d : Fmt.DeclaredRound) (r : Fmt.RoundView) : Bool :=
  (Fmt.kindOf d.entry.name).any fun k =>
    ((Fmt.dsElems d.entry k).zip r.drawn.elems).all fun x => x.1 != .elemNZ || x.2 != (0, 0, 0)

/-- Each round shows just the items that its entry cuts, but for the roots, which are in no view
(Fmt/View.lean); it drew as many elements, positions and matrix entries as its entry says; EVERY
POSITION THAT IT DREW IS BELOW 2 ^ logN, the range that its entry states (Fmt/Plan.lean: "positions
are drawn below 2 ^ logN"); EVERY MATRIX ENTRY THAT IT DREW IS -1, 0 OR 1; AND `drawsMarkedNonzeroHaveNonzeroWords`. False if the
two lists differ in length. -/
def roundsFit : List Fmt.DeclaredRound → List Fmt.RoundView → Bool
  | d :: ds, r :: rs =>
    r.vals.map itemOf == d.items.filter (· != .root) && r.drawn.elems.length == d.entry.drawE &&
      r.drawn.poss.length == d.entry.poss && r.drawn.trits.length == d.entry.trits &&
      r.drawn.poss.all (· < 2 ^ d.entry.logN) &&
      r.drawn.trits.all (fun t => t == -1 || t == 0 || t == 1) && drawsMarkedNonzeroHaveNonzeroWords d r && roundsFit ds rs
  | [], [] => true
  | _, _ => false

/-- Columns laid into groups of the given lengths. -/
def regroup : List Nat → List OpenedColumn → List (List (Nat × List UInt64))
  | n :: ns, cols => ((cols.take n).map fun c => (c.2.1, c.2.2)) :: regroup ns (cols.drop n)
  | [], _ => []

/-- A round without the sealed digest: what a kind is shown. -/
def noDigest (r : Fmt.RoundView) : Fmt.RoundView := { r with drawn := { r.drawn with digest := none } }

/-- **The block as a step.** A refusal, under a name: "the rounds" where `roundsFit` says no; "the
columns" where the view's next columns are not, in key, position and width, those that are read, or
are fewer; `decide`'s own where it refuses. Else the next record, and as many columns taken as are
read. So no kind counts or matches columns, sees a column that it is not owed, or leaves one that it
is owed. `decide` is shown its rounds without the sealed digest. -/
def Block.step (firstTree : Nat) (b : Block S Cl) (s : S) (rs : List Fmt.RoundView) (cols : List OpenedColumn) :
    Except String (S × Nat) := do
  need "the rounds" (roundsFit b.rounds rs)
  let groups := groupsOf firstTree b.rounds (rs.map (·.drawn))
  let want := groups.flatMap id
  let got := cols.take want.length
  need "the columns" (got.map (fun c => (c.1, c.2.1, c.2.2.length)) == want)
  let s' ← b.decide s (rs.map noDigest) (regroup (groups.map (·.length)) got)
  pure (s', want.length)

/-- The number of a block's groups: its rounds' stored parts and trees. -/
def Block.openings (b : Block S Cl) : Nat :=
  b.rounds.foldl (fun n r => n + r.stored.length + r.opens.length) 0

/-- Two blocks as one, under the first one's place: the rounds and the groups are cut between them.
-/
def Block.andThen (name : String) (p q : Block S Cl) : Block S Cl :=
  { name := name, place := p.place, planOk := p.planOk && q.planOk
    rounds := p.rounds ++ q.rounds, oracles := p.oracles ++ q.oracles
    before := p.before ++ q.before
    decide := fun s rs gs =>
      (p.decide s (rs.take p.rounds.length) (gs.take p.openings)).bind fun s' =>
        q.decide s' (rs.drop p.rounds.length) (gs.drop p.openings)
    claims := p.claims ++ q.claims, after := p.after ++ q.after }

/-- A block that is typed at a part S of a wider record T, as a block at T: it reads its part by
`get` and lays it back by `set`. That it turns nothing else of T is `set`'s matter: nothing here
asks that `get` and `set` fit each other. -/
def Block.lift {T : Type} (get : T → S) (set : T → S → T) (b : Block S Cl) : Block T Cl :=
  { name := b.name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before
    decide := fun t rs gs => (b.decide (get t) rs gs).map (set t)
    claims := b.claims.map fun c => (c.1, fun n t => (c.2 n (get t)).map fun y => (y.1, set t y.2))
    after := b.after.map fun c => (c.1, fun t => (c.2 (get t)).map (set t)) }

/-- The like for a part that is there only at times (a link's own part): `get?` says whether it is;
where it is not, the block, its claims and its runs behind the batching REFUSE. -/
def Block.liftPart {T : Type} (get? : T → Option S) (set : T → S → T) (b : Block S Cl) :
    Block T Cl :=
  { name := b.name, place := b.place, planOk := b.planOk, rounds := b.rounds, oracles := b.oracles
    before := b.before
    decide := fun t rs gs => (named "the part is not there" (get? t)).bind fun p =>
      (b.decide p rs gs).map (set t)
    claims := b.claims.map fun c => (c.1, fun n t =>
      (named "the part is not there" (get? t)).bind fun p =>
        (c.2 n p).map fun y => (y.1, set t y.2))
    after := b.after.map fun c => (c.1, fun t =>
      (named "the part is not there" (get? t)).bind fun p => (c.2 p).map (set t)) }

/-- A block whose own record T is born and dies inside it: `enter` makes it of the record S, the
block b runs at it, `leave` lays what is to stay back into S. Such a block can have neither claims
nor runs behind the batching, which would want T outside: its test on the plan asks that b has none.
-/
def Block.inside {T : Type} (enter : S → Except String T) (b : Block T Cl)
    (leave : S → T → Except String S) : Block S Cl :=
  { name := b.name, place := b.place, planOk := b.planOk && b.claims.isEmpty && b.after.isEmpty
    rounds := b.rounds, oracles := b.oracles, before := b.before
    decide := fun s rs gs => (enter s).bind fun t => (b.decide t rs gs).bind (leave s)
    claims := [], after := [] }

/-- A block that has no run of claims, at another type of claims: the same block. ITS TEST ON THE
PLAN ASKS THAT IT HAS NONE: a run of claims cannot be carried to another type. The runs behind the
batching, which name no claim, stay: inside a link's `hear` the frame runs them; outside a link
`Chain.blocksInOrder` lets a block that has any fail its test on the plan: so through `Chain.retype` they
stay only to be refused. -/
def Block.retype {Cl' : Type} (b : Block S Cl) : Block S Cl' :=
  { name := b.name, place := b.place, planOk := b.planOk && b.claims.isEmpty, rounds := b.rounds
    oracles := b.oracles, before := b.before, decide := b.decide, claims := [], after := b.after }

/-- The target document's word: the log-length of the oracle message beneath root i of a round. -/
def Block.logLength (b : Block S Cl) (round i : Nat) : Option Nat :=
  (b.oracles[round]?).bind fun l => (l[i]?).map (·.logLength)

/-- The target document's word: the blocks of 256 bits of a round's challenge; `none` if there is no
such round or the format does not know its name. -/
def Block.challengeBlocks (b : Block S Cl) (round : Nat) : Option Nat :=
  (b.rounds[round]?).bind fun r =>
    (Fmt.kindOf r.entry.name).map fun k => Fmt.blocksFor (Fmt.wordsAtMost r.entry k)

/-! ## 3 Links and chains as flat lists -/

/-- A block without a round, of the fold's own text: the record's change, or a refusal. -/
def roundlessBlock (name : String) (chain : Nat) (link : Option Nat) (piece : Nat)
    (f : S → Except String S) : Block S Cl :=
  { name := name, place := ⟨chain, link, piece, .frame⟩, planOk := true, rounds := [], oracles := []
    before := []
    decide := fun s _ _ => f s
    claims := [], after := [] }

/-- One run of claims, behind what is gathered so far: x: the claims so far and the record; o: the
run, as an order names it: (n, name): the run `name` of block number n, from 0. The run is handed
the number of claims gathered so far, and the record; behind it `each` is asked, of that run's own
list and the record behind the run. A refusal where the run refuses, under the run's name and its
own words; where `each` refuses, under the run's name, "behind the run" and its own words; or where
there is no such run. -/
def claimsInStep (each : Nat × String → List Cl → S → Except String Unit) (bs : List (Block S Cl))
    (x : List Cl × S) (o : Nat × String) : Except String (List Cl × S) :=
  (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.claims.lookup o.2)).bind fun run =>
    match run x.1.length x.2 with
    | .ok y =>
      match each o y.1 y.2 with
      | .ok _ => .ok (x.1 ++ y.1, y.2)
      | .error e => .error (o.2 ++ ": behind the run: " ++ e)
    | .error e => .error (o.2 ++ ": " ++ e)

/-- The runs of a link's claims in the order that the link states, each by `claimsInStep`, the
record handed from each to the next; the first refusal ends it. -/
def claimsInBy (each : Nat × String → List Cl → S → Except String Unit) (bs : List (Block S Cl))
    (order : List (Nat × String)) (s : S) : Except String (List Cl × S) :=
  order.foldl (fun acc o => acc.bind fun x => claimsInStep each bs x o) (.ok ([], s))

/-- The same with no test behind a run. -/
def claimsIn (bs : List (Block S Cl)) (order : List (Nat × String)) (s : S) :
    Except String (List Cl × S) :=
  claimsInBy (fun _ _ _ => .ok ()) bs order s

/-- The runs behind the batching, in the order that the link states; the record is handed from each
to the next. A refusal as in `claimsIn`. -/
def afterIn (bs : List (Block S Cl)) (order : List (Nat × String)) (s : S) : Except String S :=
  order.foldl (fun acc o => acc.bind fun x =>
    (named (o.2 ++ ": no such run") ((bs[o.1]?).bind fun b => b.after.lookup o.2)).bind fun run =>
      match run x with
      | .ok y => .ok y
      | .error e => .error (o.2 ++ ": " ++ e)) (.ok s)

/-- No name stands twice in `all`; every member of `all` stands in the order just once; and the
order names no other. -/
def namesOk (all order : List (Nat × String)) : Bool :=
  all.all (fun r => all.count r == 1 && order.count r == 1) && order.all fun o => all.contains o

/-- No block has two runs of claims of one name (also behind `andThen`); every named run of every
block stands in the order just once; and the order names no other. -/
def orderOk (bs : List (Block S Cl)) (order : List (Nat × String)) : Bool :=
  namesOk (bs.zipIdx.flatMap fun b => b.1.claims.map fun c => (b.2, c.1)) order

/-- The like for the runs behind the batching. -/
def orderAfterOk (bs : List (Block S Cl)) (order : List (Nat × String)) : Bool :=
  namesOk (bs.zipIdx.flatMap fun b => b.1.after.map fun c => (b.2, c.1)) order

/-- A block has neither claims nor runs behind the batching. -/
def Block.hasNoClaimsAndNothingAfter (b : Block S Cl) : Bool := b.claims.isEmpty && b.after.isEmpty

/-- The frame's step behind the batching: the link's tests behind the adding, then the runs behind
the batching, in the link's order. A refusal of the tests is headed "the tests behind the adding".
-/
def Link.runBehind (L : Link S Cl) (s : S) : Except String S :=
  match L.tests s with
  | .ok _ => afterIn L.hear L.orderAfter s
  | .error e => .error ("the tests behind the adding: " ++ e)

/-- **The link's flat list**: laid · hear · the batching at the claims of hear, in the link's order,
with the link's test behind each run · the tests behind the adding, then the runs behind the
batching, in the link's order · close · cleared. THE FRAME, NOT THE BATCHING, RUNS WHAT STANDS
BEHIND IT. The first of these blocks holds the link's own test on the plan: `orderOk`,
`orderAfterOk`, and neither the batching nor a block of close has claims or such runs. -/
def Link.blocksInOrder (L : Link S Cl) : List (Block S Cl) :=
  { roundlessBlock (L.name ++ ": laid") L.chain (some L.number) 0 L.lay with
      planOk := orderOk L.hear L.order && orderAfterOk L.hear L.orderAfter &&
        L.close.all Block.hasNoClaimsAndNothingAfter && (L.batch (claimsInBy L.each L.hear L.order)).hasNoClaimsAndNothingAfter } ::
    L.hear ++ [L.batch (claimsInBy L.each L.hear L.order),
      roundlessBlock (L.name ++ ": behind the batching") L.chain (some L.number) (L.hear.length + 2)
        L.runBehind] ++ L.close ++
    [roundlessBlock (L.name ++ ": cleared") L.chain (some L.number) (L.hear.length + L.close.length + 3)
      L.clear]

/-- **The chain's flat list**: first · front · the links · back · last. A block outside the links
that has claims or runs behind a batching, which nobody would gather, fails its test on the plan. -/
def Chain.blocksInOrder (c : Chain S Cl) : List (Block S Cl) :=
  let bare := fun b : Block S Cl => { b with planOk := b.planOk && b.hasNoClaimsAndNothingAfter }
  bare c.first :: c.front.map bare ++ c.links.flatMap Link.blocksInOrder ++ c.back.map bare ++ [bare c.last]

/-- A chain without links, at another type of claims: each of its blocks by `Block.retype`. ITS
FIRST BLOCK's TEST ON THE PLAN ASKS THAT THE CHAIN HAS NO LINK: a link's batching is typed at its
claims and cannot be carried. -/
def Chain.retype {Cl' : Type} (c : Chain S Cl) : Chain S Cl' :=
  let f : Block S Cl' := c.first.retype
  { first := { f with planOk := f.planOk && c.links.isEmpty }, front := c.front.map Block.retype
    links := [], back := c.back.map Block.retype, last := c.last.retype }

/-! ## 4 The tests on the plan -/

/-- The three chains' declared rounds: what a compiler takes. -/
def FileDescription.roundsDeclaredByBlocks (F : FileDescription Xi) :
    List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound :=
  (F.first.blocksInOrder.flatMap (·.rounds), F.shared.blocksInOrder.flatMap (·.rounds),
    F.second.blocksInOrder.flatMap (·.rounds))

/-- A list of blocks as rows of the table of places: name, place, number of rounds. -/
def placesOf (bs : List (Block S Cl)) : List (String × Place × Nat) :=
  bs.map fun b => (b.name, b.place, b.rounds.length)

/-- The table of places. -/
def FileDescription.places (F : FileDescription Xi) : List (String × Place × Nat) :=
  placesOf F.first.blocksInOrder ++ placesOf F.shared.blocksInOrder ++ placesOf F.second.blocksInOrder

/-- `oracles` has a list for each round, with a member for each of the round's roots, and at every
root the tenants' words add up to the symbol's (so a root without a tenant is refused, unless its
symbol has no word) and each tenant's degree is 1 or 3. -/
def Block.shaped (b : Block S Cl) : Bool :=
  b.oracles.length == b.rounds.length &&
    (b.rounds.zip b.oracles).all fun x => x.2.length == x.1.entry.roots &&
      x.2.all fun o => (o.tenants.map fun t => t.main + t.mask).sum == o.words &&
        o.tenants.all fun t => t.degree == 1 || t.degree == 3

/-- The shapes at which the trees that a chain sends itself are opened, anywhere in the three lists:
the tree's number in its chain, log-length, width. chain: from 0. -/
def openedOwn (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound) (chain : Nat) :
    List (Nat × Nat × Nat) :=
  [D.1, D.2.1, D.2.2].zipIdx.flatMap fun c => (c.1.flatMap (·.opens)).filterMap fun o =>
    match o.2 with
    | .own n => if c.2 == chain then some (n, o.1.a, o.1.W) else none
    | .taken ch sent => if ch == chain then some (sent, o.1.a, o.1.W) else none

/-- The number in the label of the third chain's first own tree: behind the first chain's trees and
the one tree that is taken over from the second chain. -/
def FileDescription.lastChainFirstTreeNumber (F : FileDescription Xi) : Nat :=
  F.roundsDeclaredByBlocks.1.foldl (fun n r => n + r.entry.roots) 0 + 1

/-- At every opening the number in the tree's label is the one that its source says: the n-th own
tree of the first or the shared chain has the number n, of the second chain `lastChainFirstTreeNumber` + n; a tree
that is taken over keeps its sender's number; and the second chain alone takes trees over, from the
two earlier chains. -/
def FileDescription.labelsOk (F : FileDescription Xi) : Bool :=
  [F.roundsDeclaredByBlocks.1, F.roundsDeclaredByBlocks.2.1, F.roundsDeclaredByBlocks.2.2].zipIdx.all fun c => (c.1.flatMap (·.opens)).all fun o =>
    match o.2 with
    | .own n => o.1.tree == (if c.2 == 2 then F.lastChainFirstTreeNumber + n else n)
    | .taken ch sent => c.2 == 2 && decide (ch < 2) && o.1.tree == sent

/-- All of a chain's blocks pass their own tests on the plan and are shaped. -/
def blocksOk (bs : List (Block S Cl)) : Bool := bs.all fun b => b.planOk && b.shaped

/-- What a chain's blocks say of the trees that they send, in the order of sending. -/
def sentOf (bs : List (Block S Cl)) : List (Nat × Nat) :=
  bs.flatMap fun b => b.oracles.flatMap fun l => l.map fun o => (o.logLength, o.words)

/-- The number of the round that sends the oracle message number n of a chain, both from 0. -/
def sendRound : List Fmt.DeclaredRound → Nat → Option Nat
  | [], _ => none
  | r :: l, n => if n < r.entry.roots then some 0 else (sendRound l (n - r.entry.roots)).map (· + 1)

/-- A round draws an element, a position or a matrix entry. -/
def drawsAny (r : Fmt.DeclaredRound) : Bool := r.entry.drawE + r.entry.poss + r.entry.trits != 0

/-- Of the blocks of the chain c (from 0), which begin at the chain's round number `from'`: every
message that a block names in `before` stands in front of the block's first draw. Of the block's own
chain: it is sent in a round not later than the one of that draw (a round's message stands in front
of its draw). Of an earlier chain: it is sent there. Of a later chain, or of none: refused. Where
one of the message's tenants is sampled, a round behind the one that sends it, and likewise in front
of the draw, has sample answers in its message. A block that draws nothing is held at the round
behind its last. O: what the three chains' blocks say of the messages that they send. -/
def beforeAt (D : List Fmt.DeclaredRound × List Fmt.DeclaredRound × List Fmt.DeclaredRound)
    (O : List Oracle × List Oracle × List Oracle) (c : Nat) : Nat → List (Block S Cl) → Bool
  | _, [] => true
  | from', b :: l =>
    (b.before.all fun m =>
      let ds := if m.1 == 1 then D.1 else if m.1 == 2 then D.2.1 else D.2.2
      let os := if m.1 == 1 then O.1 else if m.1 == 2 then O.2.1 else O.2.2
      let last := if m.1 == c + 1 then from' + b.rounds.findIdx drawsAny else ds.length
      match sendRound ds m.2 with
      | none => false
      | some i =>
        decide (1 ≤ m.1) && decide (m.1 ≤ c + 1) && decide (i ≤ last) &&
          (!((os[m.2]?).any fun o => o.tenants.any (·.sampled)) ||
            ds.zipIdx.any fun r =>
              r.1.entry.answers != 0 && decide (i < r.2) && decide (r.2 ≤ last))) &&
    beforeAt D O c (from' + b.rounds.length) l

/-- The oracle messages that a chain's blocks send, in the order of sending. -/
def oraclesOf (bs : List (Block S Cl)) : List Oracle := bs.flatMap fun b => b.oracles.flatMap id

/-- The like of the whole file. -/
def FileDescription.beforeOk (F : FileDescription Xi) : Bool :=
  let O := (oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder)
  beforeAt F.roundsDeclaredByBlocks O 0 0 F.first.blocksInOrder && beforeAt F.roundsDeclaredByBlocks O 1 0 F.shared.blocksInOrder &&
    beforeAt F.roundsDeclaredByBlocks O 2 0 F.second.blocksInOrder

/-- What the three chains' blocks say of the roots that they send, for `BookPlan`. -/
def FileDescription.roots (F : FileDescription Xi) : BookPlan.SentOraclesByChain :=
  [oraclesOf F.first.blocksInOrder, oraclesOf F.shared.blocksInOrder, oraclesOf F.second.blocksInOrder]

/-- **Who may share a tree, and where a tree may be opened**: the clauses of `BookPlan`, at
the description's declared rounds and at what its blocks say of the roots. -/
def FileDescription.treeSharingOk (F : FileDescription Xi) : Bool := BookPlan.allClausesHold F.roundsDeclaredByBlocks F.roots

/-- The name of the first block of a list that fails its own test on the plan or is not shaped. -/
def firstBad (bs : List (Block S Cl)) : Option String :=
  (bs.find? fun b => !(b.planOk && b.shaped)).map (·.name)

/-- Every block of the n-th chain's list says that it stands in chain n, and no two blocks of a file
stand at one place (chain, link, number). -/
def FileDescription.placesOk (F : FileDescription Xi) : Bool :=
  let inChain := fun (n : Nat) (l : List (String × Place × Nat)) => l.all fun p => p.2.1.chain == n
  let all := F.places.map fun p => (p.2.1.chain, p.2.1.link, p.2.1.piece)
  inChain 1 (placesOf F.first.blocksInOrder) && inChain 2 (placesOf F.shared.blocksInOrder) &&
    inChain 3 (placesOf F.second.blocksInOrder) &&
    all.all fun x => all.count x == 1

/-- **What a round reads, held against what its entry draws.** A round draws positions just if it
reads: it opens a stored part or a tree. A tree is read at every position that the round draws
(`groupsOf`). Stored parts stand alone in their round, in the order of the statement's items, no
item twice (`Fmt.increasing`: so which table a part reads cannot be exchanged); each takes at least
one draw, and together they take the round's draws from the first to the last, each once, without a
gap (`Fmt.partsFrom`, the format's own function: Fmt/Rules8X.lean, `storedOk`). A stored part's
shape says that it is stored, and is no deeper than the round's range (of a tree `BookPlan`'s clause
"range" asks that); a tree's shape says that it is not stored. OUT OF THE
SAME `storedOk`: a stored part's label says tree 0; and the width of every stored part and of every
tree that is opened is at least 1 (a part of width 0 would read empty columns) and below 2 ^ 24.
With `groupsOf`, which reads a tree
at every position drawn and a stored part at its share of them, every position that an entry counts
is read somewhere. -/
def readsFit (r : Fmt.DeclaredRound) : Bool :=
  ((r.entry.poss != 0) == (!r.stored.isEmpty || !r.opens.isEmpty)) &&
    (r.stored.isEmpty ||
      (r.opens.isEmpty && Fmt.increasing (r.stored.map (·.item)) &&
        Fmt.partsFrom 0 r.stored == some r.entry.poss &&
        r.stored.all fun t =>
          decide (1 ≤ t.count) && t.sh.stored && decide (t.sh.a ≤ r.entry.logN) &&
            t.sh.tree == 0 && decide (1 ≤ t.sh.W) && decide (t.sh.W < 2 ^ 24))) &&
    r.opens.all fun o => !o.1.stored && decide (1 ≤ o.1.W) && decide (o.1.W < 2 ^ 24)

/-- `readsFit` at every round of the three chains. -/
def FileDescription.readsOk (F : FileDescription Xi) : Bool :=
  (F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2).all readsFit

/-- The first chain's last block has a round. `runEnd` lays the sealing round back behind the first
view's rounds: so the block that takes it must be the chain's last, and must itself declare it.
Behind the other two views `runEnd` lays nothing back. -/
def FileDescription.sealLast (F : FileDescription Xi) : Bool := !F.first.last.rounds.isEmpty

/-- What `oracles` says of a tree where it is sent agrees with the shape at every opening of it; and
every tree that is sent is opened somewhere. -/
def FileDescription.sentFit (F : FileDescription Xi) : Bool :=
  [sentOf F.first.blocksInOrder, sentOf F.shared.blocksInOrder, sentOf F.second.blocksInOrder].zipIdx.all fun c =>
    let opened := openedOwn F.roundsDeclaredByBlocks c.2
    opened.all (fun o => c.1[o.1]? == some (o.2.1, o.2.2)) &&
      (List.range c.1.length).all fun n => opened.any fun o => o.1 == n

/-- **The tests on the plan, but for the seal's**, which a file of one unsealed chain cannot meet:
`fileOk`; all blocks' own; every block is shaped; THE BLOCKS' ROUNDS IN A ROW ARE THE PLAN's
DECLARED ROUNDS, WHOLE (entry, stored parts, trees and their sources), chain by chain; every stored
part that is opened has the stored table's depth; `labelsOk`; `placesOk`; `beforeOk`; `treeSharingOk`;
`readsOk`; `sentFit`.
-/
def FileDescription.planOkCore (F : FileDescription Xi) : Bool :=
  F.fileOk && blocksOk F.first.blocksInOrder && blocksOk F.shared.blocksInOrder && blocksOk F.second.blocksInOrder &&
    F.roundsDeclaredByBlocks.1 == F.plans.1 && F.roundsDeclaredByBlocks.2.1 == F.plans.2.1 && F.roundsDeclaredByBlocks.2.2 == F.plans.2.2 &&
    (F.roundsDeclaredByBlocks.1 ++ F.roundsDeclaredByBlocks.2.1 ++ F.roundsDeclaredByBlocks.2.2).all (fun r => r.stored.all (·.sh.a == F.tableDepth)) &&
    F.labelsOk && F.placesOk && F.beforeOk && F.treeSharingOk && F.readsOk && F.sentFit

/-- **The tests on the plan**, of a file whose first chain ends in a seal: `planOkCore` and
`sealLast`. -/
def FileDescription.planOk (F : FileDescription Xi) : Bool := F.planOkCore && F.sealLast

/-- **BESIDE `planOk`, NOT IN IT.** The blocks' places and numbers of rounds, in the order of
the three flat lists, are the table's. It refuses a block without a round that is struck or added, a
round that is moved between neighbouring blocks, and two blocks that change places WITH THEIR
LABELS. `place` is a label that the block's maker or a driver stamps: WHICH block bears a label no
table says: two blocks with equally many rounds that are exchanged before the stamp, or one quiet
block in another's stead, pass. A block's name is its maker's word, made for refusals: it is not
held. -/
def FileDescription.wantedOk (F : FileDescription Xi) : Bool := F.places.map (·.2) == F.wanted

/-- A list of blocks: each one's place, whether one of its rounds draws, and what it names in
`before`. -/
def beforesOf (bs : List (Block S Cl)) : List (Place × Bool × List (Nat × Nat)) :=
  bs.map fun b => (b.place, b.rounds.any drawsAny, b.before)

/-- **BESIDE `planOk`, NOT IN IT.** For every row of `owed` a block stands at that place, ONE OF
ITS ROUNDS DRAWS (a quiet block at the place, with the drawing block elsewhere, is refused), and it
names in `before` every message of the row. What follows for the order is what `beforeOk` asks of a
message that is named, and no more: of the block's own chain: it is sent not behind the block's
first draw, and if it is sampled SOME round between has answers; of an earlier chain: it is sent.
That the block at the place is the one that draws the challenge which the row means rests on the
label: so `owedOk` is worth its name only beside `wantedOk`. -/
def FileDescription.owedOk (F : FileDescription Xi) : Bool :=
  let all := beforesOf F.first.blocksInOrder ++ beforesOf F.shared.blocksInOrder ++ beforesOf F.second.blocksInOrder
  F.owed.all fun r => all.any fun b => b.1 == r.1 && b.2.1 && r.2.all b.2.2.contains

/-! ## 5 The decision -/

/-- The prime of the programs' field, as a word. -/
def fieldPrimeWord : UInt64 := 0xFFFFFFFF00000001

/-- Every word of a field's element in the view is below the prime: in the rounds' items that hold
elements, in the elements drawn, and in the opened columns. -/
def viewWordsBelowPrime (v : Fmt.View) : Bool :=
  (v.rounds.all fun r =>
    (r.drawn.elems.all fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) &&
    r.vals.all fun g =>
    match g with
    | .f x => x < fieldPrimeWord
    | .e x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord
    | .answer x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord
    | .word _ => true
    | .root _ => true) &&
  v.opened.all fun o => o.2.2.all (· < fieldPrimeWord)

/-- **The fold over a chain's blocks.** Each block takes its own rounds off the front of the list,
and the columns that it reads off the front of the list. At the end: the record, the rounds left and
the columns left. A refusal bears the block's name and the name of the test that refused. -/
def foldBlocks (firstTree : Nat) : List (Block S Cl) → S → List Fmt.RoundView → List OpenedColumn →
    Except String (S × List Fmt.RoundView × List OpenedColumn)
  | [], s, rs, cols => .ok (s, rs, cols)
  | b :: l, s, rs, cols =>
    let (mine, rest) := rs.splitAt b.rounds.length
    if mine.length ≠ b.rounds.length then .error (b.name ++ ": the stretch is short") else
    match b.step firstTree s mine cols with
    | .error e => .error (b.name ++ ": " ++ e)
    | .ok (s', k) => foldBlocks firstTree l s' rest (cols.drop k)

/-- A view with an empty round behind its rounds. -/
def withEmptySealRound (v : Fmt.View) : Fmt.View :=
  { v with rounds := v.rounds ++ [⟨[], ⟨[], [], [], none⟩⟩] }

/-- A chain's fold, with nothing left over; its reason headed by the chain's name. -/
def chainAt (name : String) (firstTree : Nat) (bs : List (Block S Cl)) (s : S) (v : Fmt.View) :
    Except String S :=
  if bs.isEmpty then .error (name ++ ": it has no block") else
  match foldBlocks firstTree bs s v.rounds v.opened with
  | .ok (s', [], []) => .ok s'
  | .ok (_, rs, cols) =>
    .error (name ++ s!": left over: {rs.length} rounds, {cols.length} columns")
  | .error e => .error (name ++ ": refused at " ++ e)

/-- The words of the refusal on the plan: with the name of the first block that fails its own test,
or "the file's", and then the name of the first of `BookPlan`'s clauses that fails, if one does.
`none` where the tests on the plan pass. -/
def FileDescription.planWord (F : FileDescription Xi) : Option String :=
  if F.planOk then none else
    some ("the tests on the plan" ++
      match (firstBad F.first.blocksInOrder).or ((firstBad F.shared.blocksInOrder).or (firstBad F.second.blocksInOrder)) with
      | some n => ": " ++ n
      | none => ": the file's" ++
        match (BookPlan.clauses F.roundsDeclaredByBlocks F.roots).find? (!·.2) with
        | some c => ": the book's " ++ c.1
        | none => "")

/-- The decision's course, of its parts: what the tests on the plan and on the instance have said;
the first two chains' first states; the second chain's start; the three lists of blocks; the last
test; the three views. -/
def runCore {S₁ S₂ S₃ : Type} (planWord : Option String) (okStart : Bool) (s₁ : S₁) (s₂ : S₂)
    (start₃ : S₁ → S₂ → Except String S₃) (firstTree₃ : Nat) (b₁ : List (Block S₁ Cl))
    (b₂ : List (Block S₂ Cl)) (b₃ : List (Block S₃ Cl)) (fin : S₁ → S₂ → S₃ → Bool)
    (v₁ v₂ v₃ : Fmt.View) : Except String (S₁ × S₂ × S₃) := do
  if let some w := planWord then throw w
  need "the test on the instance" okStart
  need "a word of the first view is not below the prime" (viewWordsBelowPrime v₁)
  need "a word of the second view is not below the prime" (viewWordsBelowPrime v₂)
  need "a word of the third view is not below the prime" (viewWordsBelowPrime v₃)
  let e₁ ← chainAt "the first chain" 0 b₁ s₁ (withEmptySealRound v₁)
  let e₂ ← chainAt "the shared chain" 0 b₂ s₂ v₂
  let s₃ ← match start₃ e₁ e₂ with
    | .ok s => pure s
    | .error e => throw ("the second chain's start: " ++ e)
  let e₃ ← chainAt "the second chain" firstTree₃ b₃ s₃ v₃
  need "the ends fail the last test" (fin e₁ e₂ e₃)
  pure (e₁, e₂, e₃)

/-- **The decision, with the three chains' ends.** `.error` with the reason in words at the first of
these that says no: the tests on the plan, with the name of the first block that fails its own, or
"the file's"; the test on the instance; every word of the first, the second, the third view is below
the prime; the first chain's fold, at its view with the sealing round put back; the shared chain's;
the second chain's start; its fold; the last test. Each fold runs at its own chain's state, over
`Chain.blocksInOrder`, with nothing left over. -/
def FileDescription.runEnd (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) :
    Except String (F.S₁ × F.S₂ × F.S₃) :=
  runCore F.planWord (F.okStart x) (F.start₁ (F.pub x)) (F.start₂ (F.pub x)) (F.start₃ (F.pub x))
    F.lastChainFirstTreeNumber F.first.blocksInOrder F.shared.blocksInOrder F.second.blocksInOrder (F.fin x) v₁ v₂ v₃

/-- "yes", or "no: " and the reason. -/
def sayOf {α : Type} : Except String α → String
  | .ok _ => "yes"
  | .error e => "no: " ++ e

/-- **The decision**: true where `runEnd` gives the ends. -/
def FileDescription.run (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) : Bool :=
  (F.runEnd x v₁ v₂ v₃).isOk

/-- The same in words: "yes", or "no: " and the reason. -/
def FileDescription.say (F : FileDescription Xi) (x : Xi) (v₁ v₂ v₃ : Fmt.View) : String :=
  sayOf (F.runEnd x v₁ v₂ v₃)

/-- A description at the instances Xi, as one at the instances Xi', along a map from Xi' to Xi. So a
description can be typed at a plain record, and be laid where another type of instances is wanted.
-/
def FileDescription.pull {Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) : FileDescription Xi' where
  S₁ := F.S₁
  S₂ := F.S₂
  S₃ := F.S₃
  Cl := F.Cl
  plans := F.plans
  tableDepth := F.tableDepth
  wanted := F.wanted
  owed := F.owed
  fileOk := F.fileOk
  okStart := fun x => F.okStart (f x)
  XiPub := F.XiPub
  pub := fun x => F.pub (f x)
  start₁ := F.start₁
  start₂ := F.start₂
  start₃ := F.start₃
  first := F.first
  shared := F.shared
  second := F.second
  fin := fun x => F.fin (f x)

/-- Its declared rounds are the same. -/
theorem FileDescription.pull_decl {Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) :
    (F.pull f).roundsDeclaredByBlocks = F.roundsDeclaredByBlocks := rfl

/-- Its tests on the plan are the same. -/
theorem FileDescription.pull_planOk {Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) :
    (F.pull f).planOk = F.planOk := rfl

/-- Its decision at x is the description's at f x. -/
theorem FileDescription.pull_runEnd {Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) (x : Xi')
    (v₁ v₂ v₃ : Fmt.View) : (F.pull f).runEnd x v₁ v₂ v₃ = F.runEnd (f x) v₁ v₂ v₃ := rfl

theorem FileDescription.pull_run {Xi' : Type} (f : Xi' → Xi) (F : FileDescription Xi) (x : Xi')
    (v₁ v₂ v₃ : Fmt.View) : (F.pull f).run x v₁ v₂ v₃ = F.run (f x) v₁ v₂ v₃ := rfl

/-- FOR A HARNESS: a first view as the verifier program's reader gives it, without its last round.
`none` if there is no round, or if the last round holds an item or draws an element, a position or a
matrix entry. Its digest is not asked. -/
def offSeal (v : Fmt.View) : Option Fmt.View :=
  match v.rounds.getLast? with
  | some ⟨[], ⟨[], [], [], _⟩⟩ => some { v with rounds := v.rounds.dropLast }
  | _ => none

/-! ## 6 Limits

No block of the protocol is here, and nothing is proved but `FileDescription.pull`'s four equations. That
the tests behind the runs of claims can only refuse is Johnson/Desc/BlockLaws.lean's.

WHICH VIEWS. Those that the compiler's slot hands (OnBytes/Maker/Whole.lean): the first has no
sealing round; `runEnd` puts it back, once, as an empty round, so that the first chain's blocks
state the plan's entries whole. A first view as the verifier program's reader gives it holds that
round: a harness on that road takes it off first by `offSeal`, and says in its print which road it
ran.

WHAT IS READ. No read hangs on the carried record or on a symbol read before. ON THE THIRD CHAIN A
TREE THAT IS TAKEN OVER AND THE CHAIN's FIRST OWN TREE BOTH SHOW UNDER THE KEY 0 (the key is cut off
at 0, as in the verifier program and in `Three.Whole.key`, OnBytes/Three/Data.lean): there
`Block.step` tells them apart by their order, position and width alone. The width is idle under the
slot's own views, where a column has its width by type; it bites at a running reader's views. EVERY
TREE THAT THE THIRD CHAIN TAKES OVER SHOWS UNDER THE KEY 0: a key names no tree there. That a view
lists the opened columns in the order of the declared openings, tree by tree, is the reduction's
making (`wantsOf`), not a test of this file: the name to lean on is `WantsAre` (BlockSlot.lean).
`readsOk` holds, on the plan, what each round reads against what its entry
draws.

WHAT `Block.step` DOES NOT ASK: that nothing is owed from the round closed before, and that each
entry's count of batched rows is 0, asked inside or handed on.
SO NO KIND MAY DROP ITS OWN GUARD ON AN ENTRY's ROWS. That `decide` looks at every
item is its own matter; a round's name reaches `decide` only by the kind's own saying.

CLAIMS. No claim can be forgotten in silence, IF ITS KIND NAMES THE RUN (the fields `claims` and
`after` have no default, so a kind writes [] with its own hand; but a kind
that writes [] and lays its equations nowhere passes every test here: no number of the plan is held
against what `claimsIn` gathers), AND IF THE BATCHING's BLOCK RUNS THE FUNCTION THAT IT IS
HANDED: nothing here asks that: the batching kind's writer shows by a control that a claim struck
from `hear` turns its verdict. (A file's description holds chains, and `runEnd` makes the flat lists
itself: none is typed by hand.) The runs behind the batching are run by the frame. `each` is reached
only through that same function: a batching that does not call it goes round `each` too. `each` and
`tests` have no default, so a link's maker writes the empty ones with its own hand: the type shuts
forgetting, not emptiness.

THE ORDER. `orderOk` and `orderAfterOk` hold a link's two orders against what its blocks STATE:
every stated run stands in the order just once, and the order names no other. So an order that is
laid whole is refused as soon as one run that it lists is stated by no block. NOTHING HERE HOLDS AN
ORDER AGAINST THE PROTOCOL's: a maker of links that first cuts the protocol's order down to the runs
that the blocks state silences both tests, at a run, a stretch or the whole. That the order is laid
uncut is the matter of the file that makes the links.

FIXED BEFORE THE DRAW. `before` is a block's own word on which oracle messages its test leans;
`beforeOk` asks, on the plan alone, that they are sent in time. Which round answers which message's
sample no datum says: what is asked of a sampled message is that SOME round behind its sending, and
in front of the draw, has sample answers in its message. NOT ASKED: values that are sent in the
clear. THAT THE BLOCK WHICH DRAWS NAMES ALL THAT ANY TEST HOLDS AGAINST ITS CHALLENGE is asked by
`owedOk` alone, for the rows of `owed` alone, and `owedOk` stands beside `planOk`: `run` does not
ask it. A message of
an earlier chain counts as in front of every draw of a later chain: so the rounds stand in the
reduction; that a later chain's draws hang on the earlier chains' messages in the compiled protocol
is the compiler's matter (their seals), not asked here: SO A ROW OF `owed`, OR A WORD OF `before`,
THAT NAMES AN EARLIER CHAIN's MESSAGE SAYS OF THE ORDER NOTHING THAT A PLAN COULD FAIL: whoever
leans on it names as a premise that the later chain's draws hang on that message. Behind `andThen`
both blocks' lists are held at the FIRST block's first draw: more than either asks.

TENANTS. `Oracle` and `SymbolComponent` stand in Johnson/Desc/Oracle.lean. `BookPlan`'s clauses sum and rows
ask once more, and more, than `Block.shaped` asks of the tenants' words and degrees. That the
tenants told are those that the blocks lay, and that a block cuts a column by these words, is asked
nowhere.

HOSTS AND GUESTS. That a guest speaks only of values that are sent or fixed before the first of the
host's rounds that draws a coordinate which the guest borrows BEARS SOUNDNESS AND STANDS IN `KindWithGuestIdentities`'s
DOCSTRING ALONE: G is a letter; nothing tests it; nothing tests that a host is handed every guest.
That `clear` clears what `lay` laid is the link's own matter.

THE FOLD. `foldBlocks` says once more, over blocks and with a refusal's name, what `stepAll`
(Johnson/Desc/Step.lean) says over a table of steps. The two are tied by no statement. `stepAll`
serves the tables of steps that are run.

BESIDE `planOk`: `wantedOk` and `owedOk` are asked by no decision here: `planOkCore` has neither.
Whoever counts on one asks it by name.

FOUR FREE FIELDS BEAR THE VERDICT: `plans`, `fileOk`, `okStart`, `fin`. No test here can hold them:
`fin := fun _ _ _ _ => true` is a lawful description. `fin` is the only place where a record's own
end tests can be asked (each chain stands at its end; nothing waits; what was heard is what is
asked); `okStart` the only home of the tests on the instance alone. Whoever ties a description to a
statement names what these four must hold as premises.

CHAINS ARE NUMBERED IN TWO WAYS: `Place.chain` and `before` count them 1, 2, 3; `TreeSource.taken`,
`openedOwn`, `labelsOk` and `BookPlan` count them from 0. In `before` the chain 0 is refused; a
file that writes there the number which it writes in `.taken` names another chain's message, and
the test may well say yes.

THE PLAN. `plans` is a field: that it is the plan of the public files is asked where such an F is
made. IT HOLDS THE DECLARED ROUNDS WHOLE, not their entries alone: so which
trees a round must open is held against the rule that makes the declared rounds of the public files;
that this rule is the protocol's rests on reading (its own Limits). It holds the plans' ROUNDS: an
entry under the name RECORD is no round (`Fmt.Plan.rounds`) and stands in no view. A block's `place`
is its maker's word: what is tested of it is that its chain is the one in whose list it stands and
that no two blocks stand at one place; `andThen` keeps the first block's place alone. A BLOCK
WITHOUT A ROUND THAT IS LEFT OUT: a chain's first and last block and a link's
tests behind the adding are fields without a default, so these cannot be forgotten; every other such
block is missed by no test of `planOk`; `wantedOk`, beside it, refuses the description then, if the
table is made off the plan; a quiet half that is joined to a block by `andThen` no table sees.
`fieldPrimeWord` is a literal: the plan's field is not asked. So is the 1 in `lastChainFirstTreeNumber`: that just one
tree's number lies between the first chain's trees and the third's own is not asked.

BESIDE THIS FILE (Johnson/Desc/BlockSlot.lean): that `groupsOf` is `wantsOf` at the data made of
`roundsDeclaredByBlocks`; what the slot tests in front of `run` (the proofs of work; no draw shortened; a stored
symbol carries its position; the rounds without a challenge); that `viewWordsBelowPrime` is `okView`
(OnBytes/Maker/OkView.lean) and, beside it, the drawn elements' words.

A REFUSAL's WORDS name the chain, the block, and the test inside it that refused: "the rounds" and
"the columns" are `Block.step`'s own two; every other name is the kind's. A text that is typed with
`Option` is laid under one name by `named`: its refusals then all bear that one name.
-/

end VerifiableInference.Desc
