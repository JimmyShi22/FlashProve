-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/Frame.lean: the types in which an honest prover is written for a
protocol description in the format of Johnson/Desc/Block.lean (`FileDescription`), and the functions that
run it. The honest prover is the party that follows the protocol: from its input, its coins and the
verifier's challenges it computes each round's message. A request is one run of the protocol on
one instance. This file has definitions, and three equations on lists of rounds (`Seen.plus_nil`,
`Seen.plus_plus`, `Seen.front_plus`). The definitions: the types; `run`, which plays a prover at
given challenges and builds the three views that a verifier sees; and an executable test, `say`,
which applies the description's own decision to these views. The prover's side of no sub-protocol is
defined here. No other theorem is stated: none says that an honest run is accepted. Some parameters
are left open (see "What is left open").

The frame is a set of Lean types for the request's honest prover: it is cut into parts, each paired
with a candidate simulator. `Good` lists conditions on the pairs of one sub-protocol. Frame.lean,
Side.lean and Sum.lean hold definitions only, but for these three equations. No theorem there says
that a part of this protocol meets `Good`, or that parts which meet it can be joined. So the frame
proves no hiding, zero knowledge or index privacy.

Block.lean describes each sub-protocol from the verifier's side, and says of the honest prover
that it is "absent here" (Johnson/Desc/Block.lean, the head). This file gives
the types for it. `Good` is defined in Honest/Side.lean.

Terms of Block.lean. A description has three chains of sub-protocols (`Block`): the first, the
shared and the second. The shared chain's rounds are sent once for all requests of a batch, and its
prover's sides are given no instance, only the key (`Prover.key x`); the first and the second chain
are a request's own, played before and after it. (The rounds that are shared in the library's sense
are those of the chain that `FileDescription` calls `shared`: OnBytes/Maker/Whole.lean, `annOf`.) The first
chain's last round is the sealing round, of which a view shows nothing. Each sub-protocol has a
place (`Place`) and a kind (`Kind`: a function from a place's public parameters to the sub-protocol
there). A view is what a verifier sees of a chain: each round's items in the clear, its challenge,
and the columns that are opened. In the error strings, which are code: half = a prover's side; row =
its list of parts; run (of coins) = block; stands, handed, in front of, behind = is, given, before,
after.

The idea. A `Block` declares what a sub-protocol's rounds send, as shapes (`rounds`, `oracles`), and
what the verifier decides. A `Placed` is its counterpart at the same place and computes the
messages. It is a list of parts: each `Part` has one `Move` for each of its rounds, and the parts'
rounds, in the list's order, are the sub-protocol's rounds. The functions here go over the
description's own flat lists of sub-protocols (`Chain.blocksInOrder`), so the prover is a prover for that
very description. An error is returned for a list with another number of rounds than the
sub-protocol at its place, a part with another number of coins than the book of coins has for it
(see "Parts and coins"), or a message of another shape than the sub-protocol declares.

  1  `Said`, `Table`, `Sending`   an item in the clear; an oracle message in full; a round's message
  2  `Due`, `Cs`, `CsAll`, `Cs.split`, `CsAll.split`   a number of coins; coins; coins for a list of
     named counts; coins at a sum of counts, split in two
  3  `Addr`, `Purse`, `Ahead`, `ProverCoinCounts`, `Coins`, `Coins.look`, `orderOf`, `Addr.before`,
     `ProverCoinCounts.spentBy`, `ProverCoinCounts.knownBy`, `cutAll`, `ProverCoinCounts.clauses`   a part's address; coins for a table
     of addresses; the public book of coins; a run's coins; the order of parts; the entries between
     two parts; the tests on the book
  4  `Seen` (with `Seen.bare`, `Seen.front`, `Seen.plus`), `State`, `Move`, `Part`, `Placed`,
     `KindHalf`   the prover's side of a round, of a
     stretch of rounds, of a sub-protocol at its place, of a kind; `Odds`: a stated share;
     `Part.lift`, `Part.andThen`: parts built from parts; `RowCoins`; `Shown`, `Before`, `Sim`,
     `KindSim`: the type of a part's simulator, and of what it is given; `Common`, `Local`, `Face`,
     `Prover`, `Prover.storedWords`: the prover of a file
  5  `Why`, `Refusal`, `Step`, `Step.stop`, `lend`, `lendPart`, `lendRow`, `Part.steps`,
     `Placed.steps`, `chainSteps`, `Played`, `Mid` (with `Mid.bare`, `Mid.shown`, `Mid.took`),
     `Told`, `Step.tell`, `Step.hear`, `play`,
     `midIn`   a chain's rounds in the description's order, each with its move if a prover's side is
     defined there; a round's message, and what follows its challenge; a run at given challenges
  6  `Read`, `readsOf`, `fillCols`, `treeOwn`, `treeThird`, `Draws`, `Draws.due`, `Run`,
     `Run.storedRead`, `Ready`, `readyTests`, `sharedSteps`, `readyShared`, `ready`, `sealTest`,
     `Ready.ends`, `run`   what such a run shows a verifier: the three views; `midAt`,
     `midSharedAt`, `carriedAt`: the state of a run before a part, and what the part carries
  7  `say`, `outcome`, `stopOf`, `hidAt`, `Runs`, `sameView`, `sameOutcome`   the test: the
     description's own decision on these views; a run's outcome as a statement may read it
  8  `HLot`, `lotsLacking`, `lacking`, `pureKey`, `pureSay`   the same at `onlineDescription`, the proof
     file's description

Field elements. A coin, an item that holds an element, a table's symbol and a stored table's column
are typed in the library's two fields (`Cb.Gl.F`, `Cb.Gl.E`: Cb/Gl/GlField.lean). They are converted
to 64-bit words by the library's `ofF` and `ofE` alone (OnBytes/Slice/Field.lean), whose words are
below the prime. The stored tables are the committed tables.

Parts and coins. A part is the unit that gets coins and has stops. It is named by its place and its
number in the list there (`Addr`). Coins are the prover's random field elements. A run's coins are
typed by the book (`ProverCoinCounts`), the public table of how many coins each part has. A part states its own
count and is typed at it, and that count is compared with the book's. A part is given its own coins,
and the blocks of other parts' coins that the book's entries (`Ahead`) name for it, and no others.
Being in the same list gives a part nothing: a block of another part of its own list reaches it only
through an entry, like any other block. A part states each such block by name and count, and both
are compared with the entry, so two blocks of one count cannot change places unseen. The book also
fixes the cut of a place's rounds into parts, and a list that is cut differently is rejected. What
parts pass on (`own`) is computed without a run's coins, by type: `Move.hand` is given the state
alone, and no move can change the state's other two fields (`input`, `heard`). What has been sent
reaches a later round as `Seen`, which `Move.say` alone is given.

The prover's input: all that a prover's side is given. It has five components; a capital letter is a
type, the small letter a value of it. W₀, the index (what all requests share). Rc, the stored
tables' pads and encoding randomness. x : Xi, the explicit input (at the proof file: the instance
with the out-of-domain sample of ivk, the index verification key; here: the public instance). The
key, which `Prover.key` computes from x: the part of ivk that the shared chain reads (out-of-domain
seeds and answers); it is not ivk. The witness: the request's trace, which `Prover.trace` computes
from (w₀, x). A run is a session (one request). The stored tables' columns are computed from (w₀,
rc) by `Prover.stored`. A prover's side in the shared chain is given (w₀, rc, key) alone. `Face`
fixes which field of the prover's input counts as public: the field `x` in the first and second
chain, the field `key` in the shared chain. The types of these two fields are parameters; only `run`
sets them to the description's own instance and the key made of it. A simulator (`Sim`) is given
five things: that public field, a `Before`, its part's challenges, the positions read of its part's
tables, and coins of its own. A `Before` holds the earlier rounds' messages and challenges, and
opened columns of earlier tables and of the stored tables. The type of a simulator has no further
argument, and it does not say that what is supplied for these five is public.

The key. The verifier's shared chain starts from the instance's public part (`FileDescription.start₂`). So
the prover's sides in the shared chain are given `Prover.key x`: a type parameter Ky for what the
shared chain may read of the public instance, and a function, which `ready` applies. It is meant for
the stored table's out-of-domain seeds and answers. It is neither in Rc nor among a run's coins. At
`onlineDescription` the shared chain's first state is a function of the table's key alone, by a theorem of
the library (`ToldDesc.readsKeyAlone_descPure`, Johnson/ToldDescR/Reads.lean), and `pureSay`
supplies that key itself. No type compares `key` with what `start₂` reads: with Ky := Xi the
whole instance would reach the shared chain.
Where the library's batch prover has the key. The strategy for the shared rounds (`BatchHonestProver.strat0`,
Iop/Batch.lean) is a function of the private input Wt and the shared coins: it sees no instance.
Where tables have such samples, Wt is index × the stored tables' pads and encoding randomness × seed
(`HolographicProtocol.honestOnlineBatchProver`, Hiop/RecInterface.lean; `Files.Provers.hB`, OnBytes/Flat/Object.lean), the answers are a
function of these three (`HolographicProtocol.honestOutOfDomainAnswer`, `HolographicProtocol.recOf`), and a relation on the inputs asks that
the instance holds just that seed and these answers (`HolographicProtocol.validB`, its first clause). So in the
library the key's place is Wt's third component, not the instance. Here the key is read from
the instance. The two agree at the inputs of that relation. A strategy of the library's type that is
built from a `Prover` has to compute the key from (w₀, rc, seed): that function is not defined here.

Stops. A stop is an abort condition: a test, on challenges and for the second stop on the input too,
at which the honest prover does not go on. A part has two (`Part.bad`, `Part.hid`). They follow the
three fields that the library's structure `Iop.BatchHonestProver` (Iop/Batch.lean) has for the challenges at
which the honest prover does not go on: `stop0`, a test on the shared challenges; `Bad`, a set of
lists of the other challenges; `Hid`, such a set for each input of the prover's and each instance.
They are separate from its moves. The first stop reads challenges alone. In the first and the second
chain the second stop may also read the prover's whole input (`Face.sees`): the index, the stored
tables' pads and encoding randomness, the public instance and the witness. In the shared chain the
second stop is not asked. Neither stop has the run's coins among its arguments. So whether a part is
stopped there can depend on private input; `exact` and `fresh` are not asked there, and no field of
`Good` measures these challenges. A stop fires where its test returns `some`; it stops the part
where it is the one that `Step.stop` reports, which asks the first stop first. A part's stops read
all of its own challenges, and none that is drawn later. A stop is no output of its own: `outcome`
is `none` at a stop as at any other error.

A stored run to fall back on. `run` takes `back`, the three views of a stored run, or none. Where no
prover's side is defined, a round's items in the clear are the stored run's at that round, and a
column of a table that no prover's side sent is the stored run's column at the same index. Each run
says which rounds a prover's side made (`Played.told`) and whose table a column was read from
(`Read.sender`). The book's coins are
there for every row, so a part can be given a block of coins whose owner is not written. With
`back := none` nothing is sent where no prover's side is defined. The challenges have to be the
stored run's own.

What is left open. The seven type parameters of `Prover`. Who makes the book: a description declares
mask words (`SymbolComponent.mask`) and no code's parameters (Johnson/Desc/Oracle.lean has none), so the book
cannot be computed from a `FileDescription` alone. It is an argument; functions that compute it:
BookOf.lean to BookWhole.lean. The challenges are arguments: nothing is drawn and nothing is hashed
in this file.

On `Rc`. A statement that takes a distribution over `Rc` has to state the following, which this file
does not state: Each table that a statement names has its own value of the encoder's randomness and
its own salts. Whoever makes the table draws them uniformly, once for that table, apart from every
other table's, from the coins of the proofs that are made with it, and from every run's coins. The
table's stored columns and its OOD sample are made at that value alone, and each table has one seed.
How many runs read one table is the scheme's to say, within that table's budget.

How the test can fail. `say` answers "yes" only if the tests on the book pass, the description
passes its own test on the places (`FileDescription.placesOk`), w₀ and the named element are in range
(`Prover.inRange`, `Prover.dummy`), every prover's side is alone at a place of its chain, every part
takes the book's count and does not stop, the request has a trace, the numbers of rounds and of
challenges fit, every message has the declared shape, the sealing round sends and draws nothing,
every column that is read is available and has the declared width, and `FileDescription.run` accepts. With
a stored run to fall back on, the challenges have to be its own, and a yes shows nothing about the
rounds and columns that were taken from it: with no prover's side at all it is the stored run's own
verdict.

Limits.
  * One request at a time: a batch of several requests is not modelled.
    With a batch in view, the book's tests reject a block that is owned in the shared chain and
    spent outside it; such a block may be carried there.
  * One kind of description: a `FileDescription`, which describes the proof file. The copy's file, a file
    of the offline phase, is described by a `OneChainFileDescription`, which has no counterpart in this file. The
    honest provers of the three parts of the protocol stand as one term in
    E2E/TheHonestProver.lean (`honestProvers`).
  * A part that is typed at a count need not read every coin of it: no type shows that.
  * A part without a round is never asked its stops.
  * A fault (an error of `Move.say`, a message of another shape) may depend on the coins; a stop
    cannot.
  * The two shares that a part states of its stops are numbers that the part declares: nothing
    compares them with the stops.
  * `Seen` holds the rounds and, where the player hands them, the columns that the sub-protocols
    before the round have read (`Seen.opened`). `runC` (Walk.lean) hands them; `run`, `midAt` and
    `midSharedAt` hand none. So at a prover with a part that reads the field and errs at `none` (its
    duty: the next limit), `run` returns an error wherever that part's round is reached: `say` and
    `pureSay` do not answer yes, `outcome` is `none`, `Runs` is false, and `midAt` and `midSharedAt`
    err behind that round, each in the chains that it plays. A statement over `run`, `outcome` or
    `midAt` behind that round says nothing of such a prover.
  * That a part which reads `Seen.opened` errs at `none` is a duty of whoever writes it: no type and
    no test of this file asks it.
  * A part that is placed by `Part.lift` is still given all that was heard and shown before it.
  * The views are built as `Block.step` reads them (`groupsOf`). That they are the views which the
    compiler passes on (Johnson/Desc/BlockSlot.lean), and that a `Prover` gives a strategy of the
    library's type, is not stated here.
  * The three rounds that are in no view (OnBytes/Maker/Whole.lean: the front round, the joining
    round, the seam) are not in this file. Roots, nonces, salts and proofs of work are the
    compiler's and are not in this file: a challenge here is a `Fmt.Drawn`, which has no field for a
    proof of work.
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.OnlineDescription

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest
open VerifiableInference.Desc (Block Chain FileDescription Place Oracle OpenedColumn itemOf fieldPrimeWord drawsMarkedNonzeroHaveNonzeroWords)

/-! ## 1 What is sent -/

/-- An item of a message that is sent in the clear, typed as what it is: an element of the base
field or of the extension field, a word, or a sample's answer. There is no root among them: a view
shows none. -/
inductive Said where
  | f (x : Cb.Gl.F)
  | e (x : Cb.Gl.E)
  | word (x : UInt64)
  | answer (x : Cb.Gl.E)

/-- The item as a view shows it: an element as the words below the prime that represent it
(OnBytes/Slice/Field.lean: `ofF`, `ofE`). A `.word` passes unchanged; nothing here asks that it is
below the prime. -/
def Said.got : Said → Fmt.ItemValue
  | .f x => .f (OnBytes.Slice.ofF x)
  | .e x => .e (OnBytes.Slice.ofE x)
  | .word x => .word x
  | .answer x => .answer (OnBytes.Slice.ofE x)

/-- An oracle message in full: 2 ^ logLength symbols of `words` elements of the base field each. A
symbol has its width by type. `logLength` is the sender's own label: `Sending.fits` compares both
numbers with what the sub-protocol declares, and nothing here compares `sym` with `logLength`. -/
structure Table where
  logLength : Nat
  words : Nat
  /-- the symbol at a position -/
  sym : Nat → Fin words → Cb.Gl.F

/-- The column at a position, as a view shows it. -/
def Table.col (t : Table) (x : Nat) : List UInt64 :=
  List.ofFn fun i => OnBytes.Slice.ofF (t.sym x i)

/-- What the prover sends in one round. -/
structure Sending where
  /-- the items in the clear, in the order of the round's entry -/
  vals : List Said
  /-- for each root of the round, in order: the oracle message under it -/
  tables : List Table

/-- The message has the shape that the sub-protocol declares for this round: the items of the
round's entry, except the roots, and a table of the declared length and width for each oracle
message. -/
def Sending.fits (s : Sending) (d : Fmt.DeclaredRound) (os : List Oracle) : Bool :=
  s.vals.map (fun v => itemOf v.got) == d.items.filter (· != .root) &&
    s.tables.map (fun t => (t.logLength, t.words)) == os.map fun o => (o.logLength, o.words)

/-! ## 2 Coins -/

/-- A number of coins, for each of the two fields. -/
structure Due where
  /-- elements of the base field -/
  f : Nat
  /-- elements of the extension field -/
  e : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **Coins**: so many elements of each field. By type there is no coin beyond the count. -/
structure Cs (d : Due) where
  f : Fin d.f → Cb.Gl.F
  e : Fin d.e → Cb.Gl.E

/-- No coin. -/
def Cs.empty : Cs ⟨0, 0⟩ := ⟨fun i => i.elim0, fun i => i.elim0⟩

/-- Coin number `i` of the base field. An error beyond the count: no default value is returned. -/
def Cs.fAt {d : Due} (c : Cs d) (i : Nat) : Except String Cb.Gl.F :=
  if h : i < d.f then .ok (c.f ⟨i, h⟩) else .error "a coin is asked beyond the count"

/-- The same for the extension field. -/
def Cs.eAt {d : Due} (c : Cs d) (i : Nat) : Except String Cb.Gl.E :=
  if h : i < d.e then .ok (c.e ⟨i, h⟩) else .error "a coin is asked beyond the count"

/-- The `n` coins from number `a` on, in each field; `none` if they are not all there. -/
def Cs.cut {d : Due} (c : Cs d) (a n : Due) : Option (Cs n) :=
  if h : a.f + n.f ≤ d.f ∧ a.e + n.e ≤ d.e then
    some ⟨fun i => c.f ⟨a.f + i.1, by have := h.1; have := i.2; omega⟩,
      fun i => c.e ⟨a.e + i.1, by have := h.2; have := i.2; omega⟩⟩
  else Option.none

/-- Coins for each element of a list of named counts: a block's name, and how many coins it has. -/
def CsAll : List (String × Due) → Type
  | [] => Unit
  | d :: ds => Cs d.2 × CsAll ds

/-- The sum of two counts, field by field. -/
abbrev Due.plus (a b : Due) : Due := ⟨a.f + b.f, a.e + b.e⟩

/-- Coins at a sum of two counts, split in two: in each field the first count's coins come first. -/
def Cs.split {a b : Due} (c : Cs (a.plus b)) : Cs a × Cs b :=
  (⟨fun i => c.f ⟨i.1, by have := i.2; show i.1 < a.f + b.f; omega⟩,
      fun i => c.e ⟨i.1, by have := i.2; show i.1 < a.e + b.e; omega⟩⟩,
    ⟨fun i => c.f ⟨a.f + i.1, by have := i.2; show a.f + i.1 < a.f + b.f; omega⟩,
      fun i => c.e ⟨a.e + i.1, by have := i.2; show a.e + i.1 < a.e + b.e; omega⟩⟩)

/-- Coins for two concatenated lists of named counts, split in two. -/
def CsAll.split : (l₁ l₂ : List (String × Due)) → CsAll (l₁ ++ l₂) → CsAll l₁ × CsAll l₂
  | [], _, c => ((), c)
  | d :: l₁, l₂, c =>
    let c' : Cs d.2 × CsAll (l₁ ++ l₂) := c
    let r := CsAll.split l₁ l₂ c'.2
    ((c'.1, r.1), r.2)

/-! These types are finite and not empty: the instances that a distribution on them needs. -/

noncomputable instance (d : Due) : Inhabited (Cs d) := ⟨⟨fun _ => 0, fun _ => 0⟩⟩

noncomputable instance (d : Due) : Fintype (Cs d) :=
  Fintype.ofEquiv ((Fin d.f → Cb.Gl.F) × (Fin d.e → Cb.Gl.E))
    { toFun := fun x => ⟨x.1, x.2⟩, invFun := fun c => (c.f, c.e)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

noncomputable def CsAll.any : (ds : List (String × Due)) → CsAll ds
  | [] => ()
  | d :: ds => ((default : Cs d.2), CsAll.any ds)

@[reducible] noncomputable def CsAll.fin : (ds : List (String × Due)) → Fintype (CsAll ds)
  | [] => inferInstanceAs (Fintype Unit)
  | d :: ds => letI := CsAll.fin ds; inferInstanceAs (Fintype (Cs d.2 × CsAll ds))

noncomputable instance (ds : List (String × Due)) : Inhabited (CsAll ds) := ⟨CsAll.any ds⟩
noncomputable instance (ds : List (String × Due)) : Fintype (CsAll ds) := CsAll.fin ds

/-! ## 3 The book of coins -/

/-- **A part's address**: a place, and the part's number, from 0, in the list of parts at that place
(`Placed.parts`). -/
structure Addr where
  place : Place
  part : Nat
  deriving DecidableEq, Repr, Inhabited

/-- Coins for each row of a table of addresses and counts. -/
def Purse : List (Addr × Due) → Type
  | [] => Unit
  | r :: l => Cs r.2 × Purse l

/-- The coins in the first row at an address. `none`: the address has no row. -/
def Purse.find? : (l : List (Addr × Due)) → Purse l → Addr → Option ((d : Due) × Cs d)
  | [], _, _ => Option.none
  | r :: l, c, a => if r.1 == a then some ⟨r.2, c.1⟩ else Purse.find? l c.2 a

noncomputable def Purse.any : (l : List (Addr × Due)) → Purse l
  | [] => ()
  | r :: l => ((default : Cs r.2), Purse.any l)

@[reducible] noncomputable def Purse.fin : (l : List (Addr × Due)) → Fintype (Purse l)
  | [] => inferInstanceAs (Fintype Unit)
  | r :: l => letI := Purse.fin l; inferInstanceAs (Fintype (Cs r.2 × Purse l))

noncomputable instance (l : List (Addr × Due)) : Inhabited (Purse l) := ⟨Purse.any l⟩
noncomputable instance (l : List (Addr × Due)) : Fintype (Purse l) := Purse.fin l

/-- **An entry of the book: coins that are sent ahead**, or borrowed coins. A block of its owner's
coins that one other part is given too. Owner and spender may be two parts of one place. -/
structure Ahead where
  /-- the block's name: the part that is given the block states it with the count, and `lend`
  compares both with the entry -/
  name : String
  /-- the part whose coins they are -/
  owner : Addr
  /-- the block's first coin among the owner's, in each field, from 0 -/
  start : Due
  /-- the block's length, in each field -/
  count : Due
  /-- the one part that is given the block -/
  spender : Addr
  /-- true: borrowed coins that the book marks as spent. false: borrowed coins that the book marks
  as carried. A part is given both alike. `ProverCoinCounts.clauses` separates them by three tests: a coin is in
  no two entries that spend it; a coin that a part spends is given to no earlier part, nor to that
  part as carried; a coin of the shared chain is spent by no part outside it. After the spender any
  part may carry the block. What the two are meant for: a block that is added as a mask to a value
  which is sent; and a block on which the part computes -/
  once : Bool

/-- An entry's name and count, as the part that is given the block states them. -/
abbrev Ahead.named (e : Ahead) : String × Due := (e.name, e.count)

/-- **The book of coins**: public data that goes with a description. For each chain, the parts that
have coins of their own, each with its count; the entries; and the cut: for each place at which a
prover's side may be defined, how many rounds each part of its list has. A part without a row has no
coin. The book is a check only if it is computed from the public files independently of the
definitions of the prover's sides (as `FileDescription.wanted`, Johnson/Desc/Block.lean): otherwise a
part's count is compared with itself. -/
structure ProverCoinCounts where
  first : List (Addr × Due)
  shared : List (Addr × Due)
  second : List (Addr × Due)
  ahead : List Ahead
  /-- a place, and each of its parts' numbers of rounds: `chainSteps` rejects a prover's side at a
  place without a cut, and a list that is cut differently -/
  cuts : List (Place × List Nat)

/-- **The coins of one run**, typed by the book: those of the shared chain's parts apart from the
others. -/
structure Coins (B : ProverCoinCounts) where
  first : Purse B.first
  shared : Purse B.shared
  second : Purse B.second

noncomputable instance (B : ProverCoinCounts) : Inhabited (Coins B) := ⟨⟨default, default, default⟩⟩

noncomputable instance (B : ProverCoinCounts) : Fintype (Coins B) :=
  Fintype.ofEquiv (Purse B.first × Purse B.shared × Purse B.second)
    { toFun := fun x => ⟨x.1, x.2.1, x.2.2⟩, invFun := fun c => (c.first, c.shared, c.second)
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }

/-- A part's count in a table; 0 if it has no row. -/
def dueAt (l : List (Addr × Due)) (a : Addr) : Due := (l.lookup a).getD ⟨0, 0⟩

/-- The counts of all rows at a place, added up. -/
def placeDue (l : List (Addr × Due)) (a : Place) : Due :=
  (l.filter fun r => r.1.place == a).foldl (fun n r => Due.plus n r.2) (⟨0, 0⟩ : Due)

variable {S Cl Xi V W X W₀ Rc Ky Tr X₀ G P C C' V' W' Y : Type}

/-- The book's table for chain number `ch`, from 0. Every `ch` from 2 on counts as the second chain.
-/
def ProverCoinCounts.rowsOf (B : ProverCoinCounts) (ch : Nat) : List (Addr × Due) :=
  if ch == 0 then B.first else if ch == 1 then B.shared else B.second

/-- The coins that the shared chain may be given, by address: those of its own parts alone. No coin
if the address has no row there. -/
def sharedLook (B : ProverCoinCounts) (c₀ : Purse B.shared) (a : Addr) : (d : Due) × Cs d :=
  (Purse.find? B.shared c₀ a).getD ⟨⟨0, 0⟩, Cs.empty⟩

/-- **The coins that chain number `ch`, from 0, may be given**, by address: the first chain those of
its own parts; the shared chain those of its own parts; the second chain those of all three. No coin
if the address has no row there. Every `ch` from 2 on counts as the second chain. -/
def Coins.look {B : ProverCoinCounts} (c : Coins B) (ch : Nat) (a : Addr) : (d : Due) × Cs d :=
  let no : (d : Due) × Cs d := ⟨⟨0, 0⟩, Cs.empty⟩
  if ch == 0 then (Purse.find? B.first c.first a).getD no
  else if ch == 1 then sharedLook B c.shared a
  else (((Purse.find? B.first c.first a).or (Purse.find? B.shared c.shared a)).or
    (Purse.find? B.second c.second a)).getD no

/-- The order of a description's places: the three chains' flat lists, in the order of play. -/
def orderOf (F : FileDescription Xi) : List Place :=
  F.first.blocksInOrder.map (·.place) ++ F.shared.blocksInOrder.map (·.place) ++ F.second.blocksInOrder.map (·.place)

/-- The part at `a` comes before the part at `b`, in an order of places: at an earlier place, or at
the same place with a smaller number. A place that is not in the list counts as the last. -/
def Addr.before (ord : List Place) (a b : Addr) : Bool :=
  decide (ord.findIdx (· == a.place) < ord.findIdx (· == b.place)) ||
    (a.place == b.place && decide (a.part < b.part))

/-- The entries by which the part at `p` spends coins of the part at `o`, in the book's order. -/
def ProverCoinCounts.spentBy (B : ProverCoinCounts) (o p : Addr) : List Ahead :=
  B.ahead.filter fun e => e.owner == o && e.spender == p && e.once

/-- The other entries that give coins of the part at `o` to the part at `p`, or to a part before
`p`. -/
def ProverCoinCounts.knownBy (B : ProverCoinCounts) (ord : List Place) (o p : Addr) : List Ahead :=
  B.ahead.filter fun e => e.owner == o && !(e.spender == p && e.once) &&
    (e.spender == p || e.spender.before ord p)

/-- The blocks that entries cut out of one part's own coins, entry by entry; `none` if a block is
not within the count. -/
def cutAll {d : Due} (c : Cs d) : (es : List Ahead) → Option (CsAll (es.map Ahead.named))
  | [] => some ()
  | e :: es => (c.cut e.start e.count).bind fun x => (cutAll c es).map fun y => (x, y)

/-- The mask words in the symbols of the oracle messages that a sub-protocol declares
(`SymbolComponent.mask`, Johnson/Desc/Oracle.lean). -/
def maskWords (b : Block S Cl) : Nat :=
  ((b.oracles.flatMap id).flatMap (·.tenants)).foldl (fun n t => n + t.mask) 0

/-- At every sub-protocol's place the parts have together at least as many coins, counted in
elements of the base field (an element of the extension field counts as three), as the sub-protocol
declares mask words. -/
def masksOk (bs : List (Block S Cl)) (l : List (Addr × Due)) : Bool :=
  bs.all fun b => decide (maskWords b ≤ (placeDue l b.place).f + 3 * (placeDue l b.place).e)

/-- Two intervals, each given by a start and a length, have a number in common. -/
def meets (a n b m : Nat) : Bool := n != 0 && m != 0 && decide (a < b + m) && decide (b < a + n)

/-- Two entries have a coin in common. -/
def Ahead.shares (p q : Ahead) : Bool :=
  p.owner == q.owner && (meets p.start.f p.count.f q.start.f q.count.f ||
    meets p.start.e p.count.e q.start.e q.count.e)

/-- **The tests on the book**, each under a name that says what is wrong if it fails. The Bool is
true where the test passes. -/
def ProverCoinCounts.clauses (F : FileDescription Xi) (B : ProverCoinCounts) : List (String × Bool) :=
  let p₁ := F.first.blocksInOrder.map (·.place)
  let p₂ := F.shared.blocksInOrder.map (·.place)
  let p₃ := F.second.blocksInOrder.map (·.place)
  let all := orderOf F
  let rows := B.first ++ B.shared ++ B.second
  let spent := (B.ahead.filter (·.once)).zipIdx
  let es := B.ahead.zipIdx
  let sizes := F.first.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
    F.shared.blocksInOrder.map (fun b => (b.place, b.rounds.length)) ++
    F.second.blocksInOrder.map fun b => (b.place, b.rounds.length)
  [("a row stands at no place of its chain",
      B.first.all (fun r => p₁.contains r.1.place) &&
        B.shared.all (fun r => p₂.contains r.1.place) &&
        B.second.all fun r => p₃.contains r.1.place),
    ("a part has two rows", rows.all fun r => (rows.filter fun q => q.1 == r.1).length == 1),
    ("a place states more mask words than its parts have coins",
      masksOk F.first.blocksInOrder B.first && masksOk F.shared.blocksInOrder B.shared &&
        masksOk F.second.blocksInOrder B.second),
    ("an entry's run is not within its owner's count", B.ahead.all fun a =>
      decide (a.start.f + a.count.f ≤ (dueAt rows a.owner).f) &&
        decide (a.start.e + a.count.e ≤ (dueAt rows a.owner).e)),
    ("an entry's spender does not stand behind its owner", B.ahead.all fun a =>
      all.contains a.owner.place && all.contains a.spender.place &&
        a.owner.before all a.spender),
    ("the shared chain is handed a coin of the first chain", B.ahead.all fun a =>
      !(p₁.contains a.owner.place && p₂.contains a.spender.place)),
    ("a coin stands in two entries that spend it", spent.all fun p => spent.all fun q =>
      p.2 == q.2 || !p.1.shares q.1),
    ("a coin that a part spends is handed to a part in front of it, or to itself as carried",
      es.all fun p => !p.1.once || es.all fun q =>
        p.2 == q.2 || !p.1.shares q.1 ||
          !(q.1.spender.before all p.1.spender || (q.1.spender == p.1.spender && !q.1.once))),
    ("a coin of the shared chain is spent outside it", B.ahead.all fun a =>
      !(a.once && p₂.contains a.owner.place && !p₂.contains a.spender.place)),
    ("a cut stands at no place, stands twice, has a part without a round or does not add up",
      B.cuts.all fun c =>
        sizes.lookup c.1 == some (c.2.foldl (· + ·) 0) && c.2.all (· != 0) &&
          (B.cuts.filter fun d => d.1 == c.1).length == 1),
    ("two entries bear one name", B.ahead.all fun a =>
      (B.ahead.filter fun b => b.name == a.name).length == 1)]

/-- The name of the first test on the book that fails. `none`: every test passes. -/
def ProverCoinCounts.word (F : FileDescription Xi) (B : ProverCoinCounts) : Option String :=
  ((B.clauses F).find? (!·.2)).map (·.1)

/-! ## 4 The prover's side of a sub-protocol, and the type of a simulator -/

/-- What has been shown before a round, as far as a part is given it: the rounds as a view shows
them, and where they are handed the opened columns. The first chain's sealing round has an entry
here too (no item, the empty challenge), which the first view lacks. -/
structure Seen where
  rounds : List Fmt.RoundView
  /-- the columns that the sub-protocols before this round have read, flat, in the order of reading.
  In the first and in the shared chain: of that chain's own sub-protocols alone. In the second
  chain: all of the first chain's, then all of the shared chain's, then its own. A column's key is
  its own chain's (`readsOf`): in this list two trees can bear one key. A column is found by its
  place in the order of reading, not by its key. `none`: this player hands no columns. `some []`:
  none of these has been opened yet. `runC` (Walk.lean) fills it, and so do `midAtW` and
  `midSharedAtW` (MidW.lean); `run`, `midAt` and `midSharedAt` do not. A DUTY OF EVERY PART THAT
  READS IT: AT `none` IT ERRS; it never takes `[]`, or another default, in its stead -/
  opened : Option (List OpenedColumn)

/-- The last `n` rounds that were shown. At a part's round number `n`, from 0, they are the part's
own so far. If `n` exceeds the length: the whole list. -/
def Seen.lately (s : Seen) (n : Nat) : List Fmt.RoundView := s.rounds.drop (s.rounds.length - n)

/-- Rounds alone: no columns are handed. -/
def Seen.bare (rounds : List Fmt.RoundView) : Seen := ⟨rounds, none⟩

/-- All but the last `n` rounds: the rest of `Seen.lately s n`. The columns are carried on. -/
def Seen.front (s : Seen) (n : Nat) : Seen := ⟨s.rounds.take (s.rounds.length - n), s.opened⟩

/-- The same with further rounds shown; the columns are carried on. -/
def Seen.plus (s : Seen) (l : List Fmt.RoundView) : Seen := ⟨s.rounds ++ l, s.opened⟩

/-- No round more: the same. -/
theorem Seen.plus_nil (s : Seen) : s.plus [] = s := by
  show (⟨s.rounds ++ [], s.opened⟩ : Seen) = s
  rw [List.append_nil]

/-- Rounds laid behind twice are laid behind once. -/
theorem Seen.plus_plus (s : Seen) (a b : List Fmt.RoundView) : (s.plus a).plus b = s.plus (a ++ b) := by
  show (⟨(s.rounds ++ a) ++ b, s.opened⟩ : Seen) = ⟨s.rounds ++ (a ++ b), s.opened⟩
  rw [List.append_assoc]

/-- All but the last n rounds, where just n were laid behind: what stood before. -/
theorem Seen.front_plus (s : Seen) (l : List Fmt.RoundView) (n : Nat) (h : l.length = n) :
    (s.plus l).front n = s := by
  show (⟨(s.rounds ++ l).take ((s.rounds ++ l).length - n), s.opened⟩ : Seen) = s
  rw [List.length_append, h, Nat.add_sub_cancel, List.take_left']
  rfl

/-- The prover's state. The functions of this file keep `input` and `heard`: no move can change
them. -/
structure State (W X : Type) where
  input : W
  /-- the challenges heard so far, the newest last -/
  heard : List Fmt.Drawn
  /-- what the parts pass on to each other -/
  own : X

/-- The state after a challenge. -/
def State.hears (t : State W X) (d : Fmt.Drawn) : State W X :=
  { t with heard := t.heard ++ [d] }

/-- The last `n` challenges heard. At a part's round number `n`, from 0, they are the part's own so
far. If `n` exceeds the length: the whole list. -/
def State.lately (t : State W X) (n : Nat) : List Fmt.Drawn := t.heard.drop (t.heard.length - n)

/-- The state as it is given to a part that has an input type W' and a state type Y of its own. -/
def State.narrow (wit : W → W') (get : X → Y) (t : State W X) : State W' Y :=
  ⟨wit t.input, t.heard, get t.own⟩

/-- The prover's side of one round. C: the coins that the part is given. -/
structure Move (C W X : Type) where
  /-- the message, from the coins, what has been shown, and the state. An error here is a fault of
  the part's definition, not a stop: a stop is `Part.bad`'s or `Part.hid`'s -/
  say : C → Seen → State W X → Except String Sending
  /-- what is passed on after the round's challenge, which the state already holds. It is given no
  coin and nothing that was sent: so by type `own` is computed from the input and the challenges
  alone -/
  hand : State W X → X

/-- A move that has an input type W' and a state type Y of its own, as a move at W and X: it reads
its input by `wit` and its state by `get`, and writes back what it passes on by `set`. That it
changes nothing else of X is up to `set`: nothing here asks that `get` and `set` fit each other. -/
def Move.lift (wit : W → W') (get : X → Y) (set : X → Y → X) (mv : Move C W' Y) : Move C W X :=
  ⟨fun c s t => mv.say c s (t.narrow wit get), fun t => set t.own (mv.hand (t.narrow wit get))⟩

/-- A move that is typed at coins C', as a move at coins C, of which `cut` takes its own. -/
def Move.recoin (cut : C → C') (mv : Move C' W X) : Move C W X :=
  ⟨fun c => mv.say (cut c), mv.hand⟩

/-- The coins that a part is given: its own; the blocks that it spends; the blocks that it carries.
-/
abbrev Handed (takes : Due) (spends carries : List (String × Due)) : Type :=
  Cs takes × CsAll spends × CsAll carries

/-- Of what two parts as one are given: the first part's. -/
def handFst {a b : Due} {s₁ s₂ c₁ c₂ : List (String × Due)}
    (c : Handed (a.plus b) (s₁ ++ s₂) (c₁ ++ c₂)) : Handed a s₁ c₁ :=
  (c.1.split.1, (CsAll.split s₁ s₂ c.2.1).1, (CsAll.split c₁ c₂ c.2.2).1)

/-- The second part's. -/
def handSnd {a b : Due} {s₁ s₂ c₁ c₂ : List (String × Due)}
    (c : Handed (a.plus b) (s₁ ++ s₂) (c₁ ++ c₂)) : Handed b s₂ c₂ :=
  (c.1.split.2, (CsAll.split s₁ s₂ c.2.1).2, (CsAll.split c₁ c₂ c.2.2).2)

/-- **A stated share**: `num` of `den`. A number that somebody states, as data; no bound. -/
structure Odds where
  num : Nat
  den : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The sum of two shares, as fractions are added; not reduced. At the denominator 0 a share is not
to be read: the type's default, 0 of 0, absorbs whatever is added to it (Honest/Shares.lean:
`Odds.ok`); whoever quotes this sum takes that test by name. -/
def Odds.plus (a b : Odds) : Odds := ⟨a.num * b.den + b.num * a.den, a.den * b.den⟩

/-- **A part**: the prover's side of a stretch of a sub-protocol's rounds, with one move for each.
It states how many coins it takes, and its moves are typed at these counts. A part is the unit that
gets coins and has stops. `Side.row` (Honest/Side.lean) pairs each part with one term of type `Sim`.
A list is meant to be cut no finer than this: one masked sumcheck with its lead and its end values;
one fold; one sending with its out-of-domain answers. V: what the second stop may read. -/
structure Part (V W X : Type) where
  /-- its own coins -/
  takes : Due
  /-- the entries of the book with `once := true` that name it, in the book's order: their names and
  their counts. `lend` compares both with the book -/
  spends : List (String × Due)
  /-- the entries with `once := false` that name it, in the book's order: their names and counts -/
  carries : List (String × Due)
  /-- the first stop, asked before each of the part's rounds and once more after its last: from the
  challenges before the part (in the second chain: the first and the second chain's alone, without
  the shared chain's: `Ready.start₃`), and the part's own so far. No coin and no input, by type. In
  the first and the second chain it takes the place of the library's `Bad`, in the shared chain of
  its `stop0` (`Iop.BatchHonestProver`, Iop/Batch.lean). No default -/
  bad : List Fmt.Drawn → List Fmt.Drawn → Option String
  /-- the second stop, asked as the first is, and given V too: in the first and the second chain V
  is the prover's whole input, the index and the stored tables' pads and encoding randomness
  included (`Face.own`). It takes the place of the library's `Hid`, which is the library's name for
  a set of challenges and says nothing on a property. No coin of the run, by type. In the shared
  chain V is `Empty`: there the library has no such field. No default -/
  hid : V → List Fmt.Drawn → List Fmt.Drawn → Option String
  /-- a stated number, no bound: the number stated for the share of the lists of
  challenges at which the first stop stops the part. Nothing compares it with the stop: that the
  share is at most this has to be proved by whoever relies on it. The library measures such sets as
  probabilities over uniform challenges (`prB`, Hiop/RecInterface.lean). A part whose stop never
  fires states 0 of 1. No default -/
  badShare : Odds
  /-- the same for the second stop, at every V. No default -/
  hidShare : Odds
  moves : List (Move (Handed takes spends carries) W X)

/-- The coins that the part is given. -/
abbrev Part.Coins (p : Part V W X) : Type := Handed p.takes p.spends p.carries

/-- The part is given no block of another part's coins. -/
def Part.plain (p : Part V W X) : Bool := p.spends.isEmpty && p.carries.isEmpty

/-- **A part placed in a wider input and state**, as `Block.lift` (Johnson/Desc/Block.lean) places a
sub-protocol in a wider state: one definition, with type parameters of its own, can be used at many
places. Its counts and its first stop stay; its second stop reads V by `see`. -/
def Part.lift (see : V → V') (wit : W → W') (get : X → Y) (set : X → Y → X) (p : Part V' W' Y) :
    Part V W X :=
  { takes := p.takes, spends := p.spends, carries := p.carries, bad := p.bad
    hid := fun v => p.hid (see v), badShare := p.badShare, hidShare := p.hidShare
    moves := p.moves.map (Move.lift wit get set) }

/-- Of two parts as one: a stop of the first, asked while the first part's rounds last and after its
last; then the same stop of the second, asked from there on, at the lists that it would be given as
a part of its own. `n`, `m`: the two parts' numbers of rounds. A part without a round (`n` or `m` is
0) is not asked. -/
def stopBoth (n m : Nat) (f g : List Fmt.Drawn → List Fmt.Drawn → Option String)
    (front own : List Fmt.Drawn) : Option String :=
  (if n != 0 && decide (own.length ≤ n) then f front own else none).or
    (if m != 0 && decide (n ≤ own.length) then g (front ++ own.take n) (own.drop n) else none)

/-- **Two parts as one**, as `Block.andThen` joins two sub-protocols: the counts are added up, the
lists of entries concatenated, and what the one part is given is divided between the two by type.
The moves are the two parts' own. By a reading of the definitions, not proved: it shows what the two
show as two parts of a list, at the same coins, where no entry goes from the first to the second
(the one part would be its own spender, which the book's tests reject) and the book lists the first
part's entries before the second's. One thing differs: at the challenges between the two, the list
asks the first part's two stops and then the second's, while the one part asks both first stops and
then both second stops. So an error's class can differ there, not whether there is one. -/
def Part.andThen (p q : Part V W X) : Part V W X :=
  { takes := p.takes.plus q.takes, spends := p.spends ++ q.spends
    carries := p.carries ++ q.carries
    bad := stopBoth p.moves.length q.moves.length p.bad q.bad
    hid := fun v => stopBoth p.moves.length q.moves.length (p.hid v) (q.hid v)
    badShare := p.badShare.plus q.badShare, hidShare := p.hidShare.plus q.hidShare
    moves :=
      p.moves.map (Move.recoin (handFst (b := q.takes) (s₂ := q.spends) (c₂ := q.carries))) ++
        q.moves.map (Move.recoin (handSnd (a := p.takes) (s₁ := p.spends) (c₁ := p.carries))) }

/-- **The prover's side of a sub-protocol, at its place**: a list of parts, whose rounds, in the
list's order, are the sub-protocol's. A sub-protocol that needs no cut has a list of one part. -/
structure Placed (V W X : Type) where
  place : Place
  parts : List (Part V W X)

/-- The number of a list's rounds. -/
def Placed.rounds (h : Placed V W X) : Nat := h.parts.foldl (fun n p => n + p.moves.length) 0

/-- The shares that the parts of a list of prover's sides state, added up: of the first stop; of the
second. Stated numbers added up: no bound. At the denominator 0 a share is not to be read: the
type's default, 0 of 0, absorbs whatever is added to it (Honest/Shares.lean: `halvesSharesOk`);
whoever quotes this sum takes that test by name. -/
def statedShares (hs : List (Placed V W X)) : Odds × Odds :=
  (hs.flatMap (·.parts)).foldl (fun s p => (s.1.plus p.badShare, s.2.plus p.hidShare))
    (⟨0, 1⟩, ⟨0, 1⟩)

/-- The coins that the parts of a list are given, part by part. -/
def RowCoins : List (Part V W X) → Type
  | [] => Unit
  | p :: l => p.Coins × RowCoins l

/-- A kind's honest side: from a place's public data to the prover's side there, as `Kind`
(Johnson/Desc/Block.lean) is for the sub-protocol. -/
abbrev KindHalf (P V W X : Type) : Type := P → Placed V W X

/-- What is shown of one round of a part: the items in the clear; and, for each root of the round,
the columns at the positions that are read of the oracle message under it, each with its position.
-/
structure Shown where
  vals : List Fmt.ItemValue
  cols : List (List (Nat × List UInt64))
  deriving DecidableEq

/-- **What a part's simulator is given of the run before its part.** It is wider than `Seen`, which
holds the earlier rounds as a part sees them and, where they are handed, the columns opened before
the part's place. It also holds the columns of earlier tables and of the stored tables at every
position that the whole run reads, later reads included. In a real run these values are the prover's
own and depend on its input. -/
structure Before where
  /-- round by round, in the order in which `Seen` has them: the number, from 0, of the chain to
  which the round belongs; what is shown of the round, with its tables' columns at all positions
  that are read of them in the whole run, whichever round reads them; and the round's challenge -/
  rounds : List (Nat × Shown × Fmt.Drawn)
  /-- the stored tables' columns that are read in the whole run: the statement's item, the position,
  the words -/
  stored : List (Nat × Nat × List UInt64)

/-- Of that, the rounds that a part is given, as a view shows them. The opened columns' counterpart
is `Before.opened` (Honest/Side.lean). -/
def Before.seen (f : Before) : List Fmt.RoundView := f.rounds.map fun r => ⟨r.2.1.vals, r.2.2⟩

/-- **The type of a part's simulator.** `Pb` is the type of the input's public field (`Face.pub`).
The five arguments of `tell` are all that a simulator is given, and the run's coins are not among
them. The type does not make these arguments harmless: `Pb` is a parameter, and a `Before` is
whatever the caller supplies. A term of this type need not simulate anything: `Good.exact`
(Honest/Side.lean) is the condition that relates it to its part. -/
structure Sim (Pb : Type) where
  addr : Addr
  /-- its own coins -/
  takes : Due
  /-- `tell` takes five arguments. They are the input's public field, a `Before`, the challenges of
  the part's rounds (all in advance), the positions that will be read, and the simulator's own
  coins. The positions are listed round by round and, within a round, root by root. A `Before` holds
  the earlier rounds' messages and challenges, and opened columns of earlier tables and of the
  stored tables. `tell` outputs one `Shown` for each round, or `none`. -/
  tell : Pb → Before → List Fmt.Drawn → List (List (List Nat)) → Cs takes → Option (List Shown)

/-- A kind's simulators: from a place's public data to a list of simulators, meant to hold one for
each part; the type does not tie its length to the parts. -/
abbrev KindSim (P Pb : Type) : Type := P → List (Sim Pb)

/-- The input of a prover's side in the shared chain, in three components: the index (what all
requests share); the stored tables' pads and encoding randomness; the key, which is what the shared
chain may read of the public instance. -/
structure Common (W₀ Rc Ky : Type) where
  w₀ : W₀
  rc : Rc
  key : Ky

/-- The input of a prover's side in the first or the second chain, in four components: the index
(what all requests share); the stored tables' pads and encoding randomness; the public instance; the
witness, which is the request's trace. -/
structure Local (W₀ Rc Xi Tr : Type) where
  w₀ : W₀
  rc : Rc
  x : Xi
  trace : Tr

/-- **How a chain's prover's sides are given their input.** `V`: what a second stop may read. `W`:
the input. `Pb`: the type of its public field, which a simulator is given. There are just these two,
by type: `run` plays by them, and a condition on a side takes one of them. So which field of an
input is public, and whether a second stop may read the input, is nobody's to choose. In `run`, `Xi`
is the description's own instance and the key is computed from it. The types `Xi` and `Ky` are
parameters: a statement that names no description leaves both free. -/
inductive Face : Type → Type → Type → Type 1 where
  /-- in the first and the second chain -/
  | own {W₀ Rc Xi Tr : Type} : Face (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) Xi
  /-- in the shared chain -/
  | shared {W₀ Rc Ky : Type} : Face Empty (Common W₀ Rc Ky) Ky

/-- The public field of an input: the public instance; in the shared chain the key. -/
def Face.pub {V W Pb : Type} : Face V W Pb → W → Pb
  | .own, w => w.x
  | .shared, w => w.key

/-- What a second stop may read: the input. In the shared chain that stop is not asked. -/
def Face.sees {V W Pb : Type} : Face V W Pb → W → Option V
  | .own, w => some w
  | .shared, _ => none

/-- **The honest prover of a file's three chains.** W₀: the index, which is the part of the input
that all requests share. Rc: the pads and encoding randomness with which the stored tables that the
statement names were encoded. It is part of the input: fixed before the run, with these tables, and
apart from a run's `Coins`. Who draws it, when, and whether two runs share it is not said in this
file. (The library has two typed schemes. In the prover of a whole request the prover encodes one
copy of the committed table for each request, at a value that it draws with the request: `Draw`,
`allY`, `proveA`, Johnson/Prover/All/Defs.lean. In the scheme with the whole key the committer draws
a value for the first table and one for each copy, and a copy serves many requests: `coinsC`,
`proveAt`, Johnson/WholeKey/Defs.lean. In both, each value is a draw of its own through an
enumeration that is a letter: no clause of these definitions says how it is distributed, or that two
tables' values differ.) Xi: the public instance. Ky: what the shared chain may read of it. Tr: the
witness, which is a request's trace. X₀, X: what the parts pass on, in the shared chain and in the
two others. -/
structure Prover (W₀ Rc Xi Ky Tr X₀ X : Type) where
  /-- the stored tables' columns, by the statement's item and the position, typed in the field, as a
  table's symbol is; `Prover.storedWords` converts them to words; `none`: no column there:
  `fillCols` then takes the stored run's column or returns an error -/
  stored : W₀ → Rc → Nat → Nat → Option (List Cb.Gl.F)
  /-- a request's trace: a function, which `ready` applies; `none` if there is none -/
  trace : W₀ → Xi → Option Tr
  /-- the key: what the prover's sides in the shared chain are given of the public instance: a
  function, which `ready` applies. It is meant for the stored table's out-of-domain seeds and
  answers. It is no part of Rc and no coin of a run. No type compares it with what `FileDescription.start₂`
  reads -/
  key : Xi → Ky
  /-- in range: a test on what all requests share. `run` applies it to w₀ -/
  inRange : W₀ → Bool
  /-- a named element of W₀: `readyTests` returns an error unless `inRange` is true of it, so a
  prover that passes has a range that is not empty. No other function of this file reads it -/
  dummy : W₀
  /-- what the parts pass on, at the start of the first chain -/
  own₀ : X
  /-- the same at the start of the shared chain -/
  ownShared₀ : X₀
  first : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)
  shared : List (Placed Empty (Common W₀ Rc Ky) X₀)
  second : List (Placed (Local W₀ Rc Xi Tr) (Local W₀ Rc Xi Tr) X)
  /-- what the second chain's prover's sides are given at their start, from what the first chain's
  passed on and from the shared chain's end, as `FileDescription.start₃` does for the verifier -/
  meet : X → State (Common W₀ Rc Ky) X₀ → X

/-- The stored tables' columns as a view shows them: each element as the word below the prime that
represents it (`ofF`, OnBytes/Slice/Field.lean). -/
def Prover.storedWords (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (item x : Nat) :
    Option (List UInt64) :=
  (H.stored w₀ rc item x).map (·.map OnBytes.Slice.ofF)

/-! ## 5 Playing a chain's rounds -/

/-- The classes of an error of the honest side. -/
inductive Why where
  /-- the prover, the book or the arguments do not fit the description; or a part's definition is at
  fault -/
  | unfit
  /-- what all requests share is out of range -/
  | noIndex
  /-- the request has no trace -/
  | noTrace
  /-- the run was stopped by a first stop -/
  | bad
  /-- the run was stopped by a second stop -/
  | hid
  deriving DecidableEq, Repr

/-- An error: its class, and words for the tests. `outcome` forgets both. -/
structure Refusal where
  why : Why
  words : String

/-- An error in words alone, as one of the class `unfit`. -/
def unfit {α : Type} (e : Except String α) : Except Refusal α := e.mapError fun s => ⟨.unfit, s⟩

/-- One round of a chain, as `play` meets it: the sub-protocol's name, the part's address, what the
sub-protocol declares of the round; and, if a prover's side is defined at that place, the part's two
stops and its move, with the coins and what the second stop may read already supplied. Where none is
defined the address's number is 0, both stops are constantly `none`, and there is no move. -/
structure Step (W X : Type) where
  name : String
  addr : Addr
  decl : Fmt.DeclaredRound
  oracles : List Oracle
  bad : List Fmt.Drawn → List Fmt.Drawn → Option String
  hid : List Fmt.Drawn → List Fmt.Drawn → Option String
  /-- the round's number in its part, from 0 -/
  nth : Nat
  /-- it is the last round of a part: after it the stops are asked once more -/
  last : Bool
  move : Option (Move Unit W X)

/-- The two stops, the first one first: an error of its class, or none. `l`: the challenges so far
that the stops may read. `n`: how many of them, the last ones, are the part's own. -/
def Step.stop (s : Step W X) (l : List Fmt.Drawn) (n : Nat) : Option Refusal :=
  let front := l.take (l.length - n)
  let own := l.drop (l.length - n)
  match s.bad front own, s.hid front own with
  | some e, _ => some ⟨.bad, s.name ++ ": " ++ e⟩
  | none, some e => some ⟨.hid, s.name ++ ": " ++ e⟩
  | none, none => none

/-- The places of prover's sides at which the chain has no sub-protocol. -/
def strays (bs : List (Block S Cl)) (hs : List (Placed V W X)) : List Place :=
  (hs.filter fun h => !(bs.any fun b => b.place == h.place)).map (·.place)

/-- The places at which more than one prover's side is defined. -/
def twice (hs : List (Placed V W X)) : List Place :=
  ((hs.map (·.place)).filter fun a => 1 < (hs.filter fun h => h.place == a).length).eraseDups

/-- The blocks that entries give, cut out of their owners' coins, at the names and counts at which
the part is typed. An error if these are not the entries' own names and counts, one by one, or a
block is not available. `look`: the coins that this chain may be given, by address. -/
def lend (look : Addr → (d : Due) × Cs d) :
    (ds : List (String × Due)) → List Ahead → Except String (CsAll ds)
  | [], [] => .ok ()
  | d :: ds, a :: l =>
    if a.name != d.1 then
      .error (a.name ++ ": the part names another run here: " ++ d.1)
    else if a.count != d.2 then
      .error (a.name ++ ": the part is typed at another count than the entry has")
    else
      match (look a.owner).2.cut a.start d.2 with
      | none => .error (a.name ++ ": the owner's coins are not at hand")
      | some x => (lend look ds l).map fun y => (x, y)
  | _, _ => .error "it is typed at another number of entries than the book hands it"

/-- **The coins that the part at an address is given**: its own, and the blocks of the entries that
name it as their spender, and no other part's. `rows`: the book's table for this chain. An error if
the part takes more or fewer coins than the book has for it, if its coins are not available, or if
`lend` returns one. -/
def lendPart (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (a : Addr)
    (p : Part V W X) : Except String p.Coins :=
  let mine := B.ahead.filter fun e => e.spender == a
  if p.takes != dueAt rows a then
    .error "it takes more or fewer coins than the book has for it"
  else
    match (look a).2.cut ⟨0, 0⟩ p.takes with
    | none => .error "its coins are not at hand"
    | some own =>
      (lend look p.spends (mine.filter (·.once))).bind fun sp =>
      (lend look p.carries (mine.filter (!·.once))).map fun ca => (own, sp, ca)

/-- The coins that the parts of a list at the place `a` are given, part by part, from part number
`j` on: each by `lendPart`. -/
def lendRow (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d) (a : Place) :
    (ps : List (Part V W X)) → Nat → Except String (RowCoins ps)
  | [], _ => .ok ()
  | p :: ps, j =>
    ((lendPart B rows look ⟨a, j⟩ p).mapError fun e => "part " ++ toString j ++ ": " ++ e).bind
      fun c => (lendRow B rows look a ps (j + 1)).map fun r => (c, r)

/-- A part's rounds, with its coins and what its second stop may read supplied. `rs`: the rounds of
the sub-protocol that are the part's, each with its oracle messages. -/
def Part.steps (p : Part V W X) (name : String) (a : Addr)
    (rs : List (Fmt.DeclaredRound × List Oracle)) (v : Option V) (c : p.Coins) : List (Step W X) :=
  (rs.zip p.moves).zipIdx.map fun r =>
    ⟨name, a, r.1.1.1, r.1.1.2, p.bad, fun f o => v.bind fun w => p.hid w f o, r.2,
      r.2 + 1 == p.moves.length, some ⟨fun _ => r.1.2.say c, r.1.2.hand⟩⟩

/-- A list's rounds: the sub-protocol's rounds are divided among the parts in the list's order, each
part getting as many as it has moves. `j`: the first part's number. -/
def rowSteps (name : String) (a : Place) (v : Option V) :
    (ps : List (Part V W X)) → Nat → List (Fmt.DeclaredRound × List Oracle) → RowCoins ps →
      List (Step W X)
  | [], _, _, _ => []
  | p :: ps, j, rs, c =>
    p.steps name ⟨a, j⟩ (rs.take p.moves.length) v c.1 ++
      rowSteps name a v ps (j + 1) (rs.drop p.moves.length) c.2

/-- The rounds of one sub-protocol at whose place a prover's side is defined. -/
def Placed.steps (h : Placed V W X) (b : Block S Cl) (v : Option V) (c : RowCoins h.parts) :
    List (Step W X) :=
  rowSteps b.name b.place v h.parts 0 (b.rounds.zip b.oracles) c

/-- A chain's rounds, sub-protocol by sub-protocol of the description's own flat list. `rows`: the
book's table for this chain. An error if a sub-protocol's lists of rounds and of oracle messages
differ in length, if a prover's side has another number of rounds than the sub-protocol, if the book
has no cut for its place or the list is cut differently, if the book has a row or an entry for a
part that the prover's side does not have, or if `lendRow` returns one. -/
def chainSteps (B : ProverCoinCounts) (rows : List (Addr × Due)) (look : Addr → (d : Due) × Cs d)
    (v : Option V) : List (Block S Cl) → List (Placed V W X) → Except String (List (Step W X))
  | [], _ => .ok []
  | b :: bs, hs =>
    if b.oracles.length != b.rounds.length then
      .error (b.name ++ ": its lists of rounds and of oracle messages differ in length")
    else
      match hs.find? fun h => h.place == b.place with
      | none =>
        (chainSteps B rows look v bs hs).map fun l =>
          (b.rounds.zip b.oracles).map (fun r => (⟨b.name, ⟨b.place, 0⟩, r.1, r.2,
            fun _ _ => none, fun _ _ => none, 0, false, none⟩ : Step W X)) ++ l
      | some h =>
        if h.rounds != b.rounds.length then
          .error (b.name ++ ": the prover's half has another number of rounds")
        else if B.cuts.lookup b.place != some (h.parts.map (·.moves.length)) then
          .error (b.name ++ ": the book has no cut for this place, or the row is cut otherwise")
        else if rows.any (fun r => r.1.place == b.place && decide (h.parts.length ≤ r.1.part)) then
          .error (b.name ++ ": the book has a row for a part that the half does not have")
        else if B.ahead.any (fun e =>
            e.spender.place == b.place && decide (h.parts.length ≤ e.spender.part)) then
          .error (b.name ++ ": an entry of the book names a part that the half does not have")
        else
          ((lendRow B rows look b.place h.parts 0).mapError (b.name ++ ": " ++ ·)).bind fun c =>
          (chainSteps B rows look v bs hs).map fun l => h.steps b v c ++ l

/-- A round as it was played. -/
structure Played where
  name : String
  place : Place
  /-- the number of the part that made the message; 0 where no prover's side is defined -/
  part : Nat
  /-- a prover's side made the message -/
  told : Bool
  /-- the items in the clear, as a view shows them -/
  vals : List Fmt.ItemValue
  /-- for each root of the round: the table, if a prover's side sent it -/
  tables : List (Option Table)
  drawn : Fmt.Drawn

/-- The state of a chain's run between two rounds. -/
structure Mid (W X : Type) where
  st : State W X
  /-- the challenges heard so far that the stops may read -/
  loc : List Fmt.Drawn
  /-- the rounds shown so far that a part may read -/
  seen : List Fmt.RoundView
  /-- the columns opened so far that a part may read, as `Seen.opened` has them. No round changes
  it: `ChainProgress.start` (Walk.lean) sets it, and `ChainProgress.settle` lengthens it after a sub-protocol's last
  round -/
  opened : Option (List OpenedColumn)

/-- A state at which no columns are handed. -/
def Mid.bare (st : State W X) (loc : List Fmt.Drawn) (seen : List Fmt.RoundView) : Mid W X :=
  ⟨st, loc, seen, none⟩

/-- What a part is handed of it as `Seen`. -/
def Mid.shown (m : Mid W X) : Seen := ⟨m.seen, m.opened⟩

/-- The same state after a sub-protocol that has read the columns `cols`. Where no columns are
handed, none are. It is the only function of this file that lengthens the field; `ChainProgress.start`
(Walk.lean) sets it at a chain's start. -/
def Mid.took (m : Mid W X) (cols : List OpenedColumn) : Mid W X :=
  { m with opened := m.opened.map (· ++ cols) }

/-- What a round sends, before its challenge is heard. -/
structure Told where
  /-- the items in the clear, as a view shows them -/
  vals : List Fmt.ItemValue
  /-- for each root of the round: the table, if a prover's side sent it -/
  tables : List (Option Table)
  /-- a prover's side made the message -/
  told : Bool

/-- **A round's message.** First the part's two stops are asked; then the move computes the message,
and its shape is compared with what the sub-protocol declares. An item's elements are converted to
words here. `back`: a stored run's round, to fall back on where no prover's side is defined. No
challenge of this round is read: `back` has the field `drawn`, which this definition does not read
(it reads `vals` alone, and only where there is no move), and a move is not given `back`. -/
def Step.tell (s : Step W X) (back : Option Fmt.RoundView) (m : Mid W X) : Except Refusal Told :=
  match s.stop m.loc s.nth with
  | some e => .error e
  | none =>
    match s.move with
    | some mv =>
      match mv.say () m.shown m.st with
      | .error e => .error ⟨.unfit, s.name ++ ": " ++ e⟩
      | .ok x =>
        if !x.fits s.decl s.oracles then
          .error ⟨.unfit, s.name ++ ": the message has another shape than the sub-protocol states"⟩
        else .ok ⟨x.vals.map Said.got, x.tables.map some, true⟩
    | none => .ok ⟨(back.map (·.vals)).getD [], List.replicate s.decl.entry.roots none, false⟩

/-- **After a round's challenge**: the state hears it; after a part's last round its two stops are
asked once more; the move passes on. `x`: what the round has sent. -/
def Step.hear (s : Step W X) (x : Told) (d : Fmt.Drawn) (m : Mid W X) :
    Except Refusal (Mid W X) :=
  let t := m.st.hears d
  match s.move with
  | some mv =>
    match (if s.last then s.stop (m.loc ++ [d]) (s.nth + 1) else none) with
    | some e => .error e
    | none => .ok ⟨{ t with own := mv.hand t }, m.loc ++ [d], m.seen ++ [⟨x.vals, d⟩], m.opened⟩
  | none => .ok ⟨t, m.loc ++ [d], m.seen ++ [⟨x.vals, d⟩], m.opened⟩

/-- A run of a chain's rounds at given challenges: round by round `Step.tell`, then `Step.hear`.
`back`: a stored run's rounds, by index, to fall back on. An error if the challenges are not as many
as the rounds. A `back` that is shorter gives nothing to fall back on from there; a longer one's
rest is ignored. -/
def play : List (Step W X) → List Fmt.Drawn → List Fmt.RoundView → Mid W X →
    Except Refusal (List Played × Mid W X)
  | [], [], _, m => .ok ([], m)
  | s :: ss, d :: ds, back, m =>
    (s.tell back.head? m).bind fun x =>
    (s.hear x d m).bind fun m' =>
    (play ss ds back.tail m').map fun y =>
      (⟨s.name, s.addr.place, if x.told then s.addr.part else 0, x.told, x.vals, x.tables, d⟩ ::
        y.1, y.2)
  | _, _, _, _ => .error ⟨.unfit, "the challenges are not as many as the rounds"⟩

/-- **The state of a chain's run before the part at an address**: the rounds before it, played. An
error at an address that has no round in the list. -/
def midIn (steps : List (Step W X)) (ds : List Fmt.Drawn) (back : List Fmt.RoundView) (m : Mid W X)
    (a : Addr) : Except Refusal (Mid W X) :=
  let n := (steps.takeWhile fun s => s.addr != a).length
  if !steps.any (·.addr == a) then .error ⟨.unfit, "no round of the chain stands at the address"⟩
  else (play (steps.take n) (ds.take n) back m).map (·.2)

/-! ## 6 The views -/

/-- A column that is read: its key and position as `groupsOf` (Johnson/Desc/Block.lean) has them. -/
structure Read where
  key : Nat
  pos : Nat
  /-- of a stored table: the statement's item -/
  item : Option Nat
  /-- of a tree: the chain that sent it, from 0, and its number in that chain's order of sending -/
  src : Option (Nat × Nat)
  /-- the place of the sub-protocol whose prover's side sent the table, if one did -/
  sender : Option Place
  /-- the column's words, if the table is available -/
  words : Option (List UInt64)
  /-- how many words the round that reads it declares for the column -/
  width : Nat

/-- A tree's sender and number, from its source as a round of chain number `chain` declares it. -/
def srcOf (chain : Nat) : Fmt.TreeSource → Nat × Nat
  | .own n => (chain, n)
  | .taken ch k => (ch, k)

/-- What declared rounds read at given challenges, in the order of `groupsOf`. `chain`: the chain's
number, from 0. `stored`: the stored tables' columns, by the statement's item and the position.
`tree`: the table behind a source, with its sender's place. `firstTree`: the number in the label of
the chain's first own tree: a tree's key is its own number less that, cut off at 0, as in
`groupsOf`. -/
def readsOf (chain firstTree : Nat) (stored : Nat → Nat → Option (List UInt64))
    (tree : Fmt.TreeSource → Option (Place × Table)) :
    List Fmt.DeclaredRound → List Fmt.Drawn → List Read
  | d :: ds, R :: Rs =>
    (d.stored.flatMap fun s =>
      (Fmt.listOf ((Fmt.partOf s R.poss).map (· % 2 ^ s.sh.a))).map fun x =>
        (⟨Fmt.storedKey s.item, x, some s.item, none, none, stored s.item x, s.sh.W⟩ : Read)) ++
    (d.opens.flatMap fun o =>
      (Fmt.listOf (R.poss.map (· % 2 ^ o.1.a))).map fun x =>
        (⟨o.1.tree - firstTree, x, none, some (srcOf chain o.2), (tree o.2).map (·.1),
          (tree o.2).map (·.2.col x), o.1.W⟩ : Read)) ++
    readsOf chain firstTree stored tree ds Rs
  | _, _ => []

/-- The columns of a view: each read's own words, or the stored run's column at the same index, if
it has the same key and position. An error if neither is available, or if a column has another
number of words than the round that reads it declares: a stored table's, a tree's and a stored run's
alike. -/
def fillCols : List Read → List OpenedColumn → Except String (List OpenedColumn)
  | [], _ => .ok []
  | r :: rs, back =>
    match r.words, back.head? with
    | some w, _ =>
      if w.length != r.width then .error "a column has another width than the round states"
      else (fillCols rs back.tail).map fun l => (r.key, r.pos, w) :: l
    | none, some c =>
      if !(c.1 == r.key && c.2.1 == r.pos) then
        .error "a stored column stands at another key or position than the one that is read"
      else if c.2.2.length != r.width then
        .error "a column has another width than the round states"
      else (fillCols rs back.tail).map fun l => c :: l
    | none, none => .error "a column is read of a table that is not at hand"

/-- A run's tables in the order of sending, each with its sender's place; `none` where no prover's
side sent the table. -/
def tablesOf (l : List Played) : List (Option (Place × Table)) :=
  l.flatMap fun p => p.tables.map fun t => t.map fun x => (p.place, x)

/-- The table behind a source, with its sender's place, in the first and in the shared chain: the
chain's own tree of that number, from the played rounds. Nothing is taken over from another chain
there. -/
def treeOwn (l : List Played) : Fmt.TreeSource → Option (Place × Table)
  | .own n => ((tablesOf l)[n]?).bind id
  | .taken _ _ => none

/-- The same in the second chain: its own tree, or one taken over from the first chain (0) or the
shared chain (1). `l₁`, `l₂`, `l₃`: the three chains' played rounds. -/
def treeThird (l₁ l₂ l₃ : List Played) : Fmt.TreeSource → Option (Place × Table)
  | .own n => ((tablesOf l₃)[n]?).bind id
  | .taken ch k =>
    if ch == 0 then ((tablesOf l₁)[k]?).bind id
    else if ch == 1 then ((tablesOf l₂)[k]?).bind id else none

/-- The challenges of a file's three chains, one for each declared round. The first chain's last
declared round is the sealing round, of which a view shows nothing: its challenge has to be the
empty one. -/
structure Draws where
  first : List Fmt.Drawn
  shared : List Fmt.Drawn
  second : List Fmt.Drawn

/-- A stored run's challenges, with the empty one for the first chain's sealing round. -/
def drawsOf (U : Views) : Draws :=
  ⟨U.1.rounds.map (·.drawn) ++ [⟨[], [], [], none⟩], U.2.1.rounds.map (·.drawn),
    U.2.2.rounds.map (·.drawn)⟩

/-- The same challenges. -/
def Draws.same (ρ ρ' : Draws) : Bool :=
  ρ.first == ρ'.first && ρ.shared == ρ'.shared && ρ.second == ρ'.second

/-- A challenge is one that the round's entry can draw. This is what `roundsFit` and `viewWordsBelowPrime`
(Johnson/Desc/Block.lean) ask of a round's challenge: the three counts; every position in the
entry's range; every matrix entry -1, 0 or 1; `drawsMarkedNonzeroHaveNonzeroWords`; every word of an element below the prime. And
it has no sealed digest, unless the round is a sealing round (`Fmt.kindOf` of its entry's name):
there a typed challenge shows one, and nothing is asked of it here. -/
def drawFit (d : Fmt.DeclaredRound) (R : Fmt.Drawn) : Bool :=
  R.elems.length == d.entry.drawE && R.poss.length == d.entry.poss &&
    R.trits.length == d.entry.trits && R.poss.all (· < 2 ^ d.entry.logN) &&
    R.trits.all (fun t => t == -1 || t == 0 || t == 1) && drawsMarkedNonzeroHaveNonzeroWords d ⟨[], R⟩ &&
    R.elems.all (fun x => x.1 < fieldPrimeWord && x.2.1 < fieldPrimeWord && x.2.2 < fieldPrimeWord) &&
    (R.digest.isNone || Fmt.kindOf d.entry.name == some .sealed)

/-- `drawFit` round by round; false if the two lists differ in length. -/
def drawsFit : List Fmt.DeclaredRound → List Fmt.Drawn → Bool
  | d :: ds, R :: Rs => drawFit d R && drawsFit ds Rs
  | [], [] => true
  | _, _ => false

/-- **The challenges are such as the description's rounds can draw.** A statement "at every list of
challenges" means: at every list of which this is true. The first chain's last round, its sealing
round, has the empty challenge, as `run` asks (`sealTest`): a view shows nothing of that round. -/
def Draws.due (F : FileDescription Xi) (ρ : Draws) : Bool :=
  drawsFit F.roundsDeclaredByBlocks.1 ρ.first && drawsFit F.roundsDeclaredByBlocks.2.1 ρ.shared && drawsFit F.roundsDeclaredByBlocks.2.2 ρ.second &&
    ρ.first.getLast? == some ⟨[], [], [], none⟩

/-- The first chain's last round, as played, sends nothing and has the empty challenge. -/
def sealQuiet (l : List Played) : Bool :=
  (l.getLast?.map fun p =>
    p.vals.isEmpty && p.tables.isEmpty && p.drawn == ⟨[], [], [], none⟩).getD false

/-- A run of a file's three chains: the played rounds, what was read, and the three views. -/
structure Run where
  played : List Played × List Played × List Played
  reads : List Read × List Read × List Read
  views : Views

/-- A run's rounds as a view shows them. -/
def roundsOf (l : List Played) : List Fmt.RoundView := l.map fun p => ⟨p.vals, p.drawn⟩

/-- How many columns a run reads of each stored table: the statement's item, the number. It counts
reads: a position that two rounds read counts twice. -/
def Run.storedRead (r : Run) : List (Nat × Nat) :=
  let l := (r.reads.1 ++ r.reads.2.1 ++ r.reads.2.2).filterMap (·.item)
  l.eraseDups.map fun i => (i, l.count i)

/-- **All that `run` prepares before it plays**: the two inputs, and the three chains' rounds, each
with its move and its coins supplied. No challenge is in it. -/
structure Ready (W₀ Rc Xi Ky Tr X₀ X : Type) where
  own : Local W₀ Rc Xi Tr
  common : Common W₀ Rc Ky
  first : List (Step (Local W₀ Rc Xi Tr) X)
  shared : List (Step (Common W₀ Rc Ky) X₀)
  second : List (Step (Local W₀ Rc Xi Tr) X)

/-- **The tests of a run that read neither a challenge nor the instance.** An error if a prover's
side is at no place of its chain, or two are at one place; if `FileDescription.placesOk` is false (a
sub-protocol names another chain than the one in whose list it is, or two are at one place, so that
one prover's side would be played at both); if the named element or w₀ is out of range; or if a test
on the book fails. -/
def readyTests (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) :
    Except Refusal Unit :=
  if !(strays F.first.blocksInOrder H.first ++ strays F.shared.blocksInOrder H.shared ++
      strays F.second.blocksInOrder H.second).isEmpty then
    .error ⟨.unfit, "a half stands at no place of its chain"⟩
  else if !(twice H.first ++ twice H.shared ++ twice H.second).isEmpty then
    .error ⟨.unfit, "two halves stand at one place"⟩
  else if !F.placesOk then
    .error ⟨.unfit, "the description fails its own test on the places"⟩
  else if !H.inRange H.dummy then
    .error ⟨.unfit, "the named member of the range is out of range"⟩
  else if !H.inRange w₀ then
    .error ⟨.noIndex, "what all requests share is out of range"⟩
  else
    match B.word F with
    | some e => .error ⟨.unfit, "the book: " ++ e⟩
    | none => .ok ()

/-- The shared chain's rounds, each with its move and its coins supplied, from its input and its own
parts' coins. No instance is among its arguments. -/
def sharedSteps (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (w' : Common W₀ Rc Ky) (c₀ : Purse B.shared) :
    Except Refusal (List (Step (Common W₀ Rc Ky) X₀)) :=
  unfit (chainSteps B (B.rowsOf 1) (sharedLook B c₀) (Face.shared.sees w') F.shared.blocksInOrder H.shared)

/-- **The shared chain prepared without an instance**: `readyTests` and `sharedSteps`, at a key that
the caller supplies. -/
def readyShared (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (ky : Ky) (c₀ : Purse B.shared) : Except Refusal (List (Step (Common W₀ Rc Ky) X₀)) :=
  (readyTests F B H w₀).bind fun _ => sharedSteps F B H ⟨w₀, rc, ky⟩ c₀

/-- **The first half of a run: all its tests that read no challenge, and the rounds prepared.**
`readyTests`; then the key and the request's trace are computed, by the prover's functions; then the
three chains' rounds, the shared chain's by `sharedSteps`. An error, besides those of `readyTests`
and `chainSteps`, if the request has no trace. -/
def ready (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) : Except Refusal (Ready W₀ Rc Xi Ky Tr X₀ X) :=
  (readyTests F B H w₀).bind fun _ =>
  match H.trace w₀ x with
  | none => .error ⟨.noTrace, "the request has no trace"⟩
  | some tr =>
  let w : Local W₀ Rc Xi Tr := ⟨w₀, rc, x, tr⟩
  let w' : Common W₀ Rc Ky := ⟨w₀, rc, H.key x⟩
  (unfit (chainSteps B (B.rowsOf 0) (c.look 0) (Face.own.sees w) F.first.blocksInOrder H.first)).bind
    fun m₁ =>
  (sharedSteps F B H w' c.shared).bind fun m₂ =>
  (unfit (chainSteps B (B.rowsOf 2) (c.look 2) (Face.own.sees w) F.second.blocksInOrder H.second)).map
    fun m₃ => ⟨w, w', m₁, m₂, m₃⟩

/-- The state of the shared chain's run at its start, at its input. No columns are handed. -/
def startShared (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w' : Common W₀ Rc Ky) :
    Mid (Common W₀ Rc Ky) X₀ := ⟨⟨w', [], H.ownShared₀⟩, [], [], none⟩

/-- The state of the first chain's run at its start. No columns are handed. -/
def Ready.start₁ (R : Ready W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    Mid (Local W₀ Rc Xi Tr) X := ⟨⟨R.own, [], H.own₀⟩, [], [], none⟩
/-- The shared chain's. -/
def Ready.start₂ (R : Ready W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X) :
    Mid (Common W₀ Rc Ky) X₀ := startShared H R.common

/-- The state of the second chain's run at its start, from the two earlier chains' ends. It goes on
from the first chain's end, has heard the shared chain's challenges and is shown its rounds too, and
takes `H.meet` of its end. Its stops read the first and the second chain's challenges alone. No
columns are handed: `opened` is `none`, whatever e₁ and e₂ hold; `ChainProgress.start` (Walk.lean) lays them.
-/
def Ready.start₃ (R : Ready W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (e₁ : Mid (Local W₀ Rc Xi Tr) X) (e₂ : Mid (Common W₀ Rc Ky) X₀) :
    Mid (Local W₀ Rc Xi Tr) X :=
  ⟨⟨R.own, e₁.st.heard ++ e₂.st.heard, H.meet e₁.st.own e₂.st⟩, e₁.loc, e₁.seen ++ e₂.seen, none⟩

/-- After the first chain's last round: an error if that round, the sealing round, sends or draws
something. `y`: played rounds, the sealing round last, and the state of the run after them. -/
def sealTest (y : List Played × Mid W X) : Except Refusal (List Played × Mid W X) :=
  if !sealQuiet y.1 then .error ⟨.unfit, "the sealing round sends or draws something"⟩ else .ok y

/-- **The first and the shared chain, played**: the first chain with its sealing round and the test
on it; then the shared chain. `run` and `midAt` both call it. `b₁`, `b₂`: a stored run's rounds to
fall back on. -/
def Ready.ends (R : Ready W₀ Rc Xi Ky Tr X₀ X) (H : Prover W₀ Rc Xi Ky Tr X₀ X)
    (ρ₁ ρ₂ : List Fmt.Drawn) (b₁ b₂ : List Fmt.RoundView) :
    Except Refusal ((List Played × Mid (Local W₀ Rc Xi Tr) X) ×
      (List Played × Mid (Common W₀ Rc Ky) X₀)) :=
  ((play R.first ρ₁ b₁ (R.start₁ H)).bind sealTest).bind fun r₁ =>
  (play R.shared ρ₂ b₂ (R.start₂ H)).map fun r₂ => (r₁, r₂)

/-- **An honest run**, at what all requests share, the stored tables' pads and encoding randomness,
the public instance, the run's coins and the challenges: `ready`, and then the playing. The stored
tables' columns are computed here, by the prover's function. The chains are played in the order in
which `runCore` folds them. The shared chain starts from a state of its own, whose input is (w₀, rc,
the key), is given its own parts' coins alone, and hears its own challenges alone. The second chain
may be given coins of all three chains. The first view is without its sealing round, which `runCore`
puts back (`withEmptySealRound`). An error, besides those of `ready`, `play` and `fillCols`: if there is a
stored run and the challenges are not its own (tested after all of `ready`'s tests); if the sealing
round sends or draws something (`sealTest`). -/
def run (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) (ρ : Draws) (back : Option Views) : Except Refusal Run :=
  let b₁ := (back.map (·.1)).getD ⟨[], []⟩
  let b₂ := (back.map (·.2.1)).getD ⟨[], []⟩
  let b₃ := (back.map (·.2.2)).getD ⟨[], []⟩
  let stored := H.storedWords w₀ rc
  (ready F B H w₀ rc x c).bind fun R =>
  if !((back.map fun U => ρ.same (drawsOf U)).getD true) then
    .error ⟨.unfit, "the challenges are not the stored run's"⟩
  else
  (R.ends H ρ.first ρ.shared b₁.rounds b₂.rounds).bind fun (r₁, r₂) =>
  (play R.second ρ.second b₃.rounds (R.start₃ H r₁.2 r₂.2)).bind fun r₃ =>
    let q₁ := readsOf 0 0 stored (treeOwn r₁.1) F.roundsDeclaredByBlocks.1 ρ.first
    let q₂ := readsOf 1 0 stored (treeOwn r₂.1) F.roundsDeclaredByBlocks.2.1 ρ.shared
    let q₃ := readsOf 2 F.lastChainFirstTreeNumber stored (treeThird r₁.1 r₂.1 r₃.1) F.roundsDeclaredByBlocks.2.2 ρ.second
    (unfit (fillCols q₁ b₁.opened)).bind fun c₁ =>
    (unfit (fillCols q₂ b₂.opened)).bind fun c₂ =>
    (unfit (fillCols q₃ b₃.opened)).map fun c₃ =>
      ⟨(r₁.1, r₂.1, r₃.1), (q₁, q₂, q₃),
        (⟨(roundsOf r₁.1).dropLast, c₁⟩, ⟨roundsOf r₂.1, c₂⟩, ⟨roundsOf r₃.1, c₃⟩)⟩

/-- **The state of a run before the part at an address of the first or the second chain**: `ready`,
and the rounds before the address played, as `run` plays them: for an address of the second chain by
the same `Ready.ends`. -/
def midAt (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) (ρ : Draws) (a : Addr) : Except Refusal (Mid (Local W₀ Rc Xi Tr) X) :=
  (ready F B H w₀ rc x c).bind fun R =>
  if R.first.any (·.addr == a) then midIn R.first ρ.first [] (R.start₁ H) a
  else
    (R.ends H ρ.first ρ.shared [] []).bind fun (r₁, r₂) =>
    midIn R.second ρ.second [] (R.start₃ H r₁.2 r₂.2) a

/-- The same at an address of the shared chain. -/
def midSharedAt (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) (a : Addr) : Except Refusal (Mid (Common W₀ Rc Ky) X₀) :=
  (ready F B H w₀ rc x c).bind fun R => midIn R.shared ρ.shared [] (R.start₂ H) a

/-- **The blocks that the part at an address is given as carried**, from a run's coins: by
`lendPart`, as `chainSteps` lends them. `chain`: the part's chain, from 0. `p`: the part at the
address, on the caller's word: nothing here compares `chain` or `p` with a prover's sides. -/
def carriedAt (B : ProverCoinCounts) (c : Coins B) (chain : Nat) (a : Addr) (p : Part V W X) :
    Except String (CsAll p.carries) :=
  (lendPart B (B.rowsOf chain) (c.look chain) a p).map (·.2.2)

/-! ## 7 The test -/

/-- An error of the honest side, in words, for the tests. -/
def Refusal.print (e : Refusal) : String :=
  match e.why with
  | .unfit => "the honest side: " ++ e.words
  | .noIndex => "the honest side: " ++ e.words
  | .noTrace => "the honest side: " ++ e.words
  | .bad => "the honest side stops (Bad): " ++ e.words
  | .hid => "the honest side stops (Hid): " ++ e.words

/-- **The test, in words**: "yes", or "no: " and the description's reason, or the honest side's own
error. With `back := some U` a yes shows nothing about what was taken from U. -/
def say (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) (ρ : Draws) (back : Option Views) : String :=
  match run F B H w₀ rc x c ρ back with
  | .ok r => F.say x r.views.1 r.views.2.1 r.views.2.2
  | .error e => e.print

/-- **A run's outcome, as a statement may read it**: the three views, with no stored run to fall
back on; or `none`: an error's class and words are forgotten here. -/
def outcome (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) : Option Views :=
  (run F B H w₀ rc x c ρ none).toOption.map (·.views)

/-- The class of a run's error, if there is one. Whether a stop fires is computed without the run's
coins, by the types of `Part.bad` and `Part.hid`; a fault may depend on them, and an earlier fault
takes the place of a later stop. -/
def stopOf (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) : Option Why :=
  match run F B H w₀ rc x c ρ none with
  | .ok _ => none
  | .error e => some e.why

/-- **Whether a second stop ends the run**, at one list of challenges. It is asked at coins too,
since a fault, which may depend on the coins, can come first (see `stopOf`): so it is no name for a
set of lists of challenges. That name is `silentAt` (Honest/Rule.lean), which is computed from the
stops alone, has no coin among its arguments, and still names the stop where a fault comes first.
This function serves the tests of Honest/FrameToy.lean. -/
def hidAt (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc)
    (x : Xi) (c : Coins B) (ρ : Draws) : Bool :=
  stopOf F B H w₀ rc x c ρ == some .hid

/-- The test as a proposition: the honest run's outcome is three views, and the description's
decision on them is yes. It is a definition for the tests of this folder. No theorem is stated of it
in this file, and it is none of the library's goals. -/
def Runs (F : FileDescription Xi) (B : ProverCoinCounts) (H : Prover W₀ Rc Xi Ky Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Xi)
    (c : Coins B) (ρ : Draws) : Prop :=
  ∃ U, outcome F B H w₀ rc x c ρ = some U ∧ F.run x U.1 U.2.1 U.2.2 = true

/-- Two views show the same. -/
def sameView (v v' : Fmt.View) : Bool :=
  v.rounds.map (fun r => (r.vals, r.drawn)) == v'.rounds.map (fun r => (r.vals, r.drawn)) &&
    v.opened == v'.opened

/-- Two outcomes are the same. -/
def sameOutcome : Option Views → Option Views → Bool
  | none, none => true
  | some a, some b => sameView a.1 b.1 && sameView a.2.1 b.2.1 && sameView a.2.2 b.2.2
  | _, _ => false

/-! ## 8 At the proof file's description

`onlineDescription` (Johnson/Desc/ProofFile/OnlineDescription.lean) is the proof file's description, computed from the
three public files policy.txt, layout.txt and KL.bin (the arguments `pol`, `lay`, `KL`). It is
assembled from lots: a `Lot` (LotCore.lean) is a named table of sub-protocols from one module. A
module defines a function from the public part (`Pub`, Pub.lean) to a `Lot`, and the lot's tables
are functions of the segments' data (`Ground`, Ground.lean). -/

/-- A lot's honest side: the prover's sides at the places of the lot of that name (`Lot`,
LotCore.lean), from the public part and the segments' data. The lots of `onlineFirstChainBlockTables Z` make the first
chain. -/
structure HLot (V W X : Type) where
  /-- the lot's name -/
  name : String
  halves : Pub → Ground → List (Placed V W X)

/-- The first chain's prover's sides, lot by lot. -/
def firstOf (Z : Pub) (Gr : Ground) (ls : List (HLot V W X)) : List (Placed V W X) :=
  ls.flatMap fun L => L.halves Z Gr

/-- The lots of `onlineFirstChainBlockTables Z` that have no honest side of their name. -/
def lotsLacking (Z : Pub) (ls : List (HLot V W X)) : List String :=
  ((onlineFirstChainBlockTables Z).filter fun L => !(ls.any fun h => h.name == L.name)).map (·.name)

/-- The sub-protocols whose rounds send something and at whose place no prover's side is defined. -/
def lacking (bs : List (Block S Cl)) (hs : List (Placed V W X)) : List String :=
  (bs.filter fun b => b.rounds.any (fun r => r.entry.msg != 0) &&
    !(hs.any fun h => h.place == b.place)).map (·.name)

/-- The key at `onlineDescription`: the table's key in the instance's public part. It has three fields: the
number of the statement's item that holds the table's root, the out-of-domain seeds, and the answers
(`OnBytes.TableKey`, OnBytes/Iop/Foldeq.lean). The root itself is not in it. -/
def pureKey (x : Inst) : OnBytes.TableKey := x.pub.key

/-- **The test at `onlineDescription`**: at the three public files, a book, a prover, what all requests
share, the stored tables' pads and encoding randomness, an instance, coins and challenges. `o`
stands for the hash that the format page calls the earlier hash (the format uses it beside its hash
H; `OnBytes.secondHashFunction`), as in `onlineDescription`. The key is supplied here, by `pureKey`; H's own field `key`
is not read. With `back := some U` a yes shows nothing about what was taken from U. -/
def pureSay (o : SecondHashFunctionArgument) (pol lay KL : ByteArray) (B : ProverCoinCounts)
    (H : Prover W₀ Rc Inst OnBytes.TableKey Tr X₀ X) (w₀ : W₀) (rc : Rc) (x : Inst) (c : Coins B)
    (ρ : Draws) (back : Option Views) : String :=
  match onlineDescription o pol lay KL with
  | .ok F => say F B { H with key := pureKey } w₀ rc x c ρ back
  | .error e => "no description: " ++ e

end ProofFile.Honest

#print axioms ProofFile.Honest.Seen.plus_nil
#print axioms ProofFile.Honest.Seen.plus_plus
#print axioms ProofFile.Honest.Seen.front_plus
#print axioms ProofFile.Honest.Said
#print axioms ProofFile.Honest.Said.got
#print axioms ProofFile.Honest.Table
#print axioms ProofFile.Honest.Table.col
#print axioms ProofFile.Honest.Sending
#print axioms ProofFile.Honest.Sending.fits
#print axioms ProofFile.Honest.Due
#print axioms ProofFile.Honest.Cs
#print axioms ProofFile.Honest.Cs.empty
#print axioms ProofFile.Honest.Cs.fAt
#print axioms ProofFile.Honest.Cs.eAt
#print axioms ProofFile.Honest.Cs.cut
#print axioms ProofFile.Honest.CsAll
#print axioms ProofFile.Honest.Due.plus
#print axioms ProofFile.Honest.Cs.split
#print axioms ProofFile.Honest.CsAll.split
#print axioms ProofFile.Honest.CsAll.any
#print axioms ProofFile.Honest.CsAll.fin
#print axioms ProofFile.Honest.Addr
#print axioms ProofFile.Honest.Purse
#print axioms ProofFile.Honest.Purse.find?
#print axioms ProofFile.Honest.Purse.any
#print axioms ProofFile.Honest.Purse.fin
#print axioms ProofFile.Honest.Ahead
#print axioms ProofFile.Honest.Ahead.named
#print axioms ProofFile.Honest.ProverCoinCounts
#print axioms ProofFile.Honest.Coins
#print axioms ProofFile.Honest.dueAt
#print axioms ProofFile.Honest.placeDue
#print axioms ProofFile.Honest.ProverCoinCounts.rowsOf
#print axioms ProofFile.Honest.sharedLook
#print axioms ProofFile.Honest.Coins.look
#print axioms ProofFile.Honest.orderOf
#print axioms ProofFile.Honest.Addr.before
#print axioms ProofFile.Honest.ProverCoinCounts.spentBy
#print axioms ProofFile.Honest.ProverCoinCounts.knownBy
#print axioms ProofFile.Honest.cutAll
#print axioms ProofFile.Honest.maskWords
#print axioms ProofFile.Honest.masksOk
#print axioms ProofFile.Honest.meets
#print axioms ProofFile.Honest.Ahead.shares
#print axioms ProofFile.Honest.ProverCoinCounts.clauses
#print axioms ProofFile.Honest.ProverCoinCounts.word
#print axioms ProofFile.Honest.Seen
#print axioms ProofFile.Honest.Seen.lately
#print axioms ProofFile.Honest.Seen.bare
#print axioms ProofFile.Honest.Seen.front
#print axioms ProofFile.Honest.Seen.plus
#print axioms ProofFile.Honest.State
#print axioms ProofFile.Honest.State.hears
#print axioms ProofFile.Honest.State.lately
#print axioms ProofFile.Honest.State.narrow
#print axioms ProofFile.Honest.Move
#print axioms ProofFile.Honest.Move.lift
#print axioms ProofFile.Honest.Move.recoin
#print axioms ProofFile.Honest.Handed
#print axioms ProofFile.Honest.handFst
#print axioms ProofFile.Honest.handSnd
#print axioms ProofFile.Honest.Odds
#print axioms ProofFile.Honest.Odds.plus
#print axioms ProofFile.Honest.Part
#print axioms ProofFile.Honest.Part.Coins
#print axioms ProofFile.Honest.Part.plain
#print axioms ProofFile.Honest.Part.lift
#print axioms ProofFile.Honest.stopBoth
#print axioms ProofFile.Honest.Part.andThen
#print axioms ProofFile.Honest.Placed
#print axioms ProofFile.Honest.Placed.rounds
#print axioms ProofFile.Honest.statedShares
#print axioms ProofFile.Honest.RowCoins
#print axioms ProofFile.Honest.KindHalf
#print axioms ProofFile.Honest.Shown
#print axioms ProofFile.Honest.Before
#print axioms ProofFile.Honest.Before.seen
#print axioms ProofFile.Honest.Sim
#print axioms ProofFile.Honest.KindSim
#print axioms ProofFile.Honest.Common
#print axioms ProofFile.Honest.Local
#print axioms ProofFile.Honest.Face
#print axioms ProofFile.Honest.Face.pub
#print axioms ProofFile.Honest.Face.sees
#print axioms ProofFile.Honest.Prover
#print axioms ProofFile.Honest.Prover.storedWords
#print axioms ProofFile.Honest.Why
#print axioms ProofFile.Honest.Refusal
#print axioms ProofFile.Honest.unfit
#print axioms ProofFile.Honest.Step
#print axioms ProofFile.Honest.Step.stop
#print axioms ProofFile.Honest.strays
#print axioms ProofFile.Honest.twice
#print axioms ProofFile.Honest.lend
#print axioms ProofFile.Honest.lendPart
#print axioms ProofFile.Honest.lendRow
#print axioms ProofFile.Honest.Part.steps
#print axioms ProofFile.Honest.rowSteps
#print axioms ProofFile.Honest.Placed.steps
#print axioms ProofFile.Honest.chainSteps
#print axioms ProofFile.Honest.Played
#print axioms ProofFile.Honest.Mid
#print axioms ProofFile.Honest.Mid.bare
#print axioms ProofFile.Honest.Mid.shown
#print axioms ProofFile.Honest.Mid.took
#print axioms ProofFile.Honest.Told
#print axioms ProofFile.Honest.Step.tell
#print axioms ProofFile.Honest.Step.hear
#print axioms ProofFile.Honest.play
#print axioms ProofFile.Honest.midIn
#print axioms ProofFile.Honest.Read
#print axioms ProofFile.Honest.srcOf
#print axioms ProofFile.Honest.readsOf
#print axioms ProofFile.Honest.fillCols
#print axioms ProofFile.Honest.tablesOf
#print axioms ProofFile.Honest.treeOwn
#print axioms ProofFile.Honest.treeThird
#print axioms ProofFile.Honest.Draws
#print axioms ProofFile.Honest.drawsOf
#print axioms ProofFile.Honest.Draws.same
#print axioms ProofFile.Honest.drawFit
#print axioms ProofFile.Honest.drawsFit
#print axioms ProofFile.Honest.Draws.due
#print axioms ProofFile.Honest.sealQuiet
#print axioms ProofFile.Honest.Run
#print axioms ProofFile.Honest.roundsOf
#print axioms ProofFile.Honest.Run.storedRead
#print axioms ProofFile.Honest.Ready
#print axioms ProofFile.Honest.readyTests
#print axioms ProofFile.Honest.sharedSteps
#print axioms ProofFile.Honest.readyShared
#print axioms ProofFile.Honest.ready
#print axioms ProofFile.Honest.startShared
#print axioms ProofFile.Honest.Ready.start₁
#print axioms ProofFile.Honest.Ready.start₂
#print axioms ProofFile.Honest.Ready.start₃
#print axioms ProofFile.Honest.sealTest
#print axioms ProofFile.Honest.Ready.ends
#print axioms ProofFile.Honest.run
#print axioms ProofFile.Honest.midAt
#print axioms ProofFile.Honest.midSharedAt
#print axioms ProofFile.Honest.carriedAt
#print axioms ProofFile.Honest.Refusal.print
#print axioms ProofFile.Honest.say
#print axioms ProofFile.Honest.outcome
#print axioms ProofFile.Honest.stopOf
#print axioms ProofFile.Honest.hidAt
#print axioms ProofFile.Honest.Runs
#print axioms ProofFile.Honest.sameView
#print axioms ProofFile.Honest.sameOutcome
#print axioms ProofFile.Honest.HLot
#print axioms ProofFile.Honest.firstOf
#print axioms ProofFile.Honest.lotsLacking
#print axioms ProofFile.Honest.lacking
#print axioms ProofFile.Honest.pureKey
#print axioms ProofFile.Honest.pureSay
#print axioms ProofFile.Honest.instInhabitedCs
#print axioms ProofFile.Honest.instFintypeCs
#print axioms ProofFile.Honest.instInhabitedCsAll
#print axioms ProofFile.Honest.instFintypeCsAll
#print axioms ProofFile.Honest.instInhabitedPurse
#print axioms ProofFile.Honest.instFintypePurse
#print axioms ProofFile.Honest.instInhabitedCoins
#print axioms ProofFile.Honest.instFintypeCoins
