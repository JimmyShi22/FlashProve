-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/BordersShared.lean: the table of joints of a proof file's shared chain: what the
state that each block hands to the next means, with every item sorted: shared, or a slot's own.
Definitions with code; nothing is proved. A skeleton (the comments on the two tests' rows say at which
state a row is read; a frame fact by name; o_sp's one word) (no item for a mask without a sample: K12's law is said to take
its first fold's mask as any word that is fixed before the fold's first draw: an item that nobody spends is a
debt for nothing: so the table has no letter for "the mask goes out ahead") (the own
items' letters take the oracles too, in the first chain's table's own form, so that `claimM` can be laid as
that table's `pile` as it is) (the items are the
conjuncts of the library's typed joints: see the items' source;
the pins' and the near words' meanings are letters in the first chain's table's own form; a test
`laysClearS`; the promise's "no collision" follows the open pins). It imports
Johnson/Desc/Msg.lean alone (no Mathlib): so a compiled run can evaluate the index, the open sets and
the tests on the table.

The form is that of Johnson/Desc/First/Borders.lean (the first chain's table), whose words are kept: a
border lies in front of each block of the chain's flat list and behind the last; the relation at a
border is computed: "every open item holds"; a block's row says which items it closes (`ins`), opens
(`outs`), reads and leaves (`ctx`), and whether its extractor lays anything.

What is new here: the sort. The shared chain is run once for the N slots of a batch, and a round is
paid once for all slots only where the relations read a statement through the chain's own record, the
stored table and the chain's own trees alone (Johnson/Desc/Sound/SharedOnce.lean, SpineOnce.lean). So
each item is shared (its meaning is a function of these three and the witness) or a slot's own (it may
read what was handed to the chain: the request's public part, the first chain's last record and
trees). The rule of the table, tested by `ownStill`: own items are opened or closed by one block alone,
"LIN point"; behind it they only ride.

The protocol, as OnBytes/Iop/Lin.lean's head and the kind's own page (K14.lean, a file of this project that is not in this library) tell
it. The stored table holds a matrix M. Each request has one claim < g (x) eq(psi, .), M > (+ masks) =
target, with public g and psi. On its own first chain it has sent W, said to be g's combination of M's
rows, with the row (Eval) on W. Here, once for all requests: psi_sh = (psi_lo, gamma) is drawn; o_u is
sent, said to hold u, the fold of the table's rows at gamma; the record's answers are held against it
((rec_gamma)); the table's columns at drawn locations are held against it ((loc_x)); o_omega is sent,
said to hold Omega = M eq(psi_sh, .); z_fd is drawn, and (fold) ties Omega to u there; (fold) is split
over the two groups; each group has its proximity test. On its own last chain each request then tests
the row (Dot): W at psi_sh is < g, Omega >.

The items' source. The library has this test on typed rounds, proved for a batch (Cb/Ld/LdLin.lean: the
joints j1 … j6; Cb/Ld/LdLinBProofs.lean: linkPt, linkU, linkLoc, linkO, linkZeta). Each joint's relation
is a conjunction. The items here are these conjuncts, sorted: shared: NearW (`nearU`), RecRow (`recRow`),
ColT (`row .loc`), FoldR (`row .fold`), DecTo of G_u's and Omega's families (`pin`). Own: Cl (`claimM`), Ev
(`ev`), Dot (`dot`), DecTo of W's family (`pinV`), the relation on the slot's other oracles (`pinI`). So a
kind's files can carry a link to their block and reach this table's own term. One departure: in the
typed joints the slot's row is DotU (at u) from the point to zeta and Dot (at Omega) behind it: an own
conjunct is exchanged at zeta. Here the own row is `dot`, at the witness's Omega, from the point on, with
the shared item `omU` beside it ("Omega is what u gives at psi_lo"): DotU is `dot` with `omU`. So own items
are touched by one block alone; zeta's law is "omU, from (fold) at z_fd", shared (that K14's files have that
law on the kind's own text is not established here). The fall-back, if that law does not stand: the typed
joints to the letter: zeta is then a second block that touches own items (DotU for Dot), paid once by
the carriage of the library's linkZeta, and `ownStill` names two blocks.

1 the index: `sharedPlaces`, `placesFitS`.  2 the items: `Msg2`, `RowS`, `ItemS`, `ItemS.own`.
3 the rows: `RowOfS`, `rowS`.  4 the open sets and the tests on the table: `startS`, `stepOpenS`,
`openSetsS`, `readsOpenS`, `ownStill`, `freshOuts`, `endS`, `endFits`, `pointAt`, `Comp`, `ItemS.reads`,
`laysOfS`, `laysClearS`.
5 the numbers: `NumbersS`.  6 the meaning: `MeaningS`, `ItemS.holdsSh`, `ItemS.holdsOwn`.
7 the promise: `PromS`, `promsAt`, `PromMeaning`.
The field `whose` of a row is a working note on the row's standing; it is read by no
theorem.

Whose the rows are. Read off the two texts named above and other notes
on K14's two joints, on the chains' ends and on K12.
No row is confirmed.

The joint with the first chain's table. (a) `claimM`: (Eval) on W gives the claim on M only if W is g's
combination of M's rows, and nothing says that before the shared point: the library keeps the claim open
through W's sending (j1) and opens Ev behind the point (j2). So here the claim on M is open at this
chain's start, and "LIN point" closes it and opens `ev`. The first chain's table leaves its
`pile` open through W's sending: its end (unmarked, pinW, pileOne, pinI, pinV) is meant to meet `startS`
item for item. Owed at the joint: that the pile at the last border is one claim. (b) `pinT`: "the witness's cells are what the stored table decodes to with the
record" comes out of the first chain reading the record in the public part (`pinW`); here it reads the
key in the shared chain's own record: one sentence at the joint only because the shared chain's first
record is made of that key: a lemma at the joint, owed. (c) The first chain's mark (`unmarked`) is a
slot's own: it rides here. (d) `pinV`, `pinI` must be the same terms on both sides: their meaning here is
the letter `pin₁`, which stands for the first chain's table's own `Meaning.pin`.

No mark of this chain's own. At the first chain a block can mark its record and say yes; so "no mark"
stands in every row there. The record that is meant here (St, Johnson/Desc/K14/Text.lean: the statement, the book
of trees, the roots received, the opened columns not yet read, the kind's named values) has no field for
a deferred mark, and K14's blocks refuse at once [by reading DescState.lean and K14Block.lean, not machine-checked; K14Block.lean is not in this library; how
K12's own record is entered and left at its two seats here: not read]. The one late test is the end's
(`nothingLeft`), the last block's own; what the last chain's start asks of this chain's end is that same
Bool. If a block here can defer a failure, this table is wrong: then a shared
item "no mark" goes into every row.

A row that is owed beside the table: `tablePromise` rides from border 0: so it stands in what the first
chain hands on, and in the first condition at the top. There it is granted, under the file's yes, at
tables that decode with the record, and by nothing else. Owed, with an owner: "the table decodes with the
record ⟹ it lies in the domain of which the fold's count speaks" (its name in the comments:
table_promise): one quantity by two roads.

Which top it is for. The own part of the relation changes at "LIN point": so the relation is not of the
form "Ra k and ONE Rc" for the whole chain; it fits the rule that takes any relations
with `EachPays` (FoldSlotsPays).

Limits. (1) A skeleton. (2) Most sorts of item have a letter for a meaning. (3) The tests on the table
test the table's own word. (4) That the real shared chain's flat list has these places is a test
(`placesFitS`), not run here at that chain. (5) The shape without a split (one group, one test) is
laid by the letter `split`; both stored plans that were looked at split. (6) What is open at this
chain's end is closed by the last chain's rows, which this file does not hold.
(Where this and lean/THEOREM.md differ, the page
holds.) (7) The two tests are one block each
here: if K12's files cut them finer, the rows inside are their own.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Shared
open VerifiableInference.Desc

/-! ## 1 The index -/

/-- The places of the shared chain's flat list. split: o_u and o_omega differ in code: two groups,
two tests, and the round "SPLIT". -/
def sharedPlaces (split : Bool) : List Place :=
  [⟨2, none, 0, .frame⟩, ⟨2, none, 1, .K14⟩, ⟨2, none, 2, .K1⟩, ⟨2, none, 3, .K14⟩,
   ⟨2, none, 4, .K14⟩, ⟨2, none, 5, .K1⟩, ⟨2, none, 6, .K14⟩, ⟨2, none, 7, .K14⟩,
   ⟨2, none, 8, .K14⟩, ⟨2, none, 9, .K12⟩] ++
    (if split then [⟨2, none, 10, .K12⟩] else []) ++ [⟨2, none, 11, .frame⟩]

/-- A chain's flat list has just these places, in this order. -/
def placesFitS {S Cl : Type} (c : Chain S Cl) (ps : List Place) : Bool :=
  c.blocksInOrder.map (·.place) == ps

/-! ## 2 The items -/

/-- The shared chain's own messages. -/
inductive Msg2 where
  /-- o_u: (u, r_u) -/
  | oU
  /-- o_omega -/
  | oOmega
  /-- o_sp: one mask row, in both groups -/
  | oSp
  deriving DecidableEq, Repr

/-- The classes of open rows on the two groups. -/
inductive RowS where
  /-- a message's own sample's rows -/
  | sample (m : Msg2)
  /-- (rec_gamma), once for each answer of the record -/
  | recG
  /-- (loc_x), once for each location drawn -/
  | loc
  /-- (fold), whole -/
  | fold
  /-- (fold_u): its part on G_u, with the mask entry kappa and the scalar mu -/
  | foldU
  /-- (fold_omega): its part on G_omega -/
  | foldOmega
  deriving DecidableEq, Repr

/-- **An item**: a named claim on the witness. -/
inductive ItemS where
  /-- OWN. The slot's one claim on M holds of the witness's cells: < g (x) eq(psi, .), M > (+ mask
  entries of the slot's own messages) = target (the library's Cl; the first chain's pile in its last
  form) -/
  | claimM
  /-- OWN. The row (Eval) on W holds (the library's Ev; the first chain's `wrow`) -/
  | ev
  /-- OWN. The row (Dot): W at psi_sh is < g, Omega >, Omega the witness's message of o_omega. It
  reads the shared record's psi_sh and one shared component of the witness -/
  | dot
  /-- OWN. W's pin (the first chain's `pinV`) -/
  | pinV
  /-- OWN. The index masks' pin (the first chain's `pinI`) -/
  | pinI
  /-- OWN. The first chain's record bears no mark (the first chain's `unmarked`) -/
  | unmarked1
  /-- SHARED. The witness's cells are what the stored table decodes to with the record whose key lies
  in the shared chain's own record -/
  | pinT
  /-- SHARED. The code word of the witness's u is near the fold, at gamma, of the stored table's rows
  (the library's NearW) -/
  | nearU
  /-- SHARED. u's answers at the record's seeds are the fold, at gamma, of the record's answers (the
  library's RecRow) -/
  | recRow
  /-- SHARED. The witness's message of o_omega is, entry by entry, what u gives at psi_lo -/
  | omU
  /-- SHARED. The witness's message of a sampled message is what its committed word decodes to with
  its sample -/
  | pin (m : Msg2)
  /-- SHARED. Every open row of this class, AS IT LIES IN THE RECORD AT THE BORDER AT WHICH THE ITEM IS READ, holds of
  the witness's messages. A test closes its group's rows: so it owes them AT THE RECORD IN FRONT OF ITS BLOCK, where
  they lie open: the rows that its run takes in. (Behind the run's beginning the group's list of open rows is
  empty: read there the item would hold for nothing.) -/
  | row (cls : RowS)
  deriving DecidableEq, Repr

/-- **The sort.** -/
def ItemS.own : ItemS → Bool
  | .claimM | .ev | .dot | .pinV | .pinI | .unmarked1 => true
  | _ => false

/-! ## 3 The rows -/

/-- **A block's row.** -/
structure RowOfS where
  ins : List ItemS := []
  outs : List ItemS := []
  ctx : List ItemS := []
  /-- its extractor lays components of the witness (else it is the identity) -/
  lays : Bool := false
  known : Bool := true
  whose : String := "the frame's"
  deriving Repr

/-- **The table**, by the block's number at the chain's end (`Place.piece`). -/
def rowS (split : Bool) (p : Place) : RowOfS :=
  match p.piece with
  | 0 => {}
  | 1 =>
    -- THE ONE BLOCK AT WHICH A SLOT's OWN ENTERS. Its error has two parts (the library's errPtB): the
    -- gammas that are bad for the fold of the table (a function of the table and its record: ONCE) and
    -- the slot's own polynomial identity in psi_sh (N TIMES). The last reader of the cells: its
    -- extractor lays them (what the table decodes to with the record)
    { ins := [.claimM, .pinT], outs := [.ev, .dot, .omU, .nearU, .recRow], ctx := [.pinV, .pinI]
      lays := true, whose := "K14's house (the hash build) TO CONFIRM; the library's linkPt" }
  | 2 =>
    { outs := [.pin .oU, .row (.sample .oU)]
      whose := "K1's house TO CONFIRM" }
  | 3 =>
    -- no round, no chance: the rows that it lays say RecRow
    { ins := [.recRow], outs := [.row .recG], ctx := [.pin .oU], whose := "K14's house TO CONFIRM" }
  | 4 =>
    -- the rows' targets are the folds of the columns handed: the library's ColT is read off the ledger
    { ins := [.nearU], outs := [.row .loc], ctx := [.pin .oU]
      whose := "K14's house TO CONFIRM; the library's linkLoc" }
  | 5 =>
    { outs := [.pin .oOmega, .row (.sample .oOmega)] ++
        (if split then [.pin .oSp, .row (.sample .oSp)] else [])
      whose := "K1's house TO CONFIRM" }
  | 6 => { whose := "K14's house TO CONFIRM" }
  | 7 =>
    { ins := [.omU], outs := [.row .fold], ctx := [.pin .oU, .pin .oOmega]
      whose := "K14's house TO CONFIRM" }
  | 8 =>
    if split then
      { ins := [.row .fold], outs := [.row .foldU, .row .foldOmega], ctx := [.pin .oSp]
        whose := "K14's house TO CONFIRM" }
    else { whose := "K14's house TO CONFIRM" }
  | 9 =>
    -- the test on G_u. Without a split it is the one test: o_omega is a member, and ITS PIN STAYS: each
    -- slot's own last test reads it again. A FRAME FACT OF THIS ROW, BY NAME: G_omega's open rows, and the sample
    -- rows of o_omega and o_sp, lie untouched in the record across the WHOLE of this test (they ride: `row
    -- .foldOmega`, `row (.sample …)`). O_SP IS A MEMBER OF BOTH GROUPS: "both tests bind its mask table to ONE word"
    -- is `pin .oSp`: one component of the witness, pinned by its one sample: context here, closed by the second test
    { ins := [.row (.sample .oU), .row .recG, .row .loc, .pin .oU] ++
        (if split then [.row .foldU] else [.row .fold, .row (.sample .oOmega)])
      ctx := if split then [.pin .oSp] else [.pin .oOmega]
      lays := true, whose := "K12's house (H2) TO CONFIRM" }
  | 10 =>
    -- the test on G_omega: O_OMEGA's PIN IS CONTEXT: the extractor lays nothing of it: the own item
    -- `dot` reads that component
    { ins := [.row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega, .pin .oSp]
      ctx := [.pin .oOmega], lays := true, whose := "K12's house (H2) TO CONFIRM" }
  | 11 => { whose := "the chains' ends' pen (the hash build) TO CONFIRM" }
  | _ => { known := false }

/-! ## 4 The open sets, and tests on the table -/

/-- What is open at the chain's start: what the first chain is to leave (the head's (a), (b)). -/
def startS : List ItemS := [.unmarked1, .pinI, .pinV, .claimM, .pinT]

/-- The open set behind a block. -/
def stepOpenS (O : List ItemS) (r : RowOfS) : List ItemS :=
  let rest := O.filter fun i => !r.ins.contains i
  rest ++ r.outs.filter fun i => !rest.contains i

/-- The open sets at all borders: one more than there are blocks. -/
def openSetsS (split : Bool) : List Place → List ItemS → List (List ItemS)
  | [], O => [O]
  | p :: ps, O => O :: openSetsS split ps (stepOpenS O (rowS split p))

/-- A TEST: every item that a block closes or reads is open in front of it. -/
def readsOpenS (split : Bool) : List Place → List ItemS → Bool
  | [], _ => true
  | p :: ps, O =>
    ((rowS split p).ins ++ (rowS split p).ctx).all O.contains &&
      readsOpenS split ps (stepOpenS O (rowS split p))

/-- A TEST: no block opens an item that is open already. -/
def freshOuts (split : Bool) : List Place → List ItemS → Bool
  | [], _ => true
  | p :: ps, O =>
    ((rowS split p).outs.all fun i => !O.contains i) &&
      freshOuts split ps (stepOpenS O (rowS split p))

/-- The number of the block "LIN point" in the flat list. -/
def pointAt : Nat := 1

/-- No block but the one with the number pt closes, opens or reads an own item. -/
def ownStillAt (pt : Nat) (split : Bool) (ps : List Place) : Bool :=
  ps.all fun p =>
    p.piece == pt ||
      ((rowS split p).ins ++ (rowS split p).outs ++ (rowS split p).ctx).all
        fun i => !i.own

/-- **THE RULE OF THE TABLE**: own items are opened or closed by "LIN point" alone; and no other block
has one as context. -/
def ownStill (split : Bool) (ps : List Place) : Bool := ownStillAt pointAt split ps

/-- What is meant to be open at the chain's end: the slot's own, and o_omega's pin. -/
def endS : List ItemS := [.unmarked1, .pinI, .pinV, .ev, .dot, .pin .oOmega]

/-- A TEST: just that is open at the end. -/
def endFits (split : Bool) : Bool :=
  match (openSetsS split (sharedPlaces split) startS).getLast? with
  | some O => O.all endS.contains && endS.all O.contains
  | none => false

/-- How many blocks have no row yet. -/
def notYetS (split : Bool) (ps : List Place) : Nat :=
  (ps.filter fun p => !(rowS split p).known).length

/-- The components of the witness. -/
inductive Comp where
  | cells
  | msg (m : Msg2)
  /-- the slot's W, and the index masks' message -/
  | w
  | index
  deriving DecidableEq, Repr

/-- Which components of the witness an item reads. Written by hand. (The index masks' component is
laid by no block of this chain: `pinI` rides.) -/
def ItemS.reads : ItemS → List Comp
  | .claimM => [.cells, .index]
  | .ev => [.w, .index]
  | .dot => [.w, .msg .oOmega]
  | .pinV => [.w]
  | .pinI => [.index]
  | .unmarked1 => []
  | .pinT => [.cells]
  | .nearU => [.msg .oU]
  | .recRow => [.msg .oU]
  | .omU => [.msg .oU, .msg .oOmega]
  | .pin m => [.msg m]
  | .row (.sample m) => [.msg m]
  | .row .recG => [.msg .oU]
  | .row .loc => [.msg .oU]
  | .row .fold => [.msg .oU, .msg .oOmega]
  | .row .foldU => [.msg .oU, .msg .oSp]
  | .row .foldOmega => [.msg .oOmega, .msg .oSp]

/-- Which components the extractor of the block at a place lays: the point the cells; the test on G_u
o_u's message; the test on G_omega o_sp's. NEVER OMEGA's: the own item `dot` reads it. -/
def laysOfS (split : Bool) (p : Place) : List Comp :=
  if !(rowS split p).lays then []
  else match p.piece with
    | 1 => [.cells]
    | 9 => [.msg .oU]
    | 10 => [.msg .oSp]
    | _ => []

/-- A TEST: no open item that a block does not close reads a component that the block's extractor
lays. It tests the table's own word. -/
def laysClearS (split : Bool) : List Place → List ItemS → Bool
  | [], _ => true
  | p :: ps, O =>
    ((O.filter fun i => !(rowS split p).ins.contains i).all fun i =>
      i.reads.all fun c => !(laysOfS split p).contains c) &&
      laysClearS split ps (stepOpenS O (rowS split p))

/-! ## 5 The plan's numbers, as letters -/

/-- A tenant: a tree's number THROUGH THE FILE, and the message's number in the tree. -/
structure NumbersS where
  /-- the number of the shared chain's first own tree -/
  lo : Nat
  tenant : Msg2 → Nat × Nat
  /-- the tenant of the slot's W, and of the index masks' message: trees of the first chain -/
  w : Nat × Nat
  index : Nat × Nat

/-- A TEST: the shared messages lie in the chain's own trees, the slot's own below them. -/
def NumbersS.sorted (N : NumbersS) : Bool :=
  ([Msg2.oU, .oOmega, .oSp].all fun m => decide (N.lo ≤ (N.tenant m).1)) &&
    decide (N.w.1 < N.lo) && decide (N.index.1 < N.lo)

/-! ## 6 The meaning -/

/-- **What an item says.** S₂: the shared chain's own record. P₁: what was handed to the chain (the
request's public part with the first chain's last record). ONE FIELD A SORT OF ITEM THAT IS STILL A
LETTER. THE SHARED FIELDS ARE NOT HANDED P₁: BY TYPE. -/
structure MeaningS (S₂ P₁ Wt : Type) where
  /-- SHARED: tenant t of tree j: the witness's message is what the committed word decodes to with the
  tenant's sample, as THE CHAIN's OWN RECORD holds it (the first chain's table's `Meaning.pin`, at this
  chain's record) -/
  pin : Nat → Nat → S₂ → Strs → Wt → Prop
  /-- SHARED: the witness's cells are what the stored table decodes to, with the record whose key lies
  in the chain's own record -/
  pinT : S₂ → Strs → Wt → Prop
  /-- OWN: the first chain's table's own `Meaning.pin`, AS IT IS -/
  pin₁ : Nat → Nat → P₁ → Strs → Wt → Prop
  /-- SHARED (K14's files): NearW: it reads the stored table -/
  nearU : S₂ → Strs → Wt → Prop
  /-- SHARED (K14's files): RecRow -/
  recRow : S₂ → Wt → Prop
  /-- SHARED (K14's files): Omega is what u gives at the record's psi_lo -/
  omU : S₂ → Wt → Prop
  /-- SHARED (K14's, K1's files): every open row of the class, as it lies in the record, holds -/
  row : RowS → S₂ → Wt → Prop
  /-- OWN (K13's | K14's files): the slot's claim on the cells -/
  claimM : P₁ → Strs → Wt → Prop
  /-- OWN (K14's files): (Dot), at the shared record's psi_sh -/
  dot : P₁ → S₂ → Strs → Wt → Prop
  /-- OWN (K14's files): (Eval) -/
  ev : P₁ → Strs → Wt → Prop
  /-- OWN: the first chain's last record bears no mark. AT P₁ := (the public part) × (the first chain's
  record) IT HAS ONE MEANING: that record's field for a failed test is empty: TO BE LAID SO, not as a
  letter, where that record's type is at hand -/
  unmarked1 : P₁ → Prop

section
variable {S₂ P₁ Wt : Type} (N : NumbersS) (Mg : MeaningS S₂ P₁ Wt)

/-- **What a SHARED item says**: of the chain's own record, the oracles and a witness. An own item:
true. y IS MEANT TO SHOW THE STORED TABLE AND THE CHAIN's OWN TREES ALONE
(Johnson/Desc/Sound/BordersSharedQ.lean hands it just these). -/
def ItemS.holdsSh (i : ItemS) (s : S₂) (y : Strs) (w : Wt) : Prop :=
  match i with
  | .pinT => Mg.pinT s y w
  | .nearU => Mg.nearU s y w
  | .recRow => Mg.recRow s w
  | .omU => Mg.omU s w
  | .pin m => Mg.pin (N.tenant m).1 (N.tenant m).2 s y w
  | .row c => Mg.row c s w
  | _ => True

/-- **What an OWN item says**: it may read what was handed to the chain. A shared item: true. -/
def ItemS.holdsOwn (i : ItemS) (p : P₁) (s : S₂) (y : Strs) (w : Wt) : Prop :=
  match i with
  | .claimM => Mg.claimM p y w
  | .ev => Mg.ev p y w
  | .dot => Mg.dot p s y w
  | .pinV => Mg.pin₁ N.w.1 N.w.2 p y w
  | .pinI => Mg.pin₁ N.index.1 N.index.2 p y w
  | .unmarked1 => Mg.unmarked1 p
  | _ => True

end

/-! ## 7 The promise -/

/-- The SHARED clauses of the promise at the shared chain's borders. What a slot is promised of its
own (no collision at W's sample; the first chain's book-keeping) is ONE condition beside them, which
every block of this chain carries for certain (Johnson/Desc/Sound/SharedOnce.lean: `PaysCarry`). -/
inductive PromS where
  /-- the stored table, with its record, lies in the domain of which the fold's count speaks (the
  library's on0): IT COMES FROM THE KEY FILE's ONE-TIME TEST -/
  | tablePromise
  /-- of a message whose pin is open: every leaf of its tree shows its symbol; no two members of its list answer the sample alike (as it is
  filled that says too that the record holds the sample). The Bool "the record holds its sample" is no part of this clause -/
  | noColl (m : Msg2)
  /-- the kind's book-keeping on the record (a Bool) -/
  | shape (piece : Nat)
  /-- every group is tested, every sampled message is in a tested group (the chain's end) -/
  | nothingLeft
  deriving DecidableEq, Repr

/-- **The promise at the border in front of the block number k** (behind the last: k = the number of
blocks). -/
def promsAt (split : Bool) (k : Nat) : List PromS :=
  [.tablePromise, .shape k] ++
    (((openSetsS split (sharedPlaces split) startS)[k]?.getD []).filterMap fun i =>
      match i with
      | .pin m => some (.noColl m)
      | _ => none) ++
    (if (sharedPlaces split).length ≤ k then [.nothingLeft] else [])

/-- What a clause says: of the chain's own record and the oracles. NOT HANDED P₁: BY TYPE. -/
structure PromMeaning (S₂ : Type) where
  tablePromise : S₂ → Strs → Prop
  /-- the first chain's table's `noColl`, `shown`, `held`, at this chain's record. `held` (a test with code: the record still holds the
  tenant's sample) STANDS IN NO CLAUSE OF THE PROMISE: no proof spends it, and `noColl` as it is
  filled says the fact as a proposition: it stays a field for a run's sheets. If a proof wants it, it comes back as that proof's own premise -/
  noColl : Nat → Nat → S₂ → Strs → Prop
  shown : Nat → Nat → Strs → Prop
  held : Nat → Nat → S₂ → Bool
  shape : Nat → S₂ → Bool
  nothingLeft : S₂ → Bool

section
variable {S₂ : Type} (N : NumbersS) (Pm : PromMeaning S₂)

def PromS.holds (c : PromS) (s : S₂) (y : Strs) : Prop :=
  match c with
  | .tablePromise => Pm.tablePromise s y
  | .noColl m =>
    Pm.shown (N.tenant m).1 (N.tenant m).2 y ∧ Pm.noColl (N.tenant m).1 (N.tenant m).2 s y
  | .shape k => Pm.shape k s = true
  | .nothingLeft => Pm.nothingLeft s = true

end

end VerifiableInference.Desc.Shared
