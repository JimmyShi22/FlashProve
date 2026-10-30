-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Shared/Dec.lean: the decision at one proximity test, as a function of data. Definitions
with code; no theorem.

A chain's decision that is written as a fold over data comes to a proximity test with a carried
statement and book of trees, the plan's entries, and the view's rounds and opened columns. Here the
test is decided by the verifier program's own routine (`ioppVerify`, OnBytes/Iop/Prox.lean), called
once at a context that is built from these data and dropped behind the call.

Main definitions.
  `TestIn`: what is given: eight fields of the routine's context and the routine's four arguments.
  `TestIn.ctx`: the context. It is no dry run; no message is open; no named test has failed; every
    field that `TestIn` does not name stands at its record's default.
  `TestIn.front`: the group's open rows, and the context with these rows taken out.
  `TestIn.sched`: a test on the carried statement and book. It reads numbers, shapes, kinds, flags,
    counters and pads: no value that a prover has sent or that was drawn.
  `TestIn.run`: the decision. In this order: the codes' message lengths are powers of two; `sched`;
    the group's open rows are laid again, one by one, through the program's own `Blk.addRow`, so
    that its tests on a row are asked here whoever made the rows; one call of the routine; no named
    test has failed; every entry and every round that was given is used up, and no message is open.
  `TestOut`: what goes on behind a yes: the roots received, the opened columns that are left, the
    statement and the book.

A check that marks and goes on. The routine's two named tests at its last stage (the linear claim;
the symbols at the positions) write a failure into the context and go on. `run` reads that mark
behind the call and refuses under the test's name. No such mark is carried on, and `ctx` lays none
in front: so every step in front of a test has to refuse at once as well.

What `sched` adds. Seven of its clauses the routine or `Blk.addRow` asks anyway. Five are asked by
nothing else at a test: the members' numbers rise; each member is sampled; it knows the group; it
has as many sample rows as its shape has answers; its pad is `Send.pad` at the statement's codes and
its shape, which is what `Send.admit` lays. `Blk.addRow` tests that no row reads an entry of a pad,
but against the carried pad, whose default is empty. Evaluated at one stored accepted proof with one
field turned, the decision without the line `sched` said yes at a member marked as not sampled, at a
member that knows no group, and at a pad that was emptied or moved by one index. By reading, not by
a theorem: at a state that the program's own calls have made from a lawful start these five hold by
`Blk.join`, `Send.admit` and `Blk.sampledElsewhere`.

What is not asked here; it is the caller's.
  That `samples`, `firstTree`, `entries`, `g`, `stages`, `choice` and `mask` are a plan's. The
    numbers of positions that a test draws are the entries'. A wrong `firstTree` is not always
    refused.
  That the entries and rounds given are the test's own part of the chain's lists, and that the
    parts, in order, are the whole lists. `run` refuses unless all that is given is used up; it does
    not see what stands in front or behind.
  That the statement and the book are what the chain's earlier steps have made, and that they, the
    roots and the opened columns go unturned from one `TestOut` to the next `TestIn`. Above all: the
    members' sample rows are taken as they are carried; nothing here holds them against the seeds
    drawn and the answers received.
  That every step in front has ended with no message open and no named test failed: `ctx` lays both.
  At the chain's end: that every group is tested and no opened column is left. The columns that the
    test does not read are handed on.
  That an opened column hangs under its root, that the drawn values are a hash's, and that the
    view's words are below the prime: a view holds no root. Which root a tree has that was taken
    over from another chain is not seen either: on a view the routine does not read `Tree.src`.
  That a written description of the test's rounds (names, kinds, items, roots, openings) is the
    course that the routine takes at `ctx`. On a view a round's kind is not read, and roots are only
    counted.
  `front` asks membership as of now: a row that names a message which joined the group after the row
    was laid passes here; the program refuses it at the laying.

Not claimed. What the routine's yes means for the typed protocol. Nothing on soundness, on an honest
prover or on hiding.

What this comment says of the decision rests on reading and on runs; it is not machine-checked.


-/
import OnBytes.Iop.Lin

set_option autoImplicit false
namespace H2U
open OnBytes OnBytes.Params

/-- What a proximity test's routine is given: its four arguments, and those fields of its context
that `TestIn.ctx` does not lay at a constant or a default. -/
structure TestIn where
  /-- the number of answers to a sample -/
  samples : Nat
  /-- the number of the chain's first own tree: 0 at a chain that continues none; else the number of
  all trees that it takes over -/
  firstTree : Nat
  /-- the plan's entries of the test's rounds: from its round "BAT" to its round "BASE" -/
  entries : List Fmt.Entry
  /-- how many roots have been received on this chain in front of the test: it numbers the trees
  that the test receives -/
  roots : Nat
  /-- the view's rounds of the test -/
  rounds : List Fmt.RoundView
  /-- all the view's opened columns that are not yet read, in the file's order -/
  opened : List (Nat × Nat × List UInt64)
  /-- the statement as it is carried -/
  st : Statement
  /-- the book of trees as it is carried -/
  book : TreeBook
  /-- the routine's four arguments: the group's number, the stages, the choice, and the number of
  the first fold's mask if it has come before the test -/
  g : Nat
  stages : List IoppStage
  choice : IoppChoice
  mask : Option Nat

/-- The context that is built from the data. -/
def TestIn.ctx (x : TestIn) : Ctx :=
  { ch := { dry := false, firstTree := x.firstTree, samples := x.samples, entries := x.entries,
            left := x.rounds, opened := x.opened, roots := x.roots },
    st := x.st, book := x.book }

/-- The group's open rows, and the context with them taken out. -/
def TestIn.front (x : TestIn) : Array Row × Ctx :=
  (((x.st.groups[x.g]?).map (·.rows)).getD #[],
   { x.ctx with
     st := { x.st with groups := x.st.groups.modify x.g fun G => { G with rows := #[] } } })

/-- What goes on behind a yes. -/
structure TestOut where
  roots : Nat
  opened : List (Nat × Nat × List UInt64)
  st : Statement
  book : TreeBook

/-- What is asked of the carried statement and book in front of one test. Every clause reads
numbers, shapes, kinds, flags, counters and pads alone. -/
def TestIn.sched (x : TestIn) : Bool :=
  match x.st.groups[x.g]? with
  | none => false
  | some G =>
    -- the test has not begun; the group has a member; as many kept marks as members; the members
    -- rise (so none stands twice)
    !G.inRun && !G.members.isEmpty && G.kept.size == G.members.size &&
    (List.range (G.members.size - 1)).all
      (fun i => decide (G.members.getD i 0 < G.members.getD (i + 1) 0)) &&
    -- every member is there, is sampled, knows the group, has as many sample rows as its shape has
    -- answers, and its pad is the public one
    G.members.all (fun o => match x.st.oracles[o]? with
      | none => false
      | some y => y.sampled && y.groups.contains x.g && y.sampleRows.size == y.shape.answers
        && (match Send.pad x.st.codes y.shape with
            | none => false
            | some l => y.pad == l.map fun p => (p.part, p.index))) &&
    -- no open row is of the kind that the test's beginning drops without a word
    G.rows.all (fun r => r.kind != .sample) &&
    -- the mask that is handed in is there, is no member, has no sample and is not spent
    (match x.mask with
      | none => true
      | some m => match x.st.oracles[m]? with
        | none => false
        | some y =>
          !y.sampled && y.shape.answers == 0 && !y.spentAsMask && !G.members.contains m) &&
    -- the statement has as many messages as the book has places; a tree of a member or of the mask
    -- that is opened at one list only has not been opened
    x.st.oracles.size == x.book.place.size &&
    (G.members.toList ++ x.mask.toList).all (fun o =>
      match (x.book.place[o]?).bind fun p => x.book.trees[p.1]? with
      | none => false
      | some t => !t.oneList || t.lists == 0)

/-- The name under which the decision refuses where `sched` says no. -/
def schedName : String := "sched"

/-- The decision at one proximity test. -/
def TestIn.run (x : TestIn) : Except String TestOut :=
  if !x.st.codes.lengthsOk then .error Blk.codesName else
  if !x.sched then .error schedName else
  match (do x.front.1.forM (Blk.addRow x.g); ioppVerify x.g x.stages x.choice x.mask : Blk Unit)
      x.front.2 with
  | .error e => .error e.name
  | .ok (_, c) =>
    match c.failed with
    | some n => .error n
    | none =>
      if !(c.ch.entries.isEmpty && c.ch.settled) then .error planName
      else if c.ch.cur.isNone && c.ch.left.isEmpty then
        .ok { roots := c.ch.roots, opened := c.ch.opened, st := c.st, book := c.book }
      else .error shapeName

end H2U
