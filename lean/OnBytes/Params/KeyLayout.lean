-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Params/KeyLayout.lean: the layout of a key file as one value, computed from the three public
files.

A key file is, in this order (docs/format/FORMAT.md, R13.2): the head, the first table's root, the
answers of its record, the one-time chain, the place in the binding tree, the shared chain, the
second chain. No part has a word for its own length. What a reader must know before it sees such a
file is public, and this file says it in one term, `keyLayout`: for each of the three chains its
description at blank content, what the dry run of its block leaves, and the bytes of the parts that
are no chain. No number of an example is written here.

The road. `Model.Verify.planned` makes and reads back the parameter bytes of all seven chains from
the three public files. The chains' blocks are those of `Key.readKey` and `Proof.readTail`, run dry.

THIS IS NO ADMISSION OF THE PUBLIC FILES. `Model.Verify.planned` takes no bits of a caller: that the
parameter file's target is at least the bits that a caller asks for is asked by the program's stages
and not here. Of the public files `keyLayout` asks what `planned` asks, which parses all three files
and sizes all three kinds of file; `entryLayout` (OnBytes/Params/EntryLayout.lean) reads the
parameter file's first 32 lines alone. So the two layouts of one set of public files rest on two
different sets of tests. That `entryLayout` returns a value wherever `keyLayout` does is not proved.

What is content and no layout. In a file's own descriptions stand the table's root and answers, the
binding tree's root (in the shared chain's statement, and in the place of its random bytes), the two
seals (in the second chain's statement), and, for each tree that the second chain takes over from
an earlier chain, the tree's root and the value from which its leaves are hashed. Here each of them
is blank: zeros of the right length. One thing is a device of this file, which no page of the
format has: in the place of the root of a tree that is taken over stands a mark of 32 bytes that
says which tree of which chain it is (`markSrc`, `markOf`). A description with marks passes the
strict reader's conditions as if the marks were roots; it is for reading lengths, shapes and names
off, and `ChainLayout.withContent` puts the content in. The number of the second chain's first own
tree is layout: it is the number of roots that the first chain's rounds send, and one more (R13.7).

Written here a second time, and tied by no law: what the second chain's block starts from (in
`tailLayoutOf`: the five fields of `Proof.secondStart`, which takes a chain as read; and the book
with which the shared chain's end goes on, after `Proof.SharedEnd.goesOn`);
`rootsSent` and one more (`Proof.secondFirstTree`); `blankTableOf` (`EntryShape.blankTable`);
`KeyLayout.answers` (`EntryShape.answers`); the bytes of the place (`Proof.readPlace`); the parts
before the first chain (R13.1, R13.2); the labels of the shared and the second chain (in
`keyLayoutOf`, after `Key.tailPublic`; in `proofLayoutAt`, after `Proof.tailPublic`).

Main definitions: `markSrc`, `markOf`, `blankTableOf`, `rootsSent`, `ChainLayout`,
`ChainLayout.takenOver`, `ChainLayout.withContent`, `TailLayout`, `TailLayout.place`,
`TailLayout.parts`, `tailLayoutOf`, `KeyLayout`, `keyLayoutOf`, `plannedOf`, `keyLayout`,
`KeyLayout.table`, `KeyLayout.answers`, `KeyLayout.parts`.
Not yet cut as OnBytes/Params/EntryLayout.lean is: the value holds the digest of the public files
and the parameter bytes, which are answers of the hash, beside what follows without a hash.
What is not claimed: no theorem is stated here or elsewhere on these definitions. That the dry runs
do not depend on the content is not proved. No test of them lies in this tree.

-/
import OnBytes.Key.File
import OnBytes.Model.Verify
import OnBytes.Params.EntryLayout

set_option autoImplicit false

namespace OnBytes.Params

/-- A tree that is taken over, of no content. In the place of its root stands a mark of 32 bytes
that says which tree it is: the word of the chain that has sent it (0: the file's first chain; 1:
its shared chain), the word of the tree's place in that chain's order of sending, and zeros. In the
place of the value from which its leaves are hashed stand 32 zero bytes. -/
def markSrc (chain n : Nat) : Fmt.Src :=
  .given (Fmt.u64n chain ++ Fmt.u64n n ++ Fmt.zeroBytes 16) Fmt.zero32

/-- The chain and the place that a mark names. -/
def markOf (root : ByteArray) : Nat × Nat := ((Fmt.wordAt root 0).toNat, (Fmt.wordAt root 8).toNat)

/-- A table of the shape s and of no content. -/
def blankTableOf (s : IndexShape) : TableName :=
  ⟨Fmt.zero32, List.replicate (s.rows * s.answers) zeroE⟩

/-- The roots that the rounds send. -/
def rootsSent (r : Rounds) : Nat := r.foldl (fun a x => a + x.1.entry.roots) 0

/-- One chain of a layout: its description at blank content, and what the dry run leaves. -/
structure ChainLayout where
  /-- the chain's description at blank content -/
  spec : Fmt.SpecX
  /-- what the dry run of the chain's block leaves -/
  dry : ChainDry

/-- The trees that the chain takes over, in the order in which it opens them: the round, counted
from 1, the chain that has sent the tree, and the tree's place in that chain's order of sending. -/
def ChainLayout.takenOver (c : ChainLayout) : List (Nat × Nat × Nat) :=
  c.spec.base.rounds.zipIdx.flatMap fun r => r.1.opens.filterMap fun o => match o.2 with
    | .own _ => none
    | .given root _ => some (r.2 + 1, markOf root)

/-- The chain's description with the content put in: the statement, the random bytes' case, and for
each tree that is taken over its root and start, by the chain that has sent it and its place. -/
def ChainLayout.withContent (c : ChainLayout) (statement : ByteArray) (rand : Fmt.Rand)
    (src : Nat → Nat → Fmt.Src) : Fmt.SpecX :=
  { c.spec with
    base := { c.spec.base with
      statement := statement
      rand := rand
      rounds := c.spec.base.rounds.map fun r =>
        { r with opens := r.opens.map fun o => (o.1, match o.2 with
            | .own n => .own n
            | .given root _ => src (markOf root).1 (markOf root).2) } } }

/-- What a key file and a proof file each have after their first chain. The two kinds of file differ
there in the two chains' labels. -/
structure TailLayout where
  /-- the shape of the binding tree -/
  binding : LinBindingShape
  /-- the shared chain -/
  shared : ChainLayout
  /-- the second chain -/
  second : ChainLayout

/-- The bytes of the place in the binding tree: the word of the place, the leaf's salt, one digest
for each level (R13.6, R14.7; `Proof.readPlace`). -/
def TailLayout.place (t : TailLayout) : Nat := 8 + t.binding.saltBytes + 32 * t.binding.logLeaves

/-- The parts of a file after its first chain. -/
def TailLayout.parts (t : TailLayout) : List Fmt.FilePart :=
  [.outside "the place: its word" 8, .outside "the place: the leaf's salt" t.binding.saltBytes,
    .outside "the place: the path's digests" (32 * t.binding.logLeaves),
    .chain "shared" t.shared.spec, .chain "second" t.second.spec]

/-- The tail's layout. `lab₂` and `lab₃` are the labels of the shared and the second chain: a key's
or a proof's. `first` is what the dry run of the first chain's block has returned, and `roots` the
number of roots that the first chain sends. -/
def tailLayoutOf (shared : Shared) (second : Second) (binding : LinBindingShape) (lab₂ lab₃ : Nat)
    (first : Proof.FirstEnd) (roots : Nat) : Option TailLayout := do
  let table := blankTableOf shared.lin.fold.index
  let p : Proof.TailPublic := ⟨shared, second, binding, table, lab₂, lab₃⟩
  let (d2, end2) ← chainDryWith (Proof.sharedBlock p.lin (sizeKey p.lin.fold.index 0))
    (Proof.sharedStart p)
  let spec2 ← shared.describe lab₂ table Fmt.zero32 d2.rounds
  let start3 : Start :=
    { entries := second.given.rounds, samples := second.given.plan.samples, firstTree := roots + 1,
      st := first.st, book := first.book.goesOn (markSrc 0) }
  let (d3, _) ← chainDryWith
    (Proof.secondBlock p.lin first.lin { end2 with book := end2.book.goesOn (markSrc 1) }) start3
  let spec3 ← second.describe lab₃ Fmt.zero32 Fmt.zero32 d3.rounds (roots + 1)
  if Proof.bindingOk binding then
    pure ⟨binding, ⟨spec2, d2⟩, ⟨spec3, d3⟩⟩
  else none

/-- The layout of a key file. -/
structure KeyLayout where
  /-- the parameter bytes of the three chains, as read -/
  chains : KeyChains
  /-- the one-time chain -/
  oneTime : ChainLayout
  /-- what comes after the one-time chain -/
  tail : TailLayout

/-- The layout from the parameter bytes of a key's three chains, as read. Nothing if the field is
not field 2, if the public values do not fit together (`Key.admitted`), if a dry run fails, or if a
description at blank content is not in order. -/
def keyLayoutOf (k : KeyChains) : Option KeyLayout := do
  let p := k.oneTime
  if p.given.plan.field != .two || !Key.admitted p then none
  let (d1, first) ← chainDryWith (Key.oneTime p) (Key.startOf p)
  let spec1 ← p.describe (blankTableOf p.lin.fold.index) d1.rounds
  let t ← tailLayoutOf k.shared k.second p.binding labelShared labelSecond first
    (rootsSent d1.rounds)
  pure ⟨k, ⟨spec1, d1⟩, t⟩

/-- All that the program's routine `Model.Verify.planned` makes of the three public files. -/
def plannedOf (x : ConfigurationFiles) : Except String Model.Verify.Planned :=
  Model.Verify.planned x.policy x.scales (some x.layout)

/-- **The layout of a key file, from the three public files.** It is no admission of the public
files: the caller's bits are not asked. -/
def keyLayout (x : ConfigurationFiles) : Except String KeyLayout := do
  let p ← plannedOf x
  match keyLayoutOf p.chains.key with
  | some L => pure L
  | none => throw "key-parameters"

namespace KeyLayout

/-- The one shape of the tables. -/
def table (L : KeyLayout) : IndexShape := L.chains.oneTime.lin.fold.index

/-- How many stored answers follow the root. -/
def answers (L : KeyLayout) : Nat := L.table.rows * L.table.answers

/-- The parts of a key file, in the file's order (R13.2). -/
def parts (L : KeyLayout) : List Fmt.FilePart :=
  [.outside "head: the kind" 4, .outside "head: the version" 4,
    .outside "the first table's root" 32,
    .outside "the first table's stored answers" (24 * L.answers),
    .chain "one-time" L.oneTime.spec] ++
    L.tail.parts

end KeyLayout

end OnBytes.Params
