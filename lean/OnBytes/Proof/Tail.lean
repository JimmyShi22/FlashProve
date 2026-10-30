-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/Tail.lean: what a key file and a proof file have in common after their first chain.

Both files go on in the same way: the place in the binding tree, the shared chain, the second
chain (docs/format/FORMAT.md, R13.2, R13.6, R13.7, R14.1, R14.7, R14.9, R14.10). The two
chains hold the shared part and the second part of the test for linear claims on the stored table
(OnBytes/Iop/Lin.lean). The test's first part is at the end of the first chain, before its seal;
the caller reads and decides that chain. In C++ this file's part is the second half of check_proof
(blocks/frame/check.h) and of check_key_under (blocks/frame/check_key.h).

How the three chains depend on each other.
 - The first chain ends in a seal. The seal is the content of a leaf of the binding tree.
 - The binding tree's root is an item of the shared chain's statement, and it takes the place of
   that chain's random bytes.
 - The second chain's statement holds the seals of the first and of the shared chain. The second
   chain begins with the first chain's trees and takes over one tree of the shared chain.

Words. A block is a routine of the verifier in `Blk` (OnBytes/Iop/Ground.lean). Its dry run reads
no file and lists the chain's rounds. A chain's description is what the strict reader needs to read
the chain's bytes. A view is what the strict reader returns of a chain that it has read. The
block's run on the view takes the decision.

The work is done in two halves.
 1. `readTail` reads the bytes. Each chain's description comes from a dry run of the chain's block.
    A later description takes roots, run values and seals from what was read before.
 2. `tailRefusal` takes the decision on the two views. The second chain's block starts from what
    the first chain's block has returned, and reads what the shared chain's block has returned.
The statement's item for the table and the key that the blocks read are both made from the one value
`p.table`, and all blocks of the tail use the one shape `p.lin`.

Main definitions: `TailPublic`, `FirstEnd`, `sharedBlock`, `secondBlock`,
`TailRead`, `readTail`, `tailNames`, `tailRefusal`.

What is not claimed. That the first chain's parameter bytes hold the same codes and the same shape
of the test as the shared chain's is tested where the parameter bytes are read
(OnBytes/Params/Chains.lean), not here. A key's tail is the table's one-time test, a proof's tail a
later test. Here both run the same blocks on the shape and the plans that are passed in, and no
argument of a block says which test it is; the two chains' labels, which differ between a key and a
proof, enter the descriptions alone. The C++ blocks are told which, and they compare three things
with those from which the plan's errors were computed: the table, which of the two tests runs, and
the number of the binding tree's leaves, by which the plan multiplies the error of the shared point
(blocks/iop/lin.h, lin_shared_verify_on_shape: require_table, require_sharing). None of the three is
compared here. That the plans were made for this table, this test and this tree is up to the caller.
-/
import OnBytes.Iop.Lin
import OnBytes.Proof.Reading
import OnBytes.Params.Chains
import OnBytes.Proof.Place
import OnBytes.Entry.Table

namespace OnBytes.Proof

open Params (LinShape)

/-! ## The two blocks -/

/-- What is public about a tail. -/
structure TailPublic where
  /-- the parameter bytes of the shared chain, read -/
  shared : Params.Shared
  /-- the parameter bytes of the second chain, read -/
  second : Params.Second
  /-- the shape of the binding tree, as the first chain's parameter bytes have it -/
  binding : Params.LinBindingShape
  /-- the stored table that the test reads -/
  table : Params.TableName
  /-- the label of the shared chain: a key's or a proof's (OnBytes/Params/Chains.lean) -/
  lab₂ : Nat
  /-- the label of the second chain: a key's or a proof's -/
  lab₃ : Nat

/-- The shape of the test on the table. -/
def TailPublic.lin (p : TailPublic) : LinShape := p.shared.lin

/-- What the block of a first chain returns. -/
structure FirstEnd where
  /-- the statement at the block's end -/
  st : Statement
  /-- the book of trees at the block's end -/
  book : TreeBook
  /-- what the first part of the test on the table passes to the second -/
  lin : LinFirst

/-- What the block of a shared chain returns. -/
structure SharedEnd where
  /-- the statement at the block's end -/
  st : Statement
  /-- the book of trees at the block's end -/
  book : TreeBook
  /-- what the shared part of the test on the table returns -/
  lin : LinShared

/-- The closing of a first chain's block: the round in which the chain is sealed, and what the
block returns. `lin` comes from the first part of the test on the table. -/
def firstEnd (lin : LinFirst) : Blk FirstEnd := do
  let _ ← Blk.close "SEAL" .sealed
  let h ← Blk.handOver
  pure ⟨h.1, h.2, lin⟩

/-- The block of a shared chain: the shared part of the test on the table, its proximity tests, and
the seal. It fails at its end unless a proximity test has begun on every group and every sampled
oracle message is in a group (`Blk.requireAllTested`). -/
def sharedBlock (S : LinShape) (key : TableKey) : Blk SharedEnd := do
  let x ← linSharedVerify S key
  linSharedTestsVerify S x
  let _ ← Blk.close "SEAL" .sealed
  Blk.requireAllTested
  let h ← Blk.handOver
  pure ⟨h.1, h.2, x⟩

/-- The block of a second chain: the second part of the test on the table and its proximity tests.
`shared` is what the shared chain's block has returned, with its trees named by root and start. It
fails at its end unless a proximity test has begun on every group and every sampled oracle message
is in a group (`Blk.requireAllTested`). -/
def secondBlock (S : LinShape) (first : LinFirst) (shared : SharedEnd) : Blk Unit := do
  let x ← linSecondVerify S first shared.st shared.book shared.lin
  linSecondTestsVerify S first x
  Blk.requireAllTested

/-- How a later chain names the trees that the chain r has sent. Where `r.tree n` gives nothing (r
has sent no tree of that number, or has no run's value), the root is empty, and a description in
which a round opens such a tree is refused. -/
def treesOf (r : ChainRead) (n : Nat) : Fmt.Src :=
  (r.tree n).getD (.given ByteArray.empty ByteArray.empty)

/-- A shared chain's block starts from the plan's rounds and answers to a sample, the codes, and no
tree. -/
def sharedStart (p : TailPublic) : Start :=
  { entries := p.shared.given.rounds, samples := p.shared.given.plan.samples,
    st := { codes := p.shared.codes } }

/-- The number of the second chain's first own tree: it comes after the first chain's trees and the
one tree that is taken over from the shared chain (R13.7). -/
def secondFirstTree (first : ChainRead) : Nat := first.roots.length + 1

/-- What a second chain's block starts from: what the first chain's block has returned, with that
chain's trees named by root and start. -/
def secondStart (p : TailPublic) (e : FirstEnd) (first : ChainRead) : Start :=
  { entries := p.second.given.rounds, samples := p.second.given.plan.samples,
    firstTree := secondFirstTree first, st := e.st, book := e.book.goesOn (treesOf first) }

/-- What the shared chain's block has returned, as the second chain's block reads it. -/
def SharedEnd.goesOn (e : SharedEnd) (shared : ChainRead) : SharedEnd :=
  { e with book := e.book.goesOn (treesOf shared) }

/-! ## Reading -/

/-- A tail as it was read. -/
structure TailRead where
  /-- the first chain, which the caller has read -/
  first : ChainRead
  /-- the place in the binding tree as read -/
  place : Place
  /-- the table as the blocks read it -/
  key : TableKey
  /-- the shared chain as read -/
  shared : ChainRead
  /-- the second chain as read -/
  second : ChainRead

/-- The place of the first byte after the tail. -/
def TailRead.next (r : TailRead) : Nat := r.second.next

/-- Reads a tail in b after the first chain. `dry` is what the dry run of the first chain's block
has returned. The names of the refusals say which part of the file was refused. -/
def readTail (p : TailPublic) (dry : FirstEnd) (first : ChainRead) (b : ByteArray) :
    Reading TailRead := do
  let g := p.shared.given
  let seal1 ← need "first-chain-seal" first.seal
  let place ← need "place" (readPlace p.binding g.cfg seal1 b first.next)
  let key ← need "table-record" (tableKey g.plan.field g.cfg p.lin.fold.index p.table 0)
  let (rounds2, end2) ← need "shared-chain-parameters"
    ((sharedBlock p.lin key).dryRun (sharedStart p))
  let spec2 ← need "shared-chain-parameters" (p.shared.describe p.lab₂ p.table place.root rounds2)
  let shared ← readNamed "shared-chain-" spec2 b place.next
  let seal2 ← need "shared-chain-seal" shared.seal
  let rounds3 ← need "second-chain-parameters"
    ((secondBlock p.lin dry.lin (end2.goesOn shared)).rounds (secondStart p dry first))
  let spec3 ← need "second-chain-parameters"
    (p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree first))
  let second ← readNamed "second-chain-" spec3 b shared.next
  pure ⟨first, place, key, shared, second⟩

/-- The names under which `readTail` and `tailRefusal` refuse. -/
def tailNames : List String :=
  ["first-chain-seal", "place", "table-record", "shared-chain-parameters", "shared-chain-seal",
   "second-chain-parameters"] ++ namesOf "shared-chain-" ++ namesOf "second-chain-"

/-! ## Deciding -/

/-- The decision on a tail's two views. `real` is what the first chain's block has returned on the
first chain's view. Returns nothing for a yes, and else the refusal's name: the chain that was
refused and, for the two named tests of a proximity test, the test (`refusalName`). -/
def tailRefusal (p : TailPublic) (real : FirstEnd) (r : TailRead) : Option String :=
  match judge "shared-chain-" (sharedBlock p.lin r.key) (sharedStart p) r.shared.view with
  | .error why => some why
  | .ok end2 =>
    match judge "second-chain-" (secondBlock p.lin real.lin (end2.goesOn r.shared))
        (secondStart p real r.first) r.second.view with
    | .error why => some why
    | .ok () => none

/-- A chain's light form names the chain's trees as the chain does. -/
theorem treesOf_light (r : ChainRead) : treesOf r.light = treesOf r := by
  funext n
  unfold treesOf
  rw [ChainRead.light_tree]

/-- From the first chain's light form a second chain's block gets the same start. -/
theorem secondStart_light (p : TailPublic) (e : FirstEnd) (first : ChainRead) :
    secondStart p e first.light = secondStart p e first := by
  unfold secondStart secondFirstTree
  rw [treesOf_light, ChainRead.light_roots]

/-- The decision on a tail's two views takes from the first chain only what its light form keeps. -/
theorem tailRefusal_light (p : TailPublic) (real : FirstEnd) (r : TailRead) :
    tailRefusal p real { r with first := r.first.light } = tailRefusal p real r := by
  unfold tailRefusal
  simp only [secondStart_light]

/-- True if the decision on the tail's two views is yes. -/
def tailDecides (p : TailPublic) (real : FirstEnd) (r : TailRead) : Bool :=
  (tailRefusal p real r).isNone

end OnBytes.Proof
