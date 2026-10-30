-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Proof/File.lean: the check of a whole proof file.

A proof file goes to one client and is about one request of a batch. It is, in order: the head; the
request's first chain; the request's place in its batch; the batch's shared chain; the request's
second chain, with which the file ends (docs/format/FORMAT.md, R14.1). No part is
preceded by its length. The C++ counterpart is check_proof (blocks/frame/check.h).

Words. A chain is a hash chain: one interactive proof, made non-interactive. A block is a routine of
the verifier in `Blk` (OnBytes/Iop/Ground.lean). Its dry run reads no file and lists the chain's
rounds; a view is what the strict reader returns of a chain that it has read; the block's run on the
view takes the decision. A link is a part of the computation with a sub-proof of its own
(OnBytes/Iop/Req.lean). The table is a stored copy of the committed matrix of weights. A row on the
table is a linear claim on that matrix; the test on the table (OnBytes/Iop/Lin.lean) takes such rows
in. Other words: lean/GLOSSARY.md.

This file knows nothing of a model. What a request's links prove is up to the caller: the caller
passes in one block, `links`, for all links of the first chain, from the first link's first message
to the end of the links' last proximity test. That block returns the number of the oracle message
that holds the masks of the request's rows on the table, those rows, and the reply as received.

The reply is compared here and nowhere else. No chain's first hash call takes it in: the prover
sends it in a round of its own (FORMAT.md, R14.8).

Who tests the index-mask message. This oracle message has mask rows only; the request's rows on the
table take their mask entries from it. It is sent with the first link's first message but belongs to
no link's group, so the frame of links (OnBytes/Iop/Req.lean) does not test it. The first part of
the test on the table, which `firstBlock` runs, puts it into the group of the request's own rows,
since those rows' mask entries are in it, and the second chain's proximity test reads that group.
The second chain's block ends with `Blk.requireAllTested`, which fails if a sampled oracle message
is in no group or if the proximity test of some group has not begun. That call cannot see a row that
was never added to a group. The rows that `links` returns are in no group until `firstBlock` passes
them on; that `links` returns all of them is tested only by their number, `pendingRows` in the
parameter bytes.

Main definitions: `LinksResult`, `firstBlock`, `ProofRead`, `readProof`, `refusalOn`,
`proofRefusal`, `check`. One theorem: `proofRefusal_eq`.

What is not claimed. No theorem in this file is about a yes (what is proved, and of what:
lean/OnBytes/THEOREMS.md). By the protocol's design a yes means: under the parameter bytes that the
caller passes in, the file is a proof that `reply` is the reply to `request` by the weights in the
stored table, as far as `links` checks a model's steps. Where these bytes come from is up to the
caller; every call of the program derives them from the public files. A yes assumes a checked table:
no type records that the table's key file and, for a copy, its entry file were checked, so the
caller must have done that. Nothing here computes a round's error. So two things are left unsaid
here: the number of bits that a yes is worth, and whether some round needs its work to reach the
target that the parameter file sets (GLOSSARY.md: target, round, proof of work).
-/
import OnBytes.Proof.Tail
import OnBytes.Proof.Head
import OnBytes.Result

namespace OnBytes.Proof

/-- What the caller's part of the first chain returns. -/
structure LinksResult where
  /-- the oracle message that holds the masks of the request's rows on the table -/
  indexMasks : Nat := noId
  /-- the rows on the table that the links return -/
  pending : List TensorRow := []
  /-- the reply as received; none until a link has taken it off the channel -/
  reply : Option E := none

/-- True if the shape, the layout, the codes and the links' identifiers from which a caller has made
its links are those of the first chain's parameter bytes, which the strict reader hashes. It makes
a part of the comparison that `check` names as the caller's duty: these four values and no other. -/
def sameItems (p : Params.First) (codes : Codes) (shape : Params.ReqShape)
    (layout : Params.ReqLayout) (identifiers : List Nat) : Bool :=
  p.codes == codes && p.shape == shape && p.layout == layout && p.identifiers == identifiers

/-- The block of a proof's first chain: the caller's links; the comparison of the reply; the first
part of the test on the table, on the rows that the links return; the seal. A yes of this block
alone means that the caller's block `links` has passed its own tests and that the reply which it
received equals `reply`. It says nothing of the index-mask message, nor of the rows on the table:
the group that holds them is opened here and tested on the second chain. Only `proofRefusal` is the
decision on a proof. -/
def firstBlock (p : Params.First) (links : Blk LinksResult) (reply : E) : Blk FirstEnd := do
  let r ← links
  let got ← Blk.get r.reply
  Blk.check replyCheck (got == reply)
  Blk.must (r.pending.length == p.pendingRows)
  let lin ← memberFirstVerify p.lin r.indexMasks r.pending
  firstEnd lin

/-- A first chain's block starts from the plan's rounds and answers to a sample, the codes, and no
tree. -/
def firstStart (p : Params.First) : Start :=
  { entries := p.given.rounds, samples := p.given.plan.samples, st := { codes := p.codes } }

/-- What is public about the tail of a proof file. -/
def tailPublic (c : Params.ProofChains) (table : Params.TableName) : TailPublic :=
  { shared := c.shared, second := c.second, binding := c.first.binding, table := table,
    lab₂ := Params.labelSharedProof, lab₃ := Params.labelSecondProof }

/-- A proof file as it was read. -/
abbrev ProofRead : Type := TailRead

/-- Reads a proof file. No decision is taken here: `proofRefusal` takes it. `copy` is the number
under which the caller holds the table. `request` and `words` are the third and the fourth item of
the first chain's statement (`Params.First.statement`). `block` is the first chain's block. The
names of the refusals say which part of the file was refused. Also refused: parameter bytes of the
first chain for a field other than the one in which this program computes, or with 32 zero bytes as
the digest of the public files. -/
def readProof (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Reading ProofRead := do
  let (madeOn, i) ←
    match readProofHead c.first.given.plan.field file with
    | .error e => throw e
    | .ok x => pure x
  if madeOn != copy then throw "made-on-another-stored-copy"
  if c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32 then
    throw "first-chain-parameters"
  let (rounds1, dry) ← need "first-chain-parameters" (block.dryRun (firstStart c.first))
  let spec1 ← need "first-chain-parameters" (c.first.describe table copy request words rounds1)
  let first ← readNamed "first-chain-" spec1 file i
  let r ← readTail (tailPublic c table) dry first file
  if r.next != file.size then throw "bytes-left-over"
  pure r

/-- The decision on the first chain's view and on the rest of a proof file as read. Returns nothing
for a yes, and else the refusal's name (`refusalName`).
The view is an argument of its own so that the run on it holds the only reference to it: a round's
memory can then be given back when the run has left the round. The function is not inlined, so that
its arguments are made before the run begins. -/
@[noinline] def refusalOn (c : Params.ProofChains) (table : Params.TableName)
    (block : Blk FirstEnd) (view : Fmt.View) (rest : ProofRead) : Option String :=
  match judge "first-chain-" block (firstStart c.first) view with
  | .error why => some why
  | .ok real => tailRefusal (tailPublic c table) real rest

/-- The decision on the three views of a proof file. Returns nothing for a yes, and else the
refusal's name: the chain that was refused and, for three tests, the test, or a name that `links`
has given (`refusalName`). Of the first chain it keeps, beside the view, only the light form
(`ChainRead.light`). -/
def proofRefusal (c : Params.ProofChains) (table : Params.TableName) (block : Blk FirstEnd)
    (r : ProofRead) : Option String :=
  refusalOn c table block r.first.view { r with first := r.first.light }

/-- `proofRefusal` decides as on the first chain kept whole: the run on its view, then the tail. -/
theorem proofRefusal_eq (c : Params.ProofChains) (table : Params.TableName)
    (block : Blk FirstEnd) (r : ProofRead) :
    proofRefusal c table block r =
      match judge "first-chain-" block (firstStart c.first) r.first.view with
      | .error why => some why
      | .ok real => tailRefusal (tailPublic c table) real r := by
  unfold proofRefusal refusalOn
  simp only [tailRefusal_light]

/-- The names under which `readProof` and `proofRefusal` refuse, but for the names that `links`
gives. -/
def fileNames : List String :=
  ["made-on-another-stored-copy", "first-chain-parameters", "bytes-left-over"] ++ headNames ++
    namesOf "first-chain-" ++ tailNames

/-- The intermediate values that the first chain's block notes in its run on the view, in their
order. No test reads them. They let this verifier be compared with another one, value by value. -/
def firstNotes (c : Params.ProofChains) (block : Blk FirstEnd) (r : ProofRead) :
    Array (String × E) :=
  block.notesOn (firstStart c.first) r.first.view

/-- Checks the proof file `file` under the parameter bytes of its three chains. table: root and
answers of the stored copy with the number `copy`, as the reader of its key file or entry file has
kept them. request: the request as one string of bytes. words: the caller's request itself, byte for
byte; for a model's proof the request file, whole. reply: the reply that the client was given.
links: the caller's part of the first chain. The check of a proof file is one verdict: it keeps its
own list of the tree vertices that it has met (FORMAT.md, R7.14; OnBytes/Chain/Session.lean) and
shares it with no other file's check.
The caller's duty. Every public value that `links` uses (the request's shape, the layout, the codes,
the links' identifiers, the shape of the test on the table, whatever else its sub-proofs take as
data) is taken out of `c.first`, which was read from the bytes that the strict reader hashes, or is
compared with it before this call. A value that reaches `links` in any other way is bound by no hash
call, and a yes then says nothing about it. Nothing here ties `request` to `words`: both are hashed
as they come. That `request` is the string which belongs to `words` is the caller's to see to; both
are strings of bytes, so passing them in the wrong order is no error of types. -/
def check (c : Params.ProofChains) (table : Params.TableName) (copy : Nat)
    (request words : ByteArray) (reply : E) (links : Blk LinksResult) (file : ByteArray) :
    Verdict :=
  let block := firstBlock c.first links reply
  match (readProof c table copy request words block file).fromStart with
  | .error why => .refused ⟨.proof, why⟩
  | .ok r =>
    match proofRefusal c table block r with
    | some why => .refused ⟨.proof, why⟩
    | none => .accepted

end OnBytes.Proof
