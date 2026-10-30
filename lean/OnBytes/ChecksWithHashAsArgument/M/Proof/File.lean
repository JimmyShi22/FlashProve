-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/ChecksWithHashAsArgument/M/Proof/File.lean: the definitions of OnBytes/Proof/File.lean that hand a hash on
(`readProof`, `check`), written once more over a monad m in which the hash is asked, by this
project's authors, after that file's text. What does not hash is that file's own.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Proof.File
import OnBytes.ChecksWithHashAsArgument.M.Chain.EngineM
import OnBytes.ChecksWithHashAsArgument.M.Chain.Reader
import OnBytes.ChecksWithHashAsArgument.M.Chain.Session
import OnBytes.ChecksWithHashAsArgument.M.Chain.Why
import OnBytes.ChecksWithHashAsArgument.M.Entry.Table
import OnBytes.ChecksWithHashAsArgument.M.Proof.Place
import OnBytes.ChecksWithHashAsArgument.M.Proof.Reading
import OnBytes.ChecksWithHashAsArgument.M.Proof.Tail

namespace OnBytes.TwoPort.M.Proof

open OnBytes.Proof

/-- Reads a proof file. No decision is taken here: `proofRefusal` takes it. `copy` is the number
under which the caller holds the table. `request` and `words` are the third and the fourth item of
the first chain's statement (`Params.First.statement`). `block` is the first chain's block. The
names of the refusals say which part of the file was refused. Also refused: parameter bytes of the
first chain for a field other than the one in which this program computes, or with 32 zero bytes as
the digest of the public files. -/
def readProof {m : Type → Type} [Monad m] (hh : HashM m) (c : Params.ProofChains)
    (table : Params.TableName) (copy : Nat) (request words : ByteArray) (block : Blk FirstEnd)
    (file : ByteArray) : Reading m ProofRead := do
  let (madeOn, i) ←
    match readProofHead c.first.given.plan.field file with
    | .error e => throw e
    | .ok x => pure x
  if madeOn != copy then throw "made-on-another-stored-copy"
  if c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32 then
    throw "first-chain-parameters"
  let (rounds1, dry) ← need "first-chain-parameters" (block.dryRun (firstStart c.first))
  let spec1 ← need "first-chain-parameters" (c.first.describe table copy request words rounds1)
  let first ← readNamed hh "first-chain-" spec1 file i
  let r ← readTail hh (tailPublic c table) dry first file
  if r.next != file.size then throw "bytes-left-over"
  pure r

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
def check {m : Type → Type} [Monad m] (hh : HashM m) (c : Params.ProofChains)
    (table : Params.TableName)
    (copy : Nat) (request words : ByteArray) (reply : E) (links : Blk LinksResult)
    (file : ByteArray) : m Verdict := do
  let block := firstBlock c.first links reply
  match ← (readProof hh c table copy request words block file).fromStart with
  | .error why => pure (.refused ⟨.proof, why⟩)
  | .ok r =>
    match proofRefusal c table block r with
    | some why => pure (.refused ⟨.proof, why⟩)
    | none => pure .accepted

end OnBytes.TwoPort.M.Proof
