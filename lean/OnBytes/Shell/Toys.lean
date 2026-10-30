-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Shell/Toys.lean: verdicts on the files of the small test protocols.

The C++ library comes with tools that write files of small test protocols, on made-up data: a
product test and a chain of links (blocks/toy/handover.cpp); a key file and an entry file, which
ties a further stored copy of a table to the first (blocks/frame/handover_files.cpp); and the proof
files of a test batch (blocks/frame/handover_proof.cpp). Each tool has one or two public files,
which fix its sizes and its security target. Here every chain's parameter bytes are derived from
them, and the checks of OnBytes/Toy/, Key/, Entry/ and Proof/ are applied to the files' bytes. The
bits that the caller asks for do not change the parameter bytes: public files whose own target is
below them are refused under the name `security-bits`. This file holds no public file: the functions
take whatever they are given.

In these protocols proof of work counts toward the bits that the caller asks, and how much work a
round has is a line of the public file. So each call also says whether some round holds only with
its work: the functions `productWork` to `toyProofWork` give the numbers for the line on work, by
the accounting of the whole call (OnBytes/Plan/ToyWork.lean).

Main definitions: `product`, `links`, `key`, `entry`, `toyProof`; `productWork`, `linksWork`,
`keyWork`, `entryWork`, `toyProofWork`. What is not claimed: no theorem is stated here.
-/
import OnBytes.Toy.Product
import OnBytes.Toy.Links
import OnBytes.Key.File
import OnBytes.Entry.File
import OnBytes.Proof.ToyLinks
import OnBytes.Plan.ToyRuns
import OnBytes.Plan.ToyShapes
import OnBytes.Plan.ToyWork

namespace OnBytes.Shell

/-- A check's result as a verdict. What the check returns on success is dropped. -/
def verdictOf {α : Type} : Except Refusal α → Verdict
  | .ok _ => .accepted
  | .error r => .refused r

/-- Goes on with what was derived from the public files, or refuses under the name that the
derivation gives. -/
def derived {α : Type} (x : Except String α) (next : α → Verdict) : Verdict :=
  match x with
  | .error name => .refused ⟨.configuration, name⟩
  | .ok a => next a

/-- The verdict on a proof file of the product test, under its public file. -/
def product (bits : Nat) (pub file : ByteArray) : Verdict :=
  derived (Plan.productRun pub bits) fun r => Toy.product r.params file

/-- The verdict on a proof file of the chain of links, under its public file. -/
def links (bits : Nat) (pub file : ByteArray) : Verdict :=
  derived (Plan.linksRun pub bits) fun r => Toy.links r.params file

/-- The verdict on a key file under the parameter bytes of its three chains. -/
def keyUnder (oneTime shared second file : ByteArray) : Verdict :=
  match Params.KeyChains.read oneTime shared second with
  | none => .refused ⟨.configuration, "key-parameters"⟩
  | some k => verdictOf (Key.check k file)

/-- The verdict on a key file, under the two public files. -/
def key (bits : Nat) (pub1 pub2 file : ByteArray) : Verdict :=
  derived (Plan.toyForCommitters pub1 pub2 bits) fun c =>
    keyUnder c.keyOneTime c.keyShared c.keySecond file

/-- The first table as a key file holds it after its head: its root and its record's answers
(OnBytes/Entry/Table.lean says what these are). Their number follows from the parameter bytes of the
entry's chain. The key file's own proofs are not checked here. -/
def firstTable (params key : ByteArray) : Except Refusal Params.TableName :=
  match Entry.answersOf params with
  | none => .error ⟨.configuration, "entry-parameters"⟩
  | some (f, count) =>
    match Proof.readHead f .key key with
    | .error e => .error ⟨.key, e⟩
    | .ok i =>
      match readTable f count key i with
      | .error e => .error ⟨.key, e⟩
      | .ok (table, _) => .ok table

/-- The verdict on an entry file under the parameter bytes of its chain and the first table that
the key file names. -/
def entryUnder (params key file : ByteArray) : Verdict :=
  match firstTable params key with
  | .error r => .refused r
  | .ok first => verdictOf (Entry.check params first file)

/-- The verdict on an entry file, under the two public files and the first table that the key file
names. The key file's own proofs are not checked here: that is the call `key`. -/
def entry (bits : Nat) (pub1 pub2 key file : ByteArray) : Verdict :=
  derived (Plan.toyForCommitters pub1 pub2 bits) fun c => entryUnder c.entryLink key file

/-- The verdict on a proof file of a test batch, under the two public files. The further arguments
are those of `Proof.toyCall`. Not checked here: the file that names the table, which is read only
for the table's root and its record's answers; and the forms of the links' claims, which are taken
from the claims file as given. The test links prove nothing about the reply
(blocks/frame/handover_proof.cpp). -/
def toyProof (bits : Nat) (pub1 pub2 tableFile : ByteArray) (number : String)
    (request reply claims file : ByteArray) : Verdict :=
  derived (Plan.toyForProofs pub1 pub2 bits) fun c =>
    Proof.toyCall c.first c.shared c.second pub1 pub2 tableFile number request reply claims file

/-- What the accounting says on proof of work: the work that is counted, or nothing if every round
holds without its work; and the weakest round's bits without work, in hundredths. -/
abbrev Work : Type := Except String (Option Model.Stages.WorkCount × Nat)

/-- The work of a product test under its public file. -/
def productWork (bits : Nat) (pub : ByteArray) : Work := do
  (← Plan.productRun pub bits).workCount bits

/-- The work of a chain of links under its public file. -/
def linksWork (bits : Nat) (pub : ByteArray) : Work := do
  (← Plan.linksRun pub bits).workCount bits

/-- The work of a key file's chains under the two public files. -/
def keyWork (bits : Nat) (pub1 pub2 : ByteArray) : Work := do
  Plan.keyWorkCount (← Plan.toyForCommitters pub1 pub2 bits) bits

/-- The work of an entry file's chain under the two public files. -/
def entryWork (bits : Nat) (pub1 pub2 : ByteArray) : Work := do
  Plan.entryWorkCount (← Plan.toyForCommitters pub1 pub2 bits) bits

/-- The work of all chains under the two public files of a test batch. -/
def toyProofWork (bits : Nat) (pub1 pub2 : ByteArray) : Work := do
  Plan.wholeWorkCount (← Plan.toyForProofs pub1 pub2 bits) bits

end OnBytes.Shell
