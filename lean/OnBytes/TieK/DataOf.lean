-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/DataOf.lean: the data of a file's three chains, made of three chains that were read
already, without a call of a reader.

OnBytes/TieK/ReadThreeDefs.lean has one fixed reading of a file with three chains (readThree). It
calls the program's readers, which hash. A reader that asks an oracle for its hashes returns the
three chains as read (Proof.TailRead), and a statement about such a reader must not read the file
again at the program's hash. dataOf makes readThree's record of such a value r. It is readThree's
text in which the three calls of the chain's reader, the reading of the place in the binding tree
and the making of the table's key are replaced by the fields of r. What is left are the dry runs,
the three describers, the two seals, the bytes of the binding tree's leaf, and readThree's last
test, that the second chain ends at the file's end.

Of r it reads the first chain's rounds, run's value and end, the root of the place, the table's key,
the shared chain's rounds and run's value, and the second chain's end. It does not look at the three
views, which readThree makes of the descriptions, at the rest of the place, at the shared chain's
end or at what the second chain holds.

Main definitions: dataOf; keyDataOf, proofDataOf (at a key file's and a proof file's letters).
Two laws: dataOf_of and dataOf_inv: the definition, unfolded, in both directions.

Limits. It names no reader and no hash, so it says nothing on where r comes from. The first chain's
block and describer are letters of dataOf, and the block is one of proofDataOf. At the letters of
the two files no function that is called is meant to hash, and the program's readers over a monad
(OnBytes/ChecksWithHashAsArgument/M/Proof/Tail.lean) leave the same calls as they are; no theorem says so.
Its laws against the fixed reading are in OnBytes/TieK/DataOfLaws.lean [not in this library]. The
program does not import this file.


-/
import OnBytes.TieK.ReadThreeDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof

/-- **The data of three chains that were read.** p: what is public about the tail; block1, start1:
the first chain's block and what it starts from; describe1: the first chain's description from its
rounds; copy: the number that is kept in the data; r: the three chains as read. -/
def dataOf (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start)
    (describe1 : Params.Rounds → Option Fmt.SpecX) (file : ByteArray) (copy : Nat) (r : TailRead) :
    Option ChainsData :=
  match block1.dryRun start1 with
  | none => none
  | some (rounds1, dry) =>
  match describe1 rounds1 with
  | none => none
  | some S1 =>
  match r.first.seal with
  | none => none
  | some seal1 =>
  match slotBytes p.binding file r.first.next with
  | none => none
  | some (salt, path) =>
  match (sharedBlock p.lin r.key).dryRun (sharedStart p) with
  | none => none
  | some (rounds2, dry2) =>
  match p.shared.describe p.lab₂ p.table r.place.root rounds2 with
  | none => none
  | some S2 =>
  match r.shared.seal with
  | none => none
  | some seal2 =>
  match (secondBlock p.lin dry.lin (dry2.goesOn r.shared)).rounds (secondStart p dry r.first) with
  | none => none
  | some rounds3 =>
  match p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree r.first) with
  | none => none
  | some S3 =>
    if r.second.next = file.size then
      some ⟨rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, salt, path, copy⟩
    else none

/-- dataOf's definition, unfolded: where its nine steps return and the second chain ends at the
file's end, it returns their values. It names no reader and no hash, so it says nothing on where r
comes from. -/
theorem dataOf_of {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start}
    {describe1 : Params.Rounds → Option Fmt.SpecX} {file : ByteArray} {r : TailRead}
    {rounds1 : Params.Rounds} {dry : FirstEnd} {S1 : Fmt.SpecX} {seal1 seal2 : ByteArray}
    {rounds2 : Params.Rounds} {dry2 : SharedEnd} {S2 : Fmt.SpecX} {rounds3 : Params.Rounds}
    {S3 : Fmt.SpecX} {salt : ByteArray} {path : List ByteArray}
    (h1 : block1.dryRun start1 = some (rounds1, dry)) (h2 : describe1 rounds1 = some S1)
    (h3 : r.first.seal = some seal1)
    (h4 : slotBytes p.binding file r.first.next = some (salt, path))
    (h5 : (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (rounds2, dry2))
    (h6 : p.shared.describe p.lab₂ p.table r.place.root rounds2 = some S2)
    (h7 : r.shared.seal = some seal2)
    (h8 : (secondBlock p.lin dry.lin (dry2.goesOn r.shared)).rounds (secondStart p dry r.first) =
      some rounds3)
    (h9 : p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree r.first) = some S3)
    (h10 : r.second.next = file.size) (copy : Nat) :
    dataOf p block1 start1 describe1 file copy r =
      some ⟨rounds1, dry, S1, r, seal1, seal2, rounds2, dry2, S2, rounds3, S3, salt, path,
        copy⟩ := by
  unfold dataOf
  rw [h1]
  dsimp only
  rw [h2]
  dsimp only
  rw [h3]
  dsimp only
  rw [h4]
  dsimp only
  rw [h5]
  dsimp only
  rw [h6]
  dsimp only
  rw [h7]
  dsimp only
  rw [h8]
  dsimp only
  rw [h9]
  dsimp only
  rw [if_pos h10]

/-- The way back: what dataOf returns holds the values of its nine steps, the chains and the number
that it was given; and the second chain ends at the file's end. -/
theorem dataOf_inv {p : TailPublic} {block1 : Blk FirstEnd} {start1 : Start}
    {describe1 : Params.Rounds → Option Fmt.SpecX} {file : ByteArray} {copy : Nat} {r : TailRead}
    {d : ChainsData} (h : dataOf p block1 start1 describe1 file copy r = some d) :
    block1.dryRun start1 = some (d.rounds1, d.dry) ∧ describe1 d.rounds1 = some d.S1 ∧
      r.first.seal = some d.seal1 ∧
      slotBytes p.binding file r.first.next = some (d.salt, d.path) ∧
      (sharedBlock p.lin r.key).dryRun (sharedStart p) = some (d.rounds2, d.dry2) ∧
      p.shared.describe p.lab₂ p.table r.place.root d.rounds2 = some d.S2 ∧
      r.shared.seal = some d.seal2 ∧
      (secondBlock p.lin d.dry.lin (d.dry2.goesOn r.shared)).rounds (secondStart p d.dry r.first) =
        some d.rounds3 ∧
      p.second.describe p.lab₃ d.seal1 d.seal2 d.rounds3 (secondFirstTree r.first) = some d.S3 ∧
      r.second.next = file.size ∧ d.r = r ∧ d.copy = copy := by
  unfold dataOf at h
  split at h
  · cases h
  rename_i rounds1 dry h1
  try dsimp only at h
  split at h
  · cases h
  rename_i S1 h2
  try dsimp only at h
  split at h
  · cases h
  rename_i seal1 h3
  try dsimp only at h
  split at h
  · cases h
  rename_i salt path h4
  try dsimp only at h
  split at h
  · cases h
  rename_i rounds2 dry2 h5
  try dsimp only at h
  split at h
  · cases h
  rename_i S2 h6
  try dsimp only at h
  split at h
  · cases h
  rename_i seal2 h7
  try dsimp only at h
  split at h
  · cases h
  rename_i rounds3 h8
  try dsimp only at h
  split at h
  · cases h
  rename_i S3 h9
  try dsimp only at h
  split at h
  · rename_i h10
    cases h
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, rfl, rfl⟩
  · cases h

/-- The data of a key file's three chains that were read: dataOf at the letters at which
readKeyChains calls readThree. -/
def keyDataOf (k : Params.KeyChains) (table : Params.TableName) (key : ByteArray) (r : TailRead) :
    Option ChainsData :=
  dataOf (Key.tailPublic k table) (Key.oneTime k.oneTime) (Key.startOf k.oneTime)
    (k.oneTime.describe table) key 0 r

/-- The data of a proof file's three chains that were read: dataOf at the letters at which
readProofChains calls readThree. further: the table of the stored copy; entry: that copy's number;
item: the request's item; words: the request file's own bytes; block: the first chain's block. item
and words are both strings of bytes: a swap is no error of types. -/
def proofDataOf (c : Params.ProofChains) (further : Params.TableName) (entry : Nat)
    (item words : ByteArray) (block : Blk FirstEnd) (proof : ByteArray) (r : TailRead) :
    Option ChainsData :=
  dataOf (tailPublic c further) block (firstStart c.first)
    (c.first.describe further entry item words) proof entry r

end OnBytes.TieK
