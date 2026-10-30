-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/G/ProofDefs.lean: the reading of a proof file's three chains with the hash as a letter
h: definitions. The like of OnBytes/TieK/G/KeyDefs.lean, whose head says why.

Letters. c: the parameters of a proof file's three chains. further: the table of the stored copy on
which the proof was made. entry: that copy's number. item: the request's item. words: the request
file's own bytes (the fourth item of the first chain's statement). block: the first chain's block.
None is made here: whoever calls has made them, the item and the parameters' digests at hashes of
its own choosing. item and words are both strings of bytes: a swap is no error of types.
 - `readProofChainsG h c further entry item words block file`: the three chains by the twin's reader
   at h
   (`M.Proof.readProof`), the rest of the data from these by `proofDataOf`
   (OnBytes/TieK/DataOf.lean), which calls no hash.
 - `ProofOpenedG h c further entry item words block file`: `ProofOpened`
   (OnBytes/TieK/PortChains.lean)
   without its clauses on the planner's return, the digests, the chains' parameter bytes, the file's
   size, and without the four equations by which request, reply and links are made: their values
   are the letters item, words and block.
 - `ProofGoodG h c further entry item words block d`: at some file, opened so, the reading returns
   d.

Not claimed. No law is here. The bound on the file's size is dropped with the rest: whoever needs
that the reader's calls lie in a hash's domain must bring it. At c := the planner's chains the
digest of the public files inside c is the program's hash's, whatever h is. Nothing on soundness.
The program does not import this file.

-/
import OnBytes.ChecksWithHashAsArgument.M.Proof.File
import OnBytes.TieK.G.KeyDefs

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK.G

open OnBytes.Proof OnBytes.TwoPort

/-- **The reading of a proof file at the hash h.** -/
def readProofChainsG (h : M.HashM Id) (c : Params.ProofChains) (further : Params.TableName)
    (entry : Nat) (item words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) :
    Option ChainsData :=
  match ((M.Proof.readProof (m := Id) h c further entry item words block file).fromStart :
      Except String TailRead) with
  | .error _ => none
  | .ok r => proofDataOf c further entry item words block file r

/-- The proof file's three chains as read and judged at the hash h. -/
def ProofOpenedG (h : M.HashM Id) (c : Params.ProofChains) (further : Params.TableName)
    (entry : Nat) (item words : ByteArray) (block : Blk FirstEnd) (file : ByteArray) : Prop :=
  ∃ i rounds1 dry S1 r seal1 seal2 rounds2 dry2 S2 rounds3 S3 real real2,
    (c.first.given.plan.field != .two || c.first.given.cfg == Fmt.zero32) = false ∧
    readProofHead c.first.given.plan.field file = .ok (entry, i) ∧
    c.first.describe further entry item words rounds1 = some S1 ∧
    ThreeChainsG h (tailPublic c further) block (firstStart c.first) file i rounds1 dry S1 r seal1
      seal2 rounds2 dry2 S2 rounds3 S3 real real2

/-- A good reading of a proof file at the hash h. -/
def ProofGoodG (h : M.HashM Id) (c : Params.ProofChains) (further : Params.TableName)
    (entry : Nat) (item words : ByteArray) (block : Blk FirstEnd) (d : ChainsData) : Prop :=
  ∃ file, ProofOpenedG h c further entry item words block file ∧
    readProofChainsG h c further entry item words block file = some d

end OnBytes.TieK.G
