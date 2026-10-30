-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TieK/ReadThreeDefs.lean: one fixed reading of a file with three chains: the definitions.

The theorems on them are in OnBytes/TieK/ReadThree.lean, whose head says what
the reading is for.
The definitions stand in a file of their own, above the verifier program's own modules and
OnBytes/TieK/PlaceOpen.lean alone, so that a compiled program can call them.

Main names:
  `ChainsData`: the three descriptions with their rounds, the two dry ends, the three chains as
    read with the place and the table's key, the two seals, the salt and the siblings of the
    binding tree's leaf, and the number of the stored copy.
  `slotBytes`: the salt and the siblings of the binding tree's leaf.
  `readThree`: the reading, from the first chain's first byte on.
  `readKeyChains`: the reading of a key file, from the three public files and the key file's bytes.
  `furtherOf`: the table of an entry file, by the program's own readers.
  `readProofChains`: the reading of a proof file, from the files' bytes and the number of the stored
    copy.
Limits: it claims nothing on soundness. That `readThree` returns a value does not say that the
program says yes. The program does not import this file.

-/
import OnBytes.TieK.PlaceOpen
import OnBytes.Model.Verify

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.TieK
open OnBytes.Proof

/-- What one reading of a file's three chains gives. -/
structure ChainsData where
  rounds1 : Params.Rounds
  dry : FirstEnd
  S1 : Fmt.SpecX
  r : TailRead
  seal1 : ByteArray
  seal2 : ByteArray
  rounds2 : Params.Rounds
  dry2 : SharedEnd
  S2 : Fmt.SpecX
  rounds3 : Params.Rounds
  S3 : Fmt.SpecX
  /-- the salt of the binding tree's leaf -/
  salt : ByteArray
  /-- the siblings on that leaf's path, the leaf's first -/
  path : List ByteArray
  /-- the number of the stored copy on which a proof was made, as the proof file's head has it; 0 at
  a key file -/
  copy : Nat

/-- The salt and the siblings of the binding tree's leaf, which `Proof.readPlace` hashes and does
not keep. i: the place of the word in front of them. -/
def slotBytes (s : Params.LinBindingShape) (b : ByteArray) (i : Nat) :
    Option (ByteArray × List ByteArray) :=
  match Fmt.rdWord b i with
  | none => none
  | some (_, i1) =>
  match Fmt.slice b i1 s.saltBytes with
  | none => none
  | some salt => (pathAt b s.logLeaves (i1 + s.saltBytes)).map fun path => (salt, path)

/-- **The reading of three chains.** p: what is public about the tail; block1, start1: the first
chain's block and what it starts from; describe1: the first chain's description from its rounds; i:
the place of the first chain's first byte; copy: the number that is kept in the data. -/
def readThree (p : TailPublic) (block1 : Blk FirstEnd) (start1 : Start)
    (describe1 : Params.Rounds → Option Fmt.SpecX) (file : ByteArray) (i copy : Nat) :
    Option ChainsData :=
  match block1.dryRun start1 with
  | none => none
  | some (rounds1, dry) =>
  match describe1 rounds1 with
  | none => none
  | some S1 =>
  match readChain S1 [] file i with
  | none => none
  | some (o1, n1) =>
  match (⟨o1, viewOf S1 o1, n1⟩ : ChainRead).seal with
  | none => none
  | some seal1 =>
  match readPlace p.binding p.shared.given.cfg seal1 file n1 with
  | none => none
  | some place =>
  match slotBytes p.binding file n1 with
  | none => none
  | some (salt, path) =>
  match tableKey p.shared.given.plan.field p.shared.given.cfg p.lin.fold.index p.table 0 with
  | none => none
  | some key =>
  match (sharedBlock p.lin key).dryRun (sharedStart p) with
  | none => none
  | some (rounds2, dry2) =>
  match p.shared.describe p.lab₂ p.table place.root rounds2 with
  | none => none
  | some S2 =>
  match readChain S2 o1.seen file place.next with
  | none => none
  | some (o2, n2) =>
  match (⟨o2, viewOf S2 o2, n2⟩ : ChainRead).seal with
  | none => none
  | some seal2 =>
  match (secondBlock p.lin dry.lin (dry2.goesOn ⟨o2, viewOf S2 o2, n2⟩)).rounds
      (secondStart p dry ⟨o1, viewOf S1 o1, n1⟩) with
  | none => none
  | some rounds3 =>
  match p.second.describe p.lab₃ seal1 seal2 rounds3 (secondFirstTree ⟨o1, viewOf S1 o1, n1⟩) with
  | none => none
  | some S3 =>
  match readChain S3 o2.seen file n2 with
  | none => none
  | some (o3, n3) =>
    if n3 = file.size then
      some ⟨rounds1, dry, S1,
        ⟨⟨o1, viewOf S1 o1, n1⟩, place, key, ⟨o2, viewOf S2 o2, n2⟩, ⟨o3, viewOf S3 o3, n3⟩⟩,
        seal1, seal2, rounds2, dry2, S2, rounds3, S3, salt, path, copy⟩
    else none

/-- **The reading of a key file**, from the three public files and the key file's bytes: the table,
and the three chains' data. -/
def readKeyChains (pol lay KL key : ByteArray) : Option (Params.TableName × ChainsData) :=
  match Model.Verify.planned pol KL (some lay) with
  | .error _ => none
  | .ok p =>
  match Key.readTable p.chains.key.oneTime.lin.fold.index p.chains.key.oneTime.given.cfg key with
  | .error _ => none
  | .ok (table, j) =>
    (readThree (Key.tailPublic p.chains.key table) (Key.oneTime p.chains.key.oneTime)
      (Key.startOf p.chains.key.oneTime) (p.chains.key.oneTime.describe table) key j 0).map
      fun d => (table, d)

/-- The table of an entry file, by the program's own readers of the head and of a table's bytes. No
test is made on it. p: the parameters of the entry's chain. -/
def furtherOf (p : Params.Link) (ent : ByteArray) : Option Params.TableName :=
  match Proof.readHead p.given.plan.field .entry ent with
  | .error _ => none
  | .ok i =>
  match readTable p.given.plan.field (p.link.table.rows * p.link.table.answers) ent i with
  | .error _ => none
  | .ok x => some x.1

/-- **The reading of a proof file**, from the three public files, the request's and the reply's
bytes, the bytes of the entry file of the stored copy on which the proof was made, that copy's
number, and the proof file's bytes: that copy's table, and the three chains' data. -/
def readProofChains (pol lay KL request y ent : ByteArray) (entry : Nat) (proof : ByteArray) :
    Option (Params.TableName × ChainsData) :=
  match Model.Verify.planned pol KL (some lay) with
  | .error _ => none
  | .ok p =>
  match furtherOf p.chains.link ent with
  | none => none
  | some further =>
  match Model.Head.stFromCall (Model.Verify.words32 request) (Model.Verify.words32 y) p.X.T with
  | .error _ => none
  | .ok so =>
  match Model.Head.coveredOf so p.X.T p.X.P.h.V with
  | .error _ => none
  | .ok cov =>
  match Proof.requestItem pol KL request with
  | none => none
  | some item =>
  match Model.Verify.linksOf p.X cov with
  | .error _ => none
  | .ok links =>
  match readProofHead p.chains.proof.first.given.plan.field proof with
  | .error _ => none
  | .ok (copy, i) =>
    if copy = entry then
      (readThree (tailPublic p.chains.proof further)
        (firstBlock p.chains.proof.first
          (Model.Stages.runLinksH
            (p.built.links.zipWith (fun b l => { b with run := l.run }) links)
            p.chains.proof.first p.X.layers.wsLay) (Model.ofNat so.y))
        (firstStart p.chains.proof.first)
        (p.chains.proof.first.describe further entry item request) proof i copy).map fun d =>
          (further, d)
    else none

end OnBytes.TieK
