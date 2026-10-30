-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/TestRecordToyCompiled.lean: the compiler's verifier of the link, run on the programs'
toy entry file. Definitions, two theorems, tests.

An entry file is a file of the programs (the C++ implementation that comes with this Lean code). It
holds a proof that a further committed copy of a table has the same rows as the first table. The
proof's protocol, the link, is made non-interactive by a hash chain ("the chain"). It opens three
Merkle trees of its own and two stored trees: the first table's, whose root comes from the key
file, and the copy's, whose root stands in the entry file. Each table has a record, its own
out-of-domain sample: seeds, which are drawn from the table's name, and the stored answers to them,
which stand in the key file and in the entry file.
OnBytes/Entry/TestRecordToy.lean judges the toy entry file, altered copies of it and stored false
entries by Entry.check, a verifier on bytes that calls nothing of the library's compiler. Beside
each file it holds the name of the check that refuses it ("the held name"). This file and three
companions (TestRecordToyCompiledLenient.lean, TestRecordToyCompiledFalse.lean,
TestRecordToyCompiledFalseLenient.lean) judge the same files, and a fourth
(TestRecordToyCompiledSplice.lean) splices and another record, by the verifier that the library's
compiler makes of the protocol. Why: the theorems on compiling speak of that verifier. A drift of
the typed protocol, its wiring, the typing of a file or the spelling of typed queries as hash calls
away from what the programs hash and send is what these tests are there to notice, as far as these
files exercise it.

How a file is judged (`run`; `voice` is `run` under the key file's first table). The stages run in
this order.
   (a) The parameters: `Params.Link.read` on the programs' parameter bytes.
   (b) The head: `entryPlaceR` (OnBytes/Tie/EntryWithRec.lean) compares eight bytes, takes the
       copy's root and its record's answers, draws both records' seeds, and makes the link's
       verifier on a view (a `Blk`, "the block"), the chain's description and the byte at which the
       chain begins.
   (c) The description in the compiler's form: `descr`. Its statement is a function of the two
       roots and holds both records' answers. The limits `XD.ok` (Run/PlanQXRun.lean) are tested.
   (d) The reader of the chain. Strict: `Fmt.wholeChainXF` checks form, hash chain, proof of work
       and every Merkle opening itself. Lenient: `Run.laxWholeX` (Run/ParseLaxX.lean) cuts the file,
       checks the form of its parts and recomputes the hash chain as far as cutting needs. It tests
       no proof of work, hashes no leaf, walks no path and compares no root.
   (e) The typing: `toBPrfX` (Run/PlanQX.lean) turns what the reader holds into a proof string of
       the library's type.
   (f) The compiled verifier: `VXK` (Run/PlanQXFast.lean), under the two roots. Its typed oracle
       queries are answered by BLAKE2b on the format's strings (`famX`, Run/PlanQXRun.lean). A
       query, or a block of an answer, that has no spelling as a call of the format's hash gets a
       constant answer. The protocol's decision is the block's (`Blk.decides`).
   The outcome is one of: limits (c), reader (b, d or e refuses), verifier (f refuses), accepted.
   There is no outcome (`none`) if the link's parameter bytes, the key file's three or the key
   file's head cannot be read.
   The strict reader tests every opening before the compiled verifier sees it. Behind the lenient
   one the compiled verifier's run is the first to test work, leaves, paths and roots, two of the
   roots stored, on the programs' bytes.

Two controls. Neither is a verifier.
   `Taken.decision`: the same stages with the decision replaced by "always yes". What it accepts has
     every hash, proof of work, point of form and Merkle path right for the compiled verifier.
   `Taken.acceptance`: the protocol's whole acceptance replaced by "always yes" (`PY`). The
     acceptance of `skeletonOverBothExternalStrings` (Run/PlanQX.lean) is a conjunction of four: every round's proof of work
     passes; every part of a round's draws has the length that the description says; every symbol
     read from a stored table carries the position at which it was read; the decision. Where this
     control still answers "verifier", a check that the compiler adds to the protocol refuses (among
     them: the form of the typed string, the leaves, the paths, the roots). The proof of work is
     not among them: it is tested inside the acceptance.

Sources. The files are those of OnBytes/Entry/RecordToyFiles.lean, the altered copies and the names
held beside them those of OnBytes/Entry/TestRecordToy.lean: made-up toy data, no model and no
weights. `wqY` and `VY` repeat the texts of `wqX` and `VPX` (Run/PlanQX.lean) at `PY`. The expected
numbers of the tests on the description are those of the programs' parameter bytes, by the format's
spelling of a plan and of the item "the link"; `word` and `names` read them off these bytes without
the library's reader of parameters.

1. What is checked when the file compiles (#guard).
   The parameter bytes: 20 entries, the first of them RECORD, which is no round; LINK is round 3,
   counted from 0, with 152 positions below 2 ^ 14; the item "the link" gives logN 14, 2 ^ 3 rows,
   1 answer a row, and 76 opened columns of each table.
   The description at the honest file: within the limits; 19 rounds, with the names that the bytes
   hold; round 3 gives its first 76 drawn positions to the first table and the other 76 to the copy;
   stored trees of depth 14; its statement at (the root in the key file, the root in the entry
   file) is the programs' statement, byte for byte; the chain begins behind eight answers of 24
   bytes, at byte 232. Its parameter bytes are the programs': these are handed through from stage
   (a), so this test would only notice an exchange.
   The honest file: accepted behind either reader, and by both controls behind the lenient one.
   Behind the strict reader: each altered copy whose held name is of the head, of form, of work or
   of an opening is refused by the reader. So is the honest file under a first table whose root has
   bit 0 turned: that root stands in the statement, which enters the hash chain in front of every
   draw, so the file's proof of work and openings do not fit it. Copy 08 has no held name, because
   the programs' reader and Entry.check name different first checks there; it is held to be refused,
   by whichever stage.

2. Theorems.
   `compiled_is`: stage (f) is the run of `Compile.Batch.verifyOneProtocol` at the tag "link", at the
     protocol `skeletonOverBothExternalStrings` of the description, under the two roots, at the typed oracle functions
     `famX`: for every first table, every head of an entry file and every decision.
   `control_is`: what the second control runs is the run of `verifyOneProtocol` at `PY` and `wqY`, at the
     typed oracle functions `famXK` (equal to `famX` at the format's hash: `famXK_eq`,
     Run/PlanQXFast.lean): for every description and decision.

3. What is not claimed.
   What runs is `verifyOneProtocol` of Compile/Batch (of the library's two forms of the compiler the first;
   the second is OnBytes/TypedOracleCompiler/Compile/Batch), at a protocol that takes no instance (its type of
   instances is Unit). So there is one protocol for each pair of records. The records stand inside
   the statement (the answers) and inside the decision (answers and seeds); they are not an instance
   of the protocol, and the seeds are drawn in stage (b), not by a typed query. The copy's answers
   reach the verifier through the description, which is made of the file's own bytes. It is not the
   verifier of the link inside `innerCompiledVerifier` (Johnson/Top/InnerCompiledVerifier.lean). That one stands over the
   second form (Johnson/TypedOracleCompiler/RecCompile): there the answers stand in the first query's list and the
   seeds are drawn by typed queries. No theorem here joins the two.
   The decision is the same `Blk.decides` that Entry.check asks. So the tests on false entries are
   no second test of the decision. What differs is the view on which it is asked: here the one that
   the protocol makes of the typed string (`viewX`, Run/PlanQX.lean).
   The key is not verified: of the key file only the head is read, for root and answers.
   The tests are evaluations made while the file compiles. The compile fails if a result moves. They
   leave no theorem on a run, and they show what is so at this toy's files and nothing beyond.
   Which check refuses a file is not shown: the compiled verifier answers one bit.
   That `toY` changes nothing but the type is read off its definition; no theorem says it. `PY` is
   not the Link of an interface: `VY` asks its queries in the types of the interface whose Link is
   the protocol with its acceptance.
   Nothing on soundness, completeness or hiding. The interface's encoding and decoder are
   placeholders (`XD.L`, Run/PlanQXRun.lean).
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).
-/
import OnBytes.Tie.EntryWithRec
import OnBytes.Tie.StoredMain
import OnBytes.Entry.TestRecordToy
import Run.ParseLaxX

set_option autoImplicit false

namespace OnBytes.Tie.RecordToyCompiled
open Rom Iop Compile Compile.Batch _root_.Run _root_.Run.PQ
open OnBytes.Entry.RecordToy (entryParameters entryFile keyFile firstTable copies flipAt)

/-! ## The run function -/

/-- The parameters of the link, read from the programs' parameter bytes. -/
def link : Option Params.Link := Params.Link.read entryParameters

/-- The description in the compiler's form: the chain's description as the entry's head gives it,
with the statement as a function of the two roots. The two records' answers stand in it. -/
def descr (first : Params.TableName) (pl : EntryPlace) : XD :=
  xdOf pl.spec (Tie.entryStatement first pl.further)

/-- Which reader stands in front of the compiled verifier. -/
inductive Reader where
  | strict
  | lenient

/-- What a control takes out of the protocol. -/
inductive Taken where
  | nothing
  | decision
  | acceptance

/-- The chain's bytes, read. -/
def readBy (rd : Reader) (S : Fmt.SpecX) (rest : ByteArray) : Option Fmt.ChainOut :=
  match rd with
  | .strict => Fmt.wholeChainXF S rest
  | .lenient => laxWholeX (m := Id) Fmt.HF S rest

/-- The link's protocol with its whole acceptance replaced by "always yes". Shape, reads and
annotations are those of `skeletonOverBothExternalStrings`. A control's protocol, not a verifier's. -/
@[reducible] def PY (D : XD) (dec : View → Bool) : Twin.PS Unit (twoExternalStrings (2 ^ D.a) SgX) :=
  { skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec with accept := fun _ _ _ => true }

/-- The wiring: the five components of `wqX` (Run/PlanQX.lean), at `PY`. -/
def wqY (D : XD) (dec : View → Bool) : ProtocolQueryLayout 256 (D.K + 1) (PY D dec).up :=
  ⟨(wire0S D.C D.K (chalP D.base.plan.field D.K),
      wiresSL D.C D.K (chalP D.base.plan.field D.K) D.ds),
    weX D.a, decOS D.C D.ds, nOpen D.ds + (D.xs.map (·.count)).sum, max (maxDepth D.ds) D.a⟩

/-- A typed string of the link as a typed string at `PY`, field by field. -/
def toY (D : XD) (dec : View → Bool) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up) :
    OneProtocolProof 256 (PY D dec).up :=
  ⟨π.salt, π.roots, π.plains, π.opens, π.ext, π.rtreq, π.slot, π.path⟩

/-- The evaluable form of the compiled verifier at `PY`: the text of `VPX` (Run/PlanQX.lean) with
`PY` and `wqY` in the place of `skeletonOverBothExternalStrings` and `wqX`, at the typed oracle functions of `VXK`. -/
def VY (D : XD) (dec : View → Bool) (r0 r1 : ByteArray) (π : OneProtocolProof 256 (PY D dec).up) : Bool :=
  Thin.verifyPX (lam := 256) (K := D.K + 1) (fun _ => D.L dec) (famXK D dec (D.K + 1))
    (Thin.maskOf (Thin.idx2 (2 ^ D.a))) (Thin.maskBit (Thin.idx2 (2 ^ D.a))) id none
    (256 + 8 * D.base.plan.salt) 256 .link (PY D dec) (wqY D dec)
    (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
    (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ())) (fun _ => none)
    (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π

/-- Behind the entry's head: limits, reader, typing, compiled verifier. With sharp, as the second
control asks, the compiled verifier is the one at `PY`. -/
def judge (rd : Reader) (sharp : Bool) (D : XD) (dec : View → Bool) (r0 r1 rest : ByteArray) :
    Who :=
  if D.ok then
    match (readBy rd (D.atR r0 r1) rest).bind
        (toBPrfX D.base.plan.salt D.base.cfg D.C D.ds D.a D.xs dec) with
    | none => .reader
    | some π =>
      if (if sharp then VY D dec r0 r1 (toY D dec π) else VXK D dec r0 r1 π) then .accepted
      else .verifier
  else .limits

/-- From an entry file, under a first table, to an outcome. -/
def run (rd : Reader) (tk : Taken) (first : Params.TableName) (file : ByteArray) : Option Who :=
  link.map fun p =>
    match entryPlaceR recordSeeds p first file with
    | none => .reader
    | some pl =>
      let rest := file.extract pl.byte file.size
      match tk with
      | .nothing =>
        judge rd false (descr first pl) (pl.block.decides (Entry.start p)) first.root
          pl.further.root rest
      | .decision => judge rd false (descr first pl) (fun _ => true) first.root pl.further.root rest
      | .acceptance =>
        judge rd true (descr first pl) (pl.block.decides (Entry.start p)) first.root
          pl.further.root rest

/-- The outcome under the first table of the programs' key file. -/
def voice (rd : Reader) (tk : Taken) (file : ByteArray) : Option Who :=
  firstTable.bind fun t => run rd tk t file

/-- Refused, by the reader or by the compiled verifier. -/
def refused (w : Option Who) : Bool := w == some .reader || w == some .verifier

/-! ## What runs is the compiler's verifier -/

/-- States that the evaluable form `VXK` at a description and a decision is the run of
`Compile.Batch.verifyOneProtocol` at the tag "link", at the protocol `skeletonOverBothExternalStrings` of the description, under the
two roots, with the typed oracle functions that the format's hash induces (`famX`). -/
def IsCompiled (D : XD) (dec : View → Bool) : Prop :=
  ∀ (r0 r1 : ByteArray) (π : OneProtocolProof 256 (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up),
    VXK D dec r0 r1 π =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (skeletonOverBothExternalStrings D.C D.ds D.a D.xs dec).up
          (wqX D.C D.K (chalP D.base.plan.field D.K) D.ds D.a D.xs dec)
          (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
        (famX D dec Fmt.oracle (D.K + 1))

/-- What `judge` runs behind the typing, sharp being false, is the compiler's verifier: for every
first table, every head of an entry file and every decision. By `vxk_eq` (Run/PlanQXFast.lean) and
`vx_eq` (Run/PlanQXRun.lean). -/
theorem compiled_is (first : Params.TableName) (pl : EntryPlace) (dec : View → Bool) :
    IsCompiled (descr first pl) dec := fun r0 r1 π =>
  (vxk_eq (descr first pl) dec r0 r1 π).trans (vx_eq (descr first pl) dec r0 r1 π)

/-- What the second control runs is the run of `Compile.Batch.verifyOneProtocol` at `PY` and `wqY`. -/
theorem control_is (D : XD) (dec : View → Bool) (r0 r1 : ByteArray) (π : OneProtocolProof 256 (PY D dec).up) :
    VY D dec r0 r1 π =
      (verifyOneProtocol (lam := 256) (K := D.K + 1) (L := D.L dec) (256 + 8 * D.base.plan.salt) 256 .link
          (PY D dec).up (wqY D dec) (fun p s => some (.inr ⟨Tag.link, ⟨p, s⟩⟩))
          (embPX D.C D.ds D.a D.xs dec (fun _ _ p => (p.val, [])) (fun _ => some ()))
          (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π).det
        (famXK D dec (D.K + 1)) :=
  Thin.thin_ext Unit Unit 256 (D.K + 1) (D.L dec) (famXK D dec (D.K + 1)) Unit
    (twoExternalStrings (2 ^ D.a) SgX) (Thin.idx2 (2 ^ D.a)) (256 + 8 * D.base.plan.salt) 256 .link (PY D dec)
    (wqY D dec) _ _ (fun _ => none) (fun s => some (.inl s)) 0 [bytesToDig r0, bytesToDig r1] () π
    (Thin.idx2_inj (2 ^ D.a))

/-! ## The description at the honest file -/

/-- The first table and the head of the honest entry file. -/
def honest : Option (Params.TableName × EntryPlace) :=
  link.bind fun p => firstTable.bind fun t =>
    (entryPlaceR recordSeeds p t entryFile).map fun pl => (t, pl)

/-- The description at the honest file. -/
def D? : Option XD := honest.map fun x => descr x.1 x.2

/-- The word at a byte of the programs' parameter bytes. -/
def word (i : Nat) : Nat := (Fmt.wordAt entryParameters i).toNat

/-- The names of n entries of the plan, walked off the parameter bytes from byte i on. An entry is
spelled as its name's length (a word), the name, and eleven words. -/
def names : Nat → Nat → List ByteArray
  | 0, _ => []
  | n + 1, i => entryParameters.extract (i + 8) (i + 8 + word i) :: names n (i + 8 + word i + 88)

/-- The byte at which entry number n begins, walked from byte i on as `names` walks. -/
def entryAt : Nat → Nat → Nat
  | 0, i => i
  | n + 1, i => entryAt n (i + 8 + word i + 88)

/-- The rounds' names: the plan's entries without the entry RECORD, which is no round. -/
def roundNames : List ByteArray := (names (word 100) 108).filter (· != Fmt.ascii "RECORD")

/-- A held name of the head, of form, of work or of an opening: such a file falls to the strict
reader. -/
def ofReader (name : String) : Bool :=
  ["file-of-another-kind", "version-unknown", "reader-form", "bytes-left-over", "reader-work",
    "reader-opening"].contains name

/-- The first table of the key file with bit 0 of its root turned. -/
def otherFirst : Option Params.TableName :=
  firstTable.map fun t => { t with root := flipAt t.root 0 }

end OnBytes.Tie.RecordToyCompiled

open OnBytes.Tie.RecordToyCompiled OnBytes.Entry.RecordToy Run.PQ

-- the programs' parameter bytes: 20 entries, the first is RECORD; LINK is round 3
#guard word 100 == 20 && (names 1 108) == [Fmt.ascii "RECORD"] && roundNames.length == 19 &&
  roundNames.idxOf (Fmt.ascii "LINK") == 3
-- the entry LINK, number 4, at byte 528: its eighth and ninth words: 152 positions below 2 ^ 14
#guard entryAt 4 108 == 528 && names 1 528 == [Fmt.ascii "LINK"] && word (528 + 12 + 56) == 152 &&
  word (528 + 12 + 64) == 14
-- the item "the link" (192 bytes from byte 2456 to the end): logN 14, v = 3, 1 answer, 76 | 76
#guard entryParameters.extract 2440 2448 == Fmt.ascii "the link" && word 2448 == 192 &&
  entryParameters.size == 2456 + 192 && word 2456 == 14 &&
  word 2480 == 3 && word 2488 == 1 && word 2504 == 76 && word 2512 == 76

-- the description at the honest file lies within the limits
#guard D?.map (·.ok) == some true
-- 19 rounds, with the names in the parameter bytes
#guard (D?.map fun D => D.ds.length) == some 19
#guard (D?.map fun D => D.ds.map fun d => Fmt.ascii d.entry.name) == some roundNames
-- round 3 is cut 76 | 76; stored trees of depth 14
#guard (D?.map fun D => D.xs.map fun o => (o.round, o.which, o.from_, o.count)) ==
  some [(3, false, 0, 76), (3, true, 76, 76)]
#guard (D?.map fun D => D.a) == some 14
-- its parameter bytes are the programs' (handed through)
#guard (D?.map fun D => D.base.params == entryParameters) == some true
-- its statement at the two files' roots is the programs'
#guard (D?.map fun D => (D.atR (keyFile.extract 8 40) (entryFile.extract 8 40)).base.statement ==
  OnBytes.Entry.RecordToy.entryStatement) == some true
-- the roots under which the file is judged are these; the chain begins behind eight answers
#guard (honest.map fun x => (x.1.root == keyFile.extract 8 40,
  x.2.further.root == entryFile.extract 8 40, x.2.byte)) ==
  some (true, true, 40 + 24 * (2 ^ word 2480 * word 2488))

-- the honest file
#guard voice .strict .nothing entryFile == some .accepted
#guard voice .lenient .nothing entryFile == some .accepted
-- the two controls can say yes
#guard voice .lenient .decision entryFile == some .accepted
#guard voice .lenient .acceptance entryFile == some .accepted

-- the altered copies behind the strict reader
#guard copies.length == 12 && (copies.filter (·.2.2.isNone)).map (·.1) == ["08"]
#guard (copies.filter fun c =>
  match c.2.2 with
  | some name => !ofReader name || voice .strict .nothing c.2.1 != some .reader
  | none => !refused (voice .strict .nothing c.2.1)).map (·.1) == []
-- the honest file under another first root
#guard (otherFirst.bind fun t => run .strict .nothing t entryFile) == some .reader
