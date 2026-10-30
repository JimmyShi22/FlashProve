-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/ToyOne.lean: a small toy of this library's own (`Run.Toy1`; on bytes: Fmt.Toy1) over the single
oracle: the compiled verifier of one slot (`Compile.Batch.verifyOneProtocol`, its term untouched), put over a
single oracle on bit strings by the encoding of the queries with its inverse and both laws (`mT`,
Run/ToyCode.lean), run with BLAKE2b as that oracle (`oBits`, Run/OracleBits.lean), on a file made
outside Lean.

Definitions that compute, with tests; one theorem (`runOne_eq`), and a lemma on a length
(`cfgT_size`).
The toy is this library's own, and so is the file (made by the format page's own reference program,
in an edition that is not the one that ships): not the programs'.

Main names:
  `needT`: which blocks of an answer the toy's verifier reads: round 0 and round 2: the chain value
    alone; round 1: all three; a leaf, a node: the one.
  `runOne c file`: the lenient reader at the format's hash; then `(Toy1.V ..).overOneN mOne needT`,
    run at `oBits` (by `OComp.detB`, Run/DetBytes.lean: the same value as `OComp.det`, each answer's
    hash computed once).
  `runOneAll c file`: the same with all blocks asked (`OComp.overOne`): a control.
  `runOne_eq`: the run over the single oracle is the run at the typed oracle functions that the
    encoding of the queries reads out of it (Run/DetOverOne.lean).

Tests (#guard). On all 21 files of this library's own small toy (Fmt/Toy1Files.lean): the two
honest files are accepted; the 19 altered ones are refused: eleven by the verifier itself (03, 04,
05, 06, 07, 08, 11, 16, 17, 18, 19), eight by the lenient reader before it (01, 02, 09, 10, 12, 13,
14, 15) [the files as made at that edition of the format page]. Both ways of asking
give the same verdicts, file by file. Also flips of single bytes of the first honest file, as in the
run with typed oracle functions (Run/ParseToy1.lean).

Limits: tried once outside this file, not a test here (the run at `famOf`, Run/CodingFn.lean,
computes a hash anew for every bit read, and takes minutes; `runLax` is written at `famFast`,
Run/CodingFast.lean): on all 21 files the verdicts are those of Run/ParseToy1.lean's `runLax`; on
the first honest file every typed query of the verifier is one that the format writes
(`OComp.askedOK` at Run/CodingAgree.lean's `fitsC`: true). This file's last test lists the 21
outcomes, and the tests of Run/ParseToy1AllLa.lean, Run/ParseToy1AllLb.lean and
Run/ParseToy1AllLc.lean list the same 21 for `runLax`; no test sets the two lists side by side.
The toy and the file are this library's own, not the programs'. The reader calls the format's hash
directly, not through the single oracle. Tests leave no theorem. This file says nothing on
soundness.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
import Run.ParseToy1
import Run.ToyCode
import Run.OracleBits
import Run.DetOverOne
import Run.DetBytes
import Run.DetAlong
import Fmt.Rules23Laws
import Fmt.Toy1Files

set_option autoImplicit false

namespace Run.Toy1
open Iop Rom Compile Compile.Batch

theorem cfgT_size : cfgT.size = 32 := _root_.Fmt.size_H _ _ _ _ _

/-- The encoding of the queries at the toy's configuration. -/
def mOne : OracleCoding (spec 256 2 Lt) 256 := mT cfgT cfgT_size

/-- Which blocks the toy's verifier reads. -/
def needT : Need mOne
  | .fb .test, q, j =>
    if (show FbIn 256 Lt .test from q).round = 1 then true else decide (j.val = 2)
  | _, _, _ => true

/-- The single oracle, into bytes. -/
def oB (s : List Bool) : ByteArray := _root_.Fmt.oracle (toBytes s)

/-- The verifier's run over the single oracle, the needed blocks alone asked. -/
def runOn1 (c : E3) (x : Option (List (Dig 256) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT))) : Who :=
  match x with
  | none => .reader
  | some (cms, π) => if ((V cms c π).overOneN mOne needT).detB oB then .accepted else .verifier

/-- The same, all blocks asked. -/
def runOnAll (c : E3) (x : Option (List (Dig 256) × OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT))) : Who :=
  match x with
  | none => .reader
  | some (cms, π) => if ((V cms c π).overOne mOne).detB oB then .accepted else .verifier

/-- The run over the single oracle. -/
def runOne (c : E3) (file : ByteArray) : Who :=
  runOn1 c (parseLaxW (m := Id) _root_.Fmt.formatHash (specOf c) T file)

def runOneAll (c : E3) (file : ByteArray) : Who :=
  runOnAll c (parseLaxW (m := Id) _root_.Fmt.formatHash (specOf c) T file)

/-- The run over the single oracle is the run at the typed oracle functions that the encoding of the
queries reads out of it, with the needed blocks asked and with all blocks asked. -/
theorem runOne_eq (cms : List (Dig 256)) (c : E3) (π : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto QT)) :
    ((V cms c π).overOneN mOne needT).detB oB = (V cms c π).det (readSome mOne needT oBits) ∧
    ((V cms c π).overOne mOne).detB oB = (V cms c π).det (readBlocks mOne oBits) :=
  ⟨(detB_oBits _).trans (det_overOneN mOne needT oBits _),
    (detB_oBits _).trans (det_overOne mOne oBits _)⟩

end Run.Toy1

open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) file == .accepted
open Run Run.Toy1 Run.ParseEx in
#guard runOneAll (1, 2, 3) file == .accepted
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 4) file != .accepted
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) (flip file 72) == .verifier && runOneAll (1, 2, 3) (flip file 72) == .verifier
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) (flip file 96) == .verifier && runOneAll (1, 2, 3) (flip file 96) == .verifier
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) (flip file 264) == .verifier && runOneAll (1, 2, 3) (flip file 264) == .verifier
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) (flip file 488) == .verifier && runOneAll (1, 2, 3) (flip file 488) == .verifier
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) (file.extract 0 511) == .reader && runOne (1, 2, 3) (file ++ _root_.Fmt.zeroBytes 1) == .reader
open Run Run.Toy1 Run.ParseEx in
#guard runOne (1, 2, 3) (setWord file 72 18446744069414584321) == .reader

-- the 21 files of the toy (Fmt.Toy1.files): the verdicts over the single oracle, needed blocks
-- asked; the same with all blocks asked; accepted exactly where the table that came with the files
-- says so; eleven refused by the verifier
open Run Run.Toy1 in
#guard
  let a := _root_.Fmt.Toy1.files.map fun f => runOne (1, 2, 3) f.2.1
  let b := _root_.Fmt.Toy1.files.map fun f => runOneAll (1, 2, 3) f.2.1
  a == [.accepted, .accepted, .reader, .reader, .verifier, .verifier, .verifier, .verifier, .verifier, .verifier, .reader, .reader, .verifier, .reader, .reader, .reader, .reader, .verifier, .verifier, .verifier, .verifier]
    && b == a && (a.map fun w => w == .accepted) == (_root_.Fmt.Toy1.files.map fun f => f.2.2.isNone) && (a.filter fun w => w == .verifier).length == 11
