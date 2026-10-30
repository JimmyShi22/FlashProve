-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1EngineOneFW.lean: the programs' proof files for the first toy, at the full parameters, on the
compiled verifier over a single oracle.

The first toy is a product test followed by a proximity test. The programs (the C++ implementation
that comes with this Lean code) ship for it, at the full parameters (30 rounds), an honest proof of
160,520 bytes, 13 altered copies of it and 9 false proofs made by cheating provers. This file runs
one of three run functions on all 23 files. A run function maps a file to an outcome: the first
stage that refuses it, or "accepted". The honest proof is accepted and every other file is refused,
and the tests fix the outcome for each file.

Sources. The files come from the programs' archive of files with sha256
f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1 (the archive is not in this
repository). Their format is that of the format page (docs/format/FORMAT.md, which comes with the
programs) in an edition that is not the one that ships. The proofs were written by the programs' own
provers for this toy, on a CPU, by a script of the programs' tests; that script is not
in this repository. They hold made-up toy data: no model and no weights. The bytes are in
Fmt/M1ProgPFFiles.lean, those of the false proofs in Fmt/MustBeRefused/M1ProgPFa.lean to
Fmt/MustBeRefused/M1ProgPFi.lean; the head comment of each of these files says how its bytes are
tied to the archive's checksums. The altered copies are the archive's own; the false proofs were
made by its cheating provers. The strings of outcomes in the tests were obtained by evaluating these
same run functions once; a program refuses to write them into this file unless the honest proof is
accepted and nothing else is.

1. What the file contains.
   `S`, `d`: the description of the proof's hash chain (`Fmt.M1.Theirs.specFull`) and the decision
     (`Fmt.M1.dec` at `Theirs.sizesFull`). These are the names at which the theorems of
     Run/M1RunTieTheirs.lean are stated.
   The run functions. Each consists of a reader, which turns the file's bytes into a typed proof
   string, and the compiled verifier on that string. The compiled verifier is the verifier of the
   non-interactive argument that the compiler makes of an interactive oracle protocol: Merkle trees
   for the oracles, a hash chain for the challenges (`Compile.Batch.verifyOneProtocol`); proof of work is
   tested where the protocol's `accept` tests it, as here (`passSL` in `PSof`, Run/PlanQS.lean). The
   protocol, its wiring and the run functions are made from the description by the generic
   construction (Run/PlanQTypes.lean, Run/PlanQWire.lean, Run/PlanQPage.lean, Run/PlanQRun.lean,
   Run/PlanQS.lean, and for whole paths Run/PlanQSF.lean); nothing is written for this toy alone.
   What is evaluated is the evaluable form of the compiled verifier, proved equal to it (see 3). The
   compiled verifier makes all its queries to a single oracle on bit strings, through an encoding of
   the queries that is made from the description (`pageQ` in Run/PageQ.lean; it has an inverse, and
   both laws of an inverse are proved; a leaf and a node take one oracle call each,
   Run/CodingPageOne.lean). The oracle is BLAKE2b, used by the format's rules (Run/OracleBits.lean).
   `run1WPF`: whole paths: each opened leaf has an authentication path of its own, which is the form
     of the wirings in the compiler's top theorems. Its reader fills in these paths (`fullWhole`,
     Run/ParseFull.lean; the wiring: `wqSF`, Run/PlanQSF.lean). Challenges as hash blocks (`ckP` in
     Run/PlanPull.lean): a round's verifier message is the round's 256-bit blocks. The library calls
     the step from challenges as sampled values to challenges as hash blocks "pull".
   The main run function for this toy on the same files is in Run/M1EngineOneF.lean.

2. What is checked when the file compiles (#guard tests, run by Lean's evaluator).
   The description's parameters are the archive's, byte for byte, and the list of files has the
   expected length and names (of the false proofs: that they begin with "cheat-").
   The size tests that the theorems under 3 need hold at every file: `ok S`, `OKQ S` and
   `smallB S file` (Run/LaxDom.lean) for `run1PF` and `run1K`; `ok S`, `OKQ S` and `smallF S file`
   (Run/FullDom.lean) for `run1WPF` (each in the file that evaluates that run function).
   (`fourBounds S (kOf S)`, which `one_pull`, `one_ck` and `oneW_pull` need as well, is tested in
   Run/OneIsTypedTop.lean, not here.)
   The string of outcomes of each run function that this file evaluates.

3. Theorems. None is proved in this file.
   The interface. An interface is the library's record of three protocols, called Test, Link and
   Batch, with an encoding and a decoding of an index; the compiler's theorems speak of the
   verifiers at these three. The run functions stand at the interface `LbS`, whose Batch is the
   toy's protocol (Run/PlanQS.lean; the tag "onl"; the statement () in the first query). What ties
   the typed forms of the compiled verifier to `Compile.Batch.vBS` at (`LbS`, `Wb ..`): the heads of
   Run/M1RunTieTheirs.lean, Run/M1RunTiePF.lean; none of these statements is about a run function of
   this file, and none is over the single oracle. What ties the run functions over the single oracle
   to run functions on typed oracle functions: `one_pull` (`run1PF`, `runLaxSP`), `one_ck` (`run1K`,
   `runLaxS`) (Run/OneIsTypedTop.lean) and `oneW_pull` (`run1WPF`, `runFullSP`;
   Run/OneIsTypedFull.lean, proved in Run/OneIsTypedFullProofs.lean), each under `ok S`, `OKQ S` and
   `fourBounds S (kOf S)`. On a constant key string and a constant link string, `vBS` is the whole
   verifier of the scheme with batches at (`LbS`, `Wb ..`) (`batch_V`, `batch_arg` in
   Run/BatchS.lean).
   Take the protocol with challenges as sampled values and without proof of work. The library's own
   pull of it, then the library's step for proof of work, is the protocol with challenges as hash
   blocks (`planPull_proto`, Run/PlanPullProto.lean). The wiring with whole paths is the library's
   own wiring of a Test, then its step for proof of work (`planPull_wq`, Run/PlanPullWq.lean). The
   limits: the heads of these two files. Among them: the library's generic forms for Batch are other
   terms at a round with work, and no equation with them is stated. The equations for the whole
   interface and the whole wiring (Run/PlanPullFace.lean, Run/PlanPullJoin.lean [not in this library]) are about another
   interface, `LtS`, at which none of these run functions stands.
   The rest of part 3 is that of Run/M1EngineOneF.lean's head; it holds here too.

4. What is not claimed.
   No statement on soundness follows. The run functions here are not "the theorem's verifier". The
   scheme at (`LbS`, `Wb ..`) commits to nothing. On soundness Run/ has `lb_sound`
   (Run/BatchDoor.lean), at the interface, and the record `Met` (Run/M1Door.lean), at the pair.
   `metB` states `Met` under two premises on Batch's wiring; `metB_N`, `metB_M`, `metBF_T`,
   `metBF_R`, `metBF_F` state it without them, each at one closed description with challenges as
   hash blocks (Run/BatchDoor.lean, proved in Run/BatchDoorProofs.lean). None of the five is at
   `run1K`'s pair (challenges as sampled values), and `metB`'s premise `wB.OKG` is shown of that
   pair's wiring nowhere in Run/ (the head of Run/PageQRunC.lean, "Why"). `lb_sound` and `Met`'s
   fields `sound` and `low` are at the relation "everything" (`All`, Run/M1Door.lean) and are empty
   at this interface (the head of Run/BatchDoor.lean); `low` is the conclusion of `bcsSoundBatchG`
   (Compile/Batch/SpecSoundG.lean). Beyond these, and `batch_V`, `batch_arg` (see 3), no statement
   of Run/ names `Compile.Batch.argB` or `Compile.Batch.V`, has `BatchProtocol.Sound` or `BcsAt` at this
   interface, or has `Met` at this pair. For the language, the library's clause on an accepted proof
   string is true and empty here, because there is no index and the statement is empty
   (Run/BatchDoor.lean, by its head). The clause with content is the one on a witness. Nothing in
   Run/ or Fmt/ reaches it (Run/BatchDoor.lean, the head, 4). "The scheme's verifier" may be said
   only with the scheme named. No test here evaluates `Compile.Batch.V` itself; the tests evaluate
   the verifier for one proof behind a reader.
   It is not claimed that the decision is the one that the programs compute. It is a reading of the
   programs' description of the toy.
   It is not claimed that the wiring of `run1PF` and `run1K` is that of a top theorem: it has pruned
   openings, and `run1WPF`'s has whole paths. That (`LbS`, `Wb ..`) with whole paths is a top
   theorem's pair is not shown either (Run/BatchS.lean, the head).
   An outcome does not tell which check of the compiled verifier failed.
   The tests are evaluations. They leave no theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.PageQFull
import Run.LaxDom
import Run.FullDom
import Fmt.M1TheirsSpec
import Fmt.M1ProgPFFiles

set_option autoImplicit false

namespace Run.PQ.EngFW
open Run.PQ _root_.Fmt.M1

abbrev S : _root_.Fmt.Spec := Theirs.specFull
abbrev d : PQ.View → Bool := dec Theirs.sizesFull

/-- The honest proof first; then the altered copies and the false proofs, in the order of `further`
(Fmt/M1ProgPFFiles.lean). -/
def all : List (String × ByteArray) := ("proof", ProgPF.proof) :: ProgPF.further

/-- An outcome as a letter: A accepted; V refused by the compiled verifier; R refused by the reader;
L outside the limits of the generic construction or failing `OKQ`. -/
def sh : Who → Char
  | .accepted => 'A'
  | .verifier => 'V'
  | .reader => 'R'
  | .limits => 'L'

def voices (run : _root_.Fmt.Spec → (PQ.View → Bool) → ByteArray → Who) : String :=
  String.ofList (all.map fun x => sh (run S d x.2))

end Run.PQ.EngFW

open Run Run.PQ Run.PQ.EngFW _root_.Fmt.M1 in
#guard S.params.data == ProgPF.params.data && all.length == 23 && (all.map (·.1)).take 14 == ["proof", "altered-01", "altered-02", "altered-03", "altered-04", "altered-05", "altered-06", "altered-07", "altered-08", "altered-09", "altered-10", "altered-11", "altered-12", "altered-13"] && (all.drop 14).all fun x => x.1.startsWith "cheat-"
open Run Run.PQ Run.PQ.EngFW _root_.Fmt.M1 in
#guard ok S && OKQ S && all.all fun x => smallB S x.2
-- the size test that `full_HO` (Run/FullDom.lean) needs, for `run1WPF`
open Run Run.PQ Run.PQ.EngFW _root_.Fmt.M1 in
#guard all.all fun x => smallF S x.2
open Run Run.PQ Run.PQ.EngFW _root_.Fmt.M1 in
#guard voices run1WPF == "ARRRRRRRVVVRRRVVVVVVVVV"
