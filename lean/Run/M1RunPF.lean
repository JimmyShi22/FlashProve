-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1RunPF.lean: the first toy at the programs' full parameters (the toy's full sizes), on files of
this library's own, through the compiled verifier with challenges as hash blocks, with the real
hash.

Tests only. The first toy is a product test. The programs are the C++ implementation that comes
with this Lean code. There are two choices of what a round's verifier message is: as sampled values
(`ck`: the values that the format draws, field elements and positions among them) or as hash blocks
(`ckP`: the round's 256-bit blocks themselves; reads and decision apply the sampling rule). Here it
is the second ("pull" in names). The run functions are `runStrictSP` and `runLaxSP`
(Run/PlanQSP.lean). What runs behind the file reader is, by the theorem of Run/M1RunTieP.lean at
this very description (`KnownF.spec`), the library's `vBS`, run by `det` at typed oracle functions
with BLAKE2b behind them; and there the protocol's wiring obeys the library's conditions on a
wiring, also where 27 of the 30 rounds draw field elements. The decision is `Fmt.M1.dec`.

1. What the file contains. No definition. What is asked, and the files, are those of
Run/M1RunF.lean: the same list `filesF` (13 files of some 161,000 bytes).

2. What is checked when the file compiles. The honest file is accepted behind both readers. On
every file the outcome is the one that the table asks for, behind both readers. So, file by file,
it is the outcome of the run with challenges as sampled values. The three re-cut files: behind the
lenient reader the verifier refuses.

3. Theorems. None. The tests are evaluations made when the file is compiled: they leave no theorem.

4. What is not claimed.
   No proof file of the programs is run here: the files are this library's own.
   The runs are at typed oracle functions, not over a single oracle through an encoding of the
   queries.
   That the two choices give one outcome on every file is, behind the lenient reader and under
   tests that can be run, a theorem elsewhere (`run_two`, Run/PageIsRun.lean). Behind the strict
   reader it is not shown.
   No statement on soundness follows.
   The run functions stand at the interface `LbS`, whose batch part is the protocol
   (Run/PlanQS.lean; the tag "onl"; `Compile.Batch.vBS`; the equations vbs_*, vbsP_*, vbsPF_*). The
   wirings W* (Run/M1RunTieP.lean) and their laws are stated at the interface `LtS`, whose test part
   is the protocol. Their field T is the field B of the run functions' wiring (Run/PlanQS.lean:
   `Wb`). What is met at `LbS`, and what is not, is in Run/BatchDoor.lean (`metB`).

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQSP
import Run.M1RunF

namespace Run.M1RunPF
open _root_.Fmt.M1 Run.PQ Run.M1Run Run.M1RunF

#guard runLaxSP KnownF.spec (dec KnownF.par) FilesF.honest = .accepted
#guard runStrictSP KnownF.spec (dec KnownF.par) FilesF.honest = .accepted
#guard wrong runLaxSP wantLax KnownF.spec KnownF.par filesF = []
#guard wrong runStrictSP wantStrict KnownF.spec KnownF.par filesF = []
#guard FilesF.recut.map (fun x => runLaxSP KnownF.spec (dec KnownF.par) x.2.1) = [.verifier, .verifier, .verifier]

end Run.M1RunPF
