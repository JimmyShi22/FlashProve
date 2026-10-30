-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProg.lean: the compiled verifier (`Compile.Batch.verifyOneProtocol`), at the wiring with whole
paths and with BLAKE2b behind its oracles, on the programs' own proof files for the first toy. All
three honest proofs are accepted; all 39 altered copies and all 26 false proofs are refused, 37 of
the 65 by the verifier itself; both run functions give the same outcomes.

The first toy is a product test (on rows a, b, c with a_i b_i = c_i for every i; Fmt/M1Types.lean).
"The programs" are the C++ implementation that comes with this Lean code; "the format page" is
docs/format/FORMAT.md, which comes with the programs. This file only gathers the files with the
tests and states the count (in this comment alone: the file's Lean text is its imports).

Sources. The files were written by the programs, by their CPU prover; the false proofs by a version
of it in which one block cheats. They are the files that the enclosed tools make. They came in one
archive, sha256 f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1 (the archive is not
in this repository), which carries an edition of the format page that is not the one that ships;
their form is the same in a second edition, also not the one that ships. The bytes are in
Fmt/M1ProgPFFiles.lean, Fmt/M1ProgPTFiles.lean and Fmt/M1ProgPRFiles.lean, those of the false proofs
in Fmt/MustBeRefused/M1ProgPFa.lean to Fmt/MustBeRefused/M1ProgPFi.lean and
Fmt/MustBeRefused/M1ProgPT.lean; the head comment of each of these files says how its bytes are tied
to the archive's checksums. All data in them are made up.

1. What is run. A file goes to the parser that fills whole paths with real values. The files hold
   pruned openings; the parser hashes the opened leaves and walks up, so that each opened leaf gets
   an authentication path of its own. It compares no root and tests no proof of work. The resulting
   proof string goes to the evaluable form of the compiled verifier: that form is what runs. It is
   proved equal to the run of `Compile.Batch.verifyOneProtocol` at the description's protocol and the wiring
   with whole paths. The two theorems are `vpf_eq` (Run/PlanQSF.lean), with challenges as sampled
   values, and `vpfp_eq` (Run/PlanQSFP.lean), with challenges as hash blocks. `Compile.Batch.vBS` is
   the function that the scheme's verifier runs on the proof string of one slot of a batch. With
   challenges as hash blocks, and at the descriptions T, R, F of Run/M1RunTiePF.lean, that form is
   also proved equal to `vBS`, at an interface (`vbsPF_T`, `vbsPF_R`, `vbsPF_F`,
   Run/M1RunTiePF.lean). That interface is `LbS` (Run/PlanQS.lean), whose Batch protocol is the toy.
   The wiring of that one protocol meets the library's conditions on a wiring (`okgPF_T`, `okgPF_R`,
   `okgPF_F`, Run/M1RunTiePF.lean). These three are stated at the interface `LtS`, where that wiring
   is Test's. The same record is the field B of the wiring (`Wb`, Run/PlanQS.lean) at which the runs
   with challenges as hash blocks stand.

2. What is checked when the gathered files compile (#guard). The outcome of both run functions on
   every file, by name, compared with the tables that came with the files (Run/PlanQSFProgPFw.lean,
   Run/PlanQSFProgPTw.lean, Run/PlanQSFProgPRw.lean). The two run functions give the same outcome on
   all 68 files.
   Full parameters (23 files): the proof is accepted. Verifier: 12: the copies altered in an opened
   symbol, a salt, a given digest (8, 9, 10), and all 9 false proofs. Reader: 10: copies 1 to 7 (the
   hash chain moves, other positions are drawn, and the file no longer splits into the parts that
   they ask for) and 11, 12, 13 (form).
   Tiny parameters (31 files): the proof is accepted. Verifier: 21: copy 3 (here the file still
   splits, and the verifier's own tests refuse), 8, 9, 10, and all 17 false proofs. Reader: 9:
   copies 1, 2, 4 to 7, 11, 12, 13.
   Tiny parameters with a repeated position (14 files): the proof is accepted. Verifier: 4: copy 7
   (the file still splits), 8, 9, 10. Reader: 9: copies 1 to 6, 11, 12, 13.
   Which of the copies 1 to 7 still splits depends on the prover's coins. In an earlier set of the
   programs' files it was copy 5 at the tiny parameters; and there, with a repeated position, copy 3
   passed the six bits of proof of work by chance, so that the programs' own verifiers refused it at
   an opening, while here the file no longer split. A copy whose altered byte is in the hash chain
   can pass the proof of work by chance (six bits at the tiny parameters), so that the programs' own
   verifiers refuse it at an opening, while here the file no longer splits. The list `byLuck` in the
   three files named above is for such a copy; it is empty at these files.

3. Theorems. None in this file.

Notation: PF, PT, PR behind Prog in a file's name: full parameters, tiny parameters, tiny parameters
with a repeated position (these files' heads); _T, _R, _F at the end of a name:
Run/M1RunTiePF.lean's descriptions, T and R at tiny, F at full parameters.

4. What is not claimed. No statement on soundness follows. "The theorem's verifier", "the scheme's
   verifier" and "sound" may not be said of these runs (see the heads of Run/PlanQS.lean and
   Run/M1RunTiePF.lean). The formal conditions of the record `Met` (Run/M1Door.lean) on the whole
   interface and on its wiring are met, with challenges as hash blocks, at the descriptions T, R, F
   of Run/M1RunTiePF.lean. This is stated in Run/BatchDoor.lean and proved in
   Run/BatchDoorProofs.lean (`metBF_T`, `metBF_R`, `metBF_F`). At the interface `LtS` it is in
   Run/M1Door.lean (`metF_T`, `metF_R`, `metF_F`). The files with a repeated position are read under
   the description T. What is not met is told in part 4 of the heads of Run/BatchDoor.lean and
   Run/M1Door.lean. The two conditions on soundness hold there only at the relation "everything",
   where they are empty. Round-by-round knowledge soundness for a relation with content is shown
   nowhere in Run/ or Fmt/. The runs use typed oracle functions (those that a single oracle on the
   format's strings induces), not a single oracle through an encoding of the queries. The verifier
   answers one bit: which of its tests refused is not shown. Tests are evaluations made while a file
   compiles; they leave no theorem.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQSFProgPTa
import Run.PlanQSFProgPTb
import Run.PlanQSFProgPTc
import Run.PlanQSFProgPRa
import Run.PlanQSFProgPFa
import Run.PlanQSFProgPFb
import Run.PlanQSFProgPFc
import Run.PlanQSFProgPFd
import Run.PlanQSFProgPFe
import Run.PlanQSFProgPFf
import Run.PlanQSFProgPFg
import Run.PlanQSFProgPFh
