-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/M1EngineTyped.lean: the programs' own proof files of the first toy: the lists of files, and the
expected outcome of a run on each file, as data.

The programs (the C++ implementation that comes with this Lean code) make proof files of the first
toy (a product test). This file lists the files that the enclosed tools make, at three sets of
parameters: tiny parameters, tiny parameters with a repeated position (under a key at which one
position is drawn twice), and full parameters (the toy's full sizes). There are 3 honest proofs, 39
altered copies and 26 false proofs. For each file it records the expected outcome of a run of the
compiled verifier on it. A run function maps a file to an outcome; the outcome names the first stage
that refuses (the limits on the description, the reader or the verifier), or "accepted". These lists
are compared here with the reasons that came with the files. No file is run here. The runs, at the
four run functions with typed oracle functions and pruned openings, are in Run/M1EngineTypedT.lean,
Run/M1EngineTypedR.lean and Run/M1EngineTypedF1.lean to Run/M1EngineTypedF4.lean; the other run
functions have files of their own (Run/M1EngineOne*.lean and others).

Sources. The archive in which the files came has the sha256
f97d6774317660e9033841ab36ce4e63e376ebeb25542cf6f1f92e8f61644aa1 (the archive is not in this
repository). The files with the bytes (Fmt/M1ProgPTFiles.lean: tiny parameters;
Fmt/M1ProgPRFiles.lean: tiny parameters with a repeated position; Fmt/M1ProgPFFiles.lean: full
parameters) test each file's size and a hash of the format over it, against values that were made
while the file's sha256 was compared with the archive's own list of sums. The files are the
programs' own, made by the programs' own provers on a CPU (their "CPU engine") from made-up toy
data, in the format of the format page (docs/format/FORMAT.md, which comes with the programs; here
in an edition that is not the one that ships). With each bad file came the check at which the
programs' two verifiers
refuse it; for the false proofs (by cheating provers) it was written down before they were made,
and by the word that came with the files they fall only at the last block. The lists of outcomes
below were made by a program from runs of the four run functions; no name was typed in. Earlier
archives of such files had other bytes (the prover's coins differ). Which copies fall under "either
may refuse" depends on the bytes, and was different there. Those earlier files are not in this
tree.

1. What the file contains.
   `filesT`, `filesR`, `filesF`: name, bytes and part of each file. Part 0: the honest proof. 1:
     form. 2: proof of work. 3: openings. 4, 5: the last block's two checks. 6: the altered copy in
     which the last round's shown word is changed (two checks fail; see the head of
     Run/M1RunAll.lean).
   `strictOf`: the outcome, file by file, behind the strict reader (this library's rendering of the
     format page's verifier up to its decision: it checks form, proof of work and openings itself;
     `runStrictSP`, `runStrictS`), from the parts alone.
   `laxOf`, `laxT`, `laxR`, `laxF`: the outcome, file by file, behind the lenient reader (it only
     cuts the file into its parts; to cut the file, the lenient reader recomputes the hash chain,
     and it refuses some files (what it still asks the hash, what it refuses and what it does not
     test: part 1 of the head of Run/ParseLax.lean); it tests no proof of work, walks no path and
     compares no root: behind it the compiled verifier makes these checks itself; `runLaxSP`,
     `runLaxS`; "lax" in names).
   `byLuckT`, `byLuckR`, `byLuckF`: the copies in which a byte in front of a round with work is
     altered and the test of the work is then passed by luck. By the tables that came with the
     files, both of the programs' verifiers refuse such a copy at the opening behind (part 3). In
     these files there is none.
   `fits`: a list of outcomes names the files in their order, and each outcome is one that is
     allowed (`may`, Run/M1RunAll.lean; a file named in a byLuck list counts as one of part 2).

2. What is checked when the file compiles (on the data only).
   The lists' lengths, part by part.
   The parameter bytes of the two descriptions (`Theirs.specTiny`, for both tiny sets, and
   `Theirs.specFull`; Fmt/M1TheirsSpec.lean) are the bytes that came with the files. The generic
   construction's limits (`PQ.ok`) and the test of the queries' encoding (`OKQ`) hold at both
   descriptions.
   Every list of outcomes fits. So in it the honest proof alone is accepted; every false proof is
   refused by the verifier; and, behind the lenient reader, every copy with an altered opening (the
   copies 8, 9, 10 at each set of parameters) is refused by the verifier.
   How many files the verifier itself refuses behind the lenient reader: tiny 21, with a repeat 4,
   full 12.
   Where either stage may refuse (work; the shown word; a copy of a byLuck list), behind the
   lenient reader, the verifier refuses (there the file can still be cut) copy 3 (tiny), copy 7
   (with a repeat) and none (full). At all others the reader refuses: the chain changes, other
   positions are drawn, and the openings in the file have not the length that these ask for.

3. Theorems. None.

Notation: T, R, F at the end of a name: tiny parameters, tiny parameters with a repeated position,
full parameters.

4. What is not claimed.
   Not "the scheme's verifier", and no statement on soundness follows from these runs. At these
   descriptions the interface's external index has length 0, and what a compiled theorem says of an
   accepted string is empty (Run/M1Door.lean).
   Not "the programs' verdict": the decision is this library's rendering of the programs'
   description of the toy, compared with the nineteen values that the programs' tool prints beside a
   proof (`valuesF`,
   Fmt/M1Full.lean) and with these files.
   The runs use typed oracle functions with BLAKE2b behind them. The run over a single oracle,
   through an encoding of the queries, is in other files.
   The run functions stand at the interface `LbS`, whose batch part is the protocol
   (Run/PlanQS.lean; the tag "onl"; `Compile.Batch.vBS`; the equations vbs_*, vbsP_*, vbsPF_*). The
   wirings V* and W* (Run/M1RunTieTheirs.lean; W* also in Run/M1RunTieP.lean) and the conditions of
   W* are stated at the interface `LtS`, whose test part is the protocol. Their field T is the field
   B of the run functions' wiring (Run/PlanQS.lean: `Wb`). What is met at `LbS`, and what is not, is
   in Run/BatchDoor.lean (`metB`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.M1RunAll
import Fmt.M1ProgPTFiles
import Fmt.M1ProgPRFiles
import Fmt.M1ProgPFFiles
import Fmt.M1TheirsSpec
import Run.PageQ

set_option autoImplicit false

namespace Run.M1EngineTyped
open _root_.Fmt.M1 Run.PQ Run.M1Run Run.M1RunAll

def filesT : List (String × ByteArray × Nat) :=
  ProgPT.table ++ ProgPT.refusedOnly.map fun x => (x.1, x.2, 6)
def filesR : List (String × ByteArray × Nat) :=
  ProgPR.table ++ ProgPR.refusedOnly.map fun x => (x.1, x.2, 6)
def filesF : List (String × ByteArray × Nat) :=
  ProgPF.table ++ ProgPF.refusedOnly.map fun x => (x.1, x.2, 6)

/-- the outcome behind the strict reader -/
def strictOf (files : List (String × ByteArray × Nat)) : List (String × Who) :=
  files.map fun x =>
    (x.1, if x.2.2 = 0 then .accepted else if x.2.2 = 4 ∨ x.2.2 = 5 then .verifier else .reader)

/-- the outcome behind a lenient reader; vs: the files of the parts 2 and 6 that the verifier
refuses; rs: the files of part 3 that the reader refuses -/
def laxOf (vs rs : List String) (files : List (String × ByteArray × Nat)) : List (String × Who) :=
  files.map fun x =>
    (x.1, if x.2.2 = 0 then .accepted
        else if x.2.2 = 1 then .reader
        else if x.2.2 = 2 ∨ x.2.2 = 6 then (if vs.contains x.1 then .verifier else .reader)
        else if x.2.2 = 3 then (if rs.contains x.1 then .reader else .verifier)
        else .verifier)

/-- the copies in which a byte in front of a round with work is altered and the test of the work is
then passed by luck: by the tables that came with the files they fall at the opening behind it
(part 3); the draws have changed, so behind a lenient reader either stage may refuse, as at part 2
-/
def byLuckT : List String := []
def byLuckR : List String := []
def byLuckF : List String := []

def laxT : List (String × Who) := laxOf ["altered-03"] byLuckT filesT
def laxR : List (String × Who) := laxOf ["altered-07"] byLuckR filesR
def laxF : List (String × Who) := laxOf [] byLuckF filesF

/-- the outcomes that a run function is to have -/
def pin (R : Road) (lax : List (String × Who)) (files : List (String × ByteArray × Nat)) :
    List (String × Who) :=
  if R.strict then strictOf files else lax

/-- a list of outcomes names the files in their order, and each is one that is allowed; a file of
part 3 that is named in luck counts as one of part 2 -/
def fits (strict : Bool) (luck : List String)
    (files : List (String × ByteArray × Nat)) (vs : List (String × Who)) : Bool :=
  vs.map (·.1) == files.map (·.1) &&
    (files.zip vs).all fun x =>
      (may strict (if x.1.2.2 = 3 ∧ luck.contains x.1.1 then 2 else x.1.2.2)).contains x.2.2

#guard (List.range 7).map (fun d => (filesT.filter fun x => x.2.2 == d).length) = [1, 3, 6, 3, 16, 1, 1] ∧ filesT.length = 31
#guard (List.range 7).map (fun d => (filesR.filter fun x => x.2.2 == d).length) = [1, 3, 6, 3, 0, 0, 1] ∧ filesR.length = 14
#guard (List.range 7).map (fun d => (filesF.filter fun x => x.2.2 == d).length) = [1, 3, 6, 3, 7, 2, 1] ∧ filesF.length = 23
#guard Theirs.specTiny.params = ProgPT.params ∧ Theirs.specTiny.params = ProgPR.params ∧ Theirs.specFull.params = ProgPF.params
#guard PQ.ok Theirs.specTiny ∧ OKQ Theirs.specTiny ∧ PQ.ok Theirs.specFull ∧ OKQ Theirs.specFull
#guard fits false byLuckT filesT laxT ∧ fits false byLuckR filesR laxR ∧ fits false byLuckF filesF laxF
#guard fits true [] filesT (strictOf filesT) ∧ fits true [] filesR (strictOf filesR) ∧ fits true [] filesF (strictOf filesF)
-- a list of exceptions names files of part 3 alone; where it is not empty it is needed
#guard [(byLuckT, filesT, laxT), (byLuckR, filesR, laxR), (byLuckF, filesF, laxF)].all fun x => ((x.2.1.filter fun f => x.1.contains f.1).all fun f => f.2.2 == 3) && (x.1.isEmpty || !(fits false [] x.2.1 x.2.2))
-- the honest proof alone is accepted
#guard [laxT, laxR, laxF, strictOf filesT, strictOf filesR, strictOf filesF].all fun vs => (vs.filter fun v => v.2 == .accepted).map (·.1) == ["proof"]
-- how many files the verifier itself refuses: behind a lenient reader; behind the strict one (the false proofs)
#guard [laxT, laxR, laxF].map (fun vs => (vs.filter fun v => v.2 == .verifier).length) = [21, 4, 12]
#guard [strictOf filesT, strictOf filesR, strictOf filesF].map (fun vs => (vs.filter fun v => v.2 == .verifier).length) = [17, 0, 9]
-- `fits` refuses a wrong list
#guard fits false byLuckR filesR (laxOf [] [] filesR |>.map fun v => (v.1, Who.accepted)) = false ∧ fits true [] filesR laxR = false

end Run.M1EngineTyped
