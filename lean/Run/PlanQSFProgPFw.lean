-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFProgPFw.lean: the compiled verifier, with whole paths, on the programs' own proof files
for the first toy, at the full parameters (the larger of the toy's two sets of sizes, full and tiny:
`toyPar`, Fmt/M1Plan.lean). What is run, and which outcome agrees with the tables that came with the
files.

"The programs" are the C++ implementation that comes with this Lean code. The files, with the part
of the check at which each should be refused, are in Fmt/M1FullProgPFw.lean. "Whole paths" means
that each opened Merkle leaf has an authentication path of its own, the form of the wirings in the
compiler's top theorems; the files themselves hold pruned openings, in which the opened leaves of a
tree share one set of sibling digests.

1. What the file contains.
   `spokeV lo n`  On n files from place lo on: the outcome of `runFullS` (Run/PlanQSF.lean:
                  challenges as sampled values), the outcome of `runFullSP` (Run/PlanQSFP.lean:
                  challenges as hash blocks), and whether both agree with the table that came with
                  the files. An outcome is "accepted", "reader" (the parser could not turn the file
                  into a proof string) or "verifier" (the compiled verifier refused the string); a
                  fourth, "limits", says that the description fails the test `ok`
                  (Run/PlanQTypes.lean).
   `fitsV`        Which outcome agrees with a part. Both run functions stand behind a parser that
                  makes no test of work, of a leaf or of a root. So 0: accepted; 1 (form): reader; 3
                  (Merkle openings), 4 and 5 (the last block's checks): verifier. For 2 (proof of
                  work), and for the one copy whose part is left open: refused, by either. There the
                  hash chain moves, other positions are drawn, and the file may or may not still
                  split into as many bytes as the new positions ask for.
   `byLuck`       The exceptions to the rule for part 3, by name (the list may be empty). Such a
                  copy has its altered byte in the hash chain and passes the proof of work by chance
                  (six bits at the tiny parameters). The programs' own verifiers then refuse it at
                  an opening, part 3. Here other positions are drawn, the file no longer splits, and
                  the outcome is "reader".

2. What is checked when the file compiles. One test (#guard), on the table alone: every name in
   `byLuck` is a file of part 3. The list is empty at these files, so this test holds of nothing.

3. Theorems. None here. What is proved of what runs behind the parser, and at which interface:
   Run/PlanQSFProg.lean, 1. The formal conditions of the record `Met` (Run/M1Door.lean) on the whole
   interface and on its wiring are met, with challenges as hash blocks, at the descriptions T, R, F
   of Run/M1RunTiePF.lean. This is stated in Run/BatchDoor.lean and proved in
   Run/BatchDoorProofs.lean (`metBF_T`, `metBF_R`, `metBF_F`). At the interface `LtS` it is in
   Run/M1Door.lean (`metF_T`, `metF_R`, `metF_F`). What is not met is told in part 4 of the heads of
   Run/BatchDoor.lean and Run/M1Door.lean. The two conditions on soundness hold there only at the
   relation "everything", where they are empty. Round-by-round knowledge soundness for a relation
   with content is shown nowhere in Run/ or Fmt/. No statement on soundness follows.

4. What is not claimed. This file runs nothing. The outcomes are in Run/PlanQSFProgPFa.lean and the
   files that follow it; the count, and what these runs are not, are in Run/PlanQSFProg.lean.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanQSFP
import Fmt.M1FullProgPFw

namespace Run.PQ.ProgPF
open _root_.Fmt.M1

/-- the copies of part 3 whose altered byte is in the hash chain, not in an opening -/
def byLuck : List String := []

def fitsV (name : String) : Option Nat → Who → Bool
  | some 0, w => w == .accepted
  | some 1, w => w == .reader
  | some 3, w => if byLuck.contains name then w == .reader else w == .verifier
  | some 4, w => w == .verifier
  | some 5, w => w == .verifier
  | _, w => w == .reader || w == .verifier

def spokeV (lo n : Nat) :
    List (String × Who × Who × Bool) := ((_root_.Fmt.M1.ProgPF.all.drop lo).take n).map fun x =>
  let a := runFullS KnownF.spec (dec KnownF.par) x.2.1
  let b := runFullSP KnownF.spec (dec KnownF.par) x.2.1
  (x.1, a, b, fitsV x.1 x.2.2 a && fitsV x.1 x.2.2 b)

end Run.PQ.ProgPF

-- every copy that is named as an exception is a file of part 3
#guard Run.PQ.ProgPF.byLuck.all fun n => (_root_.Fmt.M1.ProgPF.all.find? (·.1 == n)).any (·.2.2 == some 3)
