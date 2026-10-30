-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSFP.lean: the compiled verifier at the wiring nearest to those in the compiler's top
theorems: challenges as hash blocks, and whole paths.

Two things separate the wiring of `VP` of Run/PlanQS.lean from the wirings in the compiler's top
theorems. (1) There, a round's verifier message is the round's hash blocks themselves, and reads and
decision apply the sampling rule (challenges as hash blocks; the library calls this a pull). In the
wiring of `VP` a verifier message is the values that the format draws, field elements and positions
among them (challenges as sampled values). Challenges as hash blocks are `ckP`, `chalP` of
Run/PlanPull.lean; Run/PlanQSP.lean runs the construction of Run/PlanQS.lean at them. (2) There,
each opened Merkle leaf has an authentication path of its own (whole paths), where the wiring of
`VP` has pruned openings; see Run/PlanQSF.lean. What a wiring is: the head of Run/PlanQSF.lean.

1. What the file contains.
   `runFullSP S dec file : Who`
                              The run function: the parser that fills whole paths, then `VPFP`.
   `fourVoices S dec file`    Whether four run functions give the same outcome on a file:
                              (challenges as sampled values, or as hash blocks) times (pruned
                              openings, or whole paths). All four stand behind parsers that leave
                              the tests of work and of openings to the verifier.

2. What is checked when the file compiles. Four tests (#guard).
   On the 21 files of this library's own small test protocol (`Fmt.Toy1.files`; the protocol:
   Run/PlanQToy1.lean) the outcome of `runFullSP` on every file, by name, is compared with a list
   in the test, and whether the file is accepted with the table of the format page's own reference
   program. The outcomes are those of `Run.Toy1.runLax` and `Run.Toy1.runFull` in the tests that
   Run/ParseToy1All.lean gathers, and of `runFullS` in Run/PlanQSFToy.lean; `Run.Toy1.runStrict`,
   with the strict reader in front, has other outcomes there (seen by setting the tests' lists side
   by side; no test compares them).
   The example file of section 8 of the format page (docs/format/FORMAT.md, which comes with the
   programs, the
   C++ implementation that comes with this Lean code), in both fields, with the decision "always
   yes", is accepted by `runFullSP`. With one byte altered, at every eighth byte, it is never
   accepted, and the four run functions give the same outcome.

3. Theorems.
   `vpfp_eq` (statement `Run.PQ.Spec.vpfp_eq`)
                              `VPFP S dec cm π` = (`Compile.Batch.verifyOneProtocol` .. (PSof (ckP ..) ..).up
                              (wqSF (ckP ..) (kOf S) (chalP ..) ..) .. [cm] () π).det (famP ..).

4. What is not claimed. What the heads of Run/PlanQSP.lean and Run/PlanQSF.lean list as not claimed.
   That the four run functions give one outcome on every file is tested on the altered copies of the
   example file named above; it is not proved. (Proved are two statements, which no statement of
   Run/ joins: under `ok S` and `smallF S file`, `full_lax` (Run/PageIsFull.lean [not in this library]): whole paths
   against pruned openings behind the lenient reader, at each choice of challenge types that meets
   its two further premises (met at the two choices in use: `kit_ck`, `kit_pull`, `room_kOf`,
   Run/PageIsProofs.lean); under `ok S` and `smallB S file`, `run_two` (Run/PageIsRun.lean):
   `runLaxS` against `runLaxSP`.)
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSF
import Run.PlanQSP
import Fmt.Toy1Files

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The verifier `VPFC` (Run/PlanQSF.lean) with challenges as hash blocks (`ckP`, `chalP`), at the
wiring without the flag. -/
def VPFP (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ckP S.plan.field) (rds S) dec).up) : Bool :=
  VPFC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec cm π

def Spec.vpfp_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ckP S.plan.field) (rds S) dec).up),
    VPFP S dec cm π =
      (verifyOneProtocol (lam := 256) (K := kOf S + 1) (L := LbS (ckP S.plan.field) (rds S) dec)
          (256 + 8 * S.plan.salt) 256 .onl (PSof (ckP S.plan.field) (rds S) dec).up
          (wqSF (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ckP S.plan.field) (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).det
        (famP (fun _ => LbS (ckP S.plan.field) (rds S) dec) _root_.Fmt.oracle
          (PDS S (ckP S.plan.field) dec) (kOf S + 1))

theorem vpfp_eq : Spec.vpfp_eq := fun S dec cm π =>
  vpfc_eq S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec cm π

/-- The run function with challenges as hash blocks, at the wiring without the flag. -/
def runFullSP (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runFullC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

/-- Whether the four run functions named in the head give the same outcome on a file. -/
def fourVoices (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Bool :=
  let a := runFullSP S dec file
  a == runFullS S dec file && a == runLaxSP S dec file && a == runLaxS S dec file

end Run.PQ

open Run Run.PQ in
#guard
  let r := _root_.Fmt.Toy1.files.map fun x => (x.1, runFullSP (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) x.2.1, x.2.2.isNone)
  (r.map fun y => (y.1, y.2.1)) == [("honest", Who.accepted), ("honest2", Who.accepted), ("alt01", Who.reader), ("alt02", Who.reader), ("alt03", Who.verifier), ("alt04", Who.verifier), ("alt05", Who.verifier), ("alt06", Who.verifier), ("alt07", Who.verifier), ("alt08", Who.verifier), ("alt09", Who.reader), ("alt10", Who.reader), ("alt11", Who.verifier), ("alt12", Who.reader), ("alt13", Who.reader), ("alt14", Who.reader), ("alt15", Who.reader), ("alt16", Who.verifier), ("alt17", Who.verifier), ("alt18", Who.verifier), ("alt19", Who.verifier)] && r.all fun y => (y.2.1 == Who.accepted) == y.2.2
open Run Run.PQ Run.PQ.TS in
#guard runFullSP (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && runFullSP (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => fourVoices (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) && runFullSP (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file1).all fun i => fourVoices (K8 .one) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file1 i) && runFullSP (K8 .one) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file1 i) != .accepted
