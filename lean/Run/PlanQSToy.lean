-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSToy.lean: tests that the functions of Run/PlanQS.lean can be evaluated, also at a round
that draws field elements.

What is evaluated. Run/PlanQS.lean's `runStrictS` and `runLaxS`: a reader at the format's hash, then
`VP`, which that file proves equal to the run of `Compile.Batch.verifyOneProtocol` at the description's
protocol (`vp_eq`).

Sources. The second group of tests uses the format page's own known answer of its section 8
(docs/format/FORMAT.md, at an edition that is not the one that ships): a whole chain in a file, with
a tree of depth 3 and an opening
(Fmt/Rules8.lean: `Known8.spec`, `file2`, `file1`), in both fields.

1. What the file contains. Tests; a wiring `WS c` (`QueryLayout`, Iop/BatchWire.lean) of the interface
   `LtS` at a small description of this library's own, that of Run/PlanQToy1.lean (Test's wiring:
   `wqS`; Link and Batch have no rounds); one theorem.

2. What is checked when the file compiles. Nine tests (#guard), in two groups.
   A comparison. At the description, decision and files of Run/PlanQToy1.lean: on the honest file
   and on the copies altered at the bytes 72, 96, 264, 488 the outcome (reader, verifier, accepted)
   is that of `runStrict` and `runLax` (Run/PlanQRun.lean: `Compile.Batch.vTS` by the library's own
   terms), behind both readers. The honest file is accepted behind the strict reader, and the
   verifier refuses the copy altered at byte 488 behind the lenient reader.
   A trial at drawn field elements. In the page's known answer the first round draws elements of the
   extension field, the last draws positions, with work. The decision is "yes", so what is tried is
   the chain, the test of work, the strict format and the walk to the root. Both descriptions are
   within the limits (`ok`). The page's file is accepted, in both fields, behind both readers. With
   one byte altered, at every eighth byte of the file, the file of one of the two fields
   (`Fmt.Known8.file2`) is never accepted. Behind the lenient reader (which leaves work and openings
   to the verifier; what the lenient reader still asks the hash, what it refuses and what it does
   not test: part 1 of the head of Run/ParseLax.lean) the verifier refuses at least one such copy
   (counted: `nVer`). One field's file under the other field's description (`Fmt.Known8.file2` at
   `K8 .one`) is not accepted behind the strict reader.
   What was measured on other forms of these functions. A form on "the twin in the monad"
   (see Run/TwinDefs.lean) ended at this file: Lean reached 12 GB of memory and was stopped there. A
   form whose walk handed digests on as functions did not come back in 300 s. The functions by the
   library's own terms were not tried there: by Run/TwinDefs.lean's head they build the lists of
   verifier messages.

3. Theorems.
   `vbs_toy`            For every claim c, cm, π: `VP (S c) (dec c) cm π` = (`Compile.Batch.vBS` (Wb
                        (WS c).K (WS c).T) (256 + 8 · the salt's bytes) 256 cm () π).det (famP ..).
                        At a closed list of rounds the annotation of Run/PlanQS.lean is the
                        library's by definition: the equation typechecks without a cast, and `vp_eq`
                        is its proof. (On the interfaces `LtS` and `LbS`: the head of
                        Run/PlanQS.lean.)

4. What is not claimed. No protocol's decision is tried in the trial. Its file is the format page's
   own example, not a program's output. The tests leave no theorem. No statement on soundness.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanQSLaws
import Run.PlanQToy1

set_option autoImplicit false

namespace Run.PQ.TS
open Iop Rom Compile Compile.Batch Run.PQ

def yes (_ : View) : Bool := true

def K8 (f : _root_.Fmt.Fld) : _root_.Fmt.Spec := _root_.Fmt.Known8.spec f

/-- Whether `runStrictS` and `runLaxS` give the outcomes of `runStrict` and `runLax` on one file, at
the description of Run/PlanQToy1.lean. -/
def agreeS (c : T1.E3) (file : ByteArray) : Bool :=
  runStrictS (T1.S c) (T1.dec c) file == runStrict (T1.S c) (T1.dec c) file &&
    runLaxS (T1.S c) (T1.dec c) file == runLax (T1.S c) (T1.dec c) file

/-- the places at which a copy is altered: every eighth byte -/
def places (b : ByteArray) : List Nat := (List.range (b.size / 8)).map (8 * ·)

/-- how many altered copies the verifier itself refuses behind the lenient reader -/
def nVer (f : _root_.Fmt.Fld) (b : ByteArray) : Nat :=
  ((places b).filter fun i => runLaxS (K8 f) yes (_root_.Fmt.flipAt b i) == .verifier).length

/-- the wiring of the interface `LtS` at the description of Run/PlanQToy1.lean -/
def WS (c : T1.E3) : QueryLayout 256 (LtS (ck (T1.S c).plan.field) (rds (T1.S c)) (T1.dec c)) where
  K := kOf (T1.S c) + 1
  T := wqS (ck (T1.S c).plan.field) (kOf (T1.S c)) (chalOf (T1.S c).plan.field (kOf (T1.S c)))
    (rds (T1.S c)) (T1.dec c)
  Lk := ⟨(), weL, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  B := ⟨(), we0, inferInstanceAs (DecidableEq Empty), 0, 0⟩
  depth := 0
  depthReq := 0

def Spec.vbs_toy : Prop :=
  ∀ (c : T1.E3) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck (T1.S c).plan.field) (rds (T1.S c)) (T1.dec c)).up),
    VP (T1.S c) (T1.dec c) cm π =
      (vBS (Wb (WS c).K (WS c).T) (256 + 8 * (T1.S c).plan.salt) 256 cm () π).det
        (famP (fun _ => LbS (ck (T1.S c).plan.field) (rds (T1.S c)) (T1.dec c)) _root_.Fmt.oracle
          (PDS (T1.S c) (ck (T1.S c).plan.field) (T1.dec c)) (kOf (T1.S c) + 1))

theorem vbs_toy : Spec.vbs_toy := fun c cm π => vp_eq (T1.S c) (T1.dec c) cm π

end Run.PQ.TS

-- the comparison
open Run Run.PQ Run.PQ.TS Run.ParseEx in
#guard agreeS (1, 2, 3) file
open Run Run.PQ Run.PQ.TS Run.ParseEx in
#guard [72, 96, 264, 488].all fun i => agreeS (1, 2, 3) (flip file i)
open Run Run.PQ Run.PQ.TS Run.ParseEx in
#guard runStrictS (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) file == .accepted && runLaxS (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) (flip file 488) == .verifier

-- the trial at drawn field elements
open Run Run.PQ Run.PQ.TS in
#guard ok (K8 .two) && ok (K8 .one)
open Run Run.PQ Run.PQ.TS in
#guard runStrictS (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && runLaxS (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard runStrictS (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted && runLaxS (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => runStrictS (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted && runLaxS (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted
open Run Run.PQ Run.PQ.TS in
#guard 0 < nVer .two _root_.Fmt.Known8.file2
-- one field's file under the other field's description
open Run Run.PQ Run.PQ.TS in
#guard runStrictS (K8 .one) yes _root_.Fmt.Known8.file2 != .accepted
