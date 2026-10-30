-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanQSP.lean: the run functions of Run/PlanQS.lean with challenges as hash blocks.

This file is about running the compiled, non-interactive verifier on the bytes of a proof file. A
run function maps a file to an outcome (`Who`, Run/PlanQRun.lean: `.limits`, `.reader`, `.verifier`,
`.accepted`): accepted, or the stage that refuses. It is a reader, which makes a typed proof string
of the file, followed by the verifier: "the verifier behind the reader". The strict reader
(`Fmt.wholeChainF`) itself tests the proof of work and compares the roots of the Merkle openings;
the lenient reader (`laxWholeF`, Run/ParseLaxFast.lean) leaves both to the verifier; what the
lenient reader still asks the hash, what it refuses and what it does not test: part 1 of the head of
Run/ParseLax.lean. S is a description of the proof's rounds (`Fmt.Spec`, Fmt/Rules8.lean), dec a
decision on what has been read (`Fmt.View`, Fmt/View.lean).

Why. There are two choices of what a round's verifier message is. With challenges as sampled values
(Run/PlanQS.lean: `VP`, `runStrictS`, `runLaxS`) the wiring applies each round's sampler. At a round
that draws a field element the verifier messages are then not exactly uniform, so that wiring does
not obey the library's laws of a wiring. With challenges as hash blocks, the choice used here
(Run/PlanPull.lean: `ckP`, `chalP`), a round's verifier message is its own hash blocks, the wiring
hands blocks on, and the view applies the sampler (the field `dr` of `ckP`). Under the hypotheses of
`planPull_okg` (every round's sampler takes at most K blocks, K being the number of blocks given to
`chalP`; every round's work is at most 64): the messages are exactly uniform, and the laws hold.
Among the laws (`ProtocolQueryLayout.OKG`, Iop/BatchWire.lean) of a wiring (here `wqS`, Run/PlanQS.lean) is, for
each round, `chal_unif`: the round's map from hash blocks to its verifier message takes uniform
blocks to a uniform message.

1. What the file contains.
   `VPP S dec cm π : Bool`, `runOnSP`, `runStrictSP`, `runLaxSP S dec file : Who`
                        Run/PlanQS.lean's `VPC`, `runOnC`, `runStrictC`, `runLaxC` at
                        (`ckP S.plan.field`, `kOf S`, `chalP S.plan.field (kOf S)`).

2. What is checked when the file compiles. Five tests (#guard). `oneVoice S dec file` says: behind
   each of the two readers, one verdict at both choices on that file, with the same stage refusing.
   (1) At a small description of this library's own (that of Run/PlanQToy1.lean) the honest file is
       accepted behind both readers (with challenges as hash blocks).
   (2) At that description `oneVoice` holds of the honest file and of the copies altered at the
       bytes 72, 96, 264, 488.
   (3), (4) The format page's own known answer of its section 8 (a round that draws elements of the
       extension field; decision "yes") is accepted in both fields behind both readers (here with
       challenges as hash blocks; with sampled values in Run/PlanQSToy.lean).
   (5) The file of one of the two fields (`Fmt.Known8.file2`), with one byte altered, at every
       eighth byte, gives, behind both readers, the outcome of the other choice's run function (a
       test here). It is never "accepted": behind the lenient reader by the same test, behind the
       strict reader by Run/PlanQSToy.lean's test on the same copies.

3. Theorems.
   `vpp_eq`             For every S, dec, cm, π: `VPP S dec cm π` is the result of the run of the
                        compiled verifier (`Compile.Batch.verifyOneProtocol`) under the typed oracle
                        functions `famP ..` (`det`, Rom/Cache.lean).

4. What is not claimed, or stands elsewhere.
   That the two choices give one verdict on every file. Here there are tests on these files only.
   For the two functions behind the lenient reader it is a theorem of a later file
   (Run/PageIsRunProofs.lean: `run_two`: `ok S` and `smallB S file` give
   `runLaxS S dec file = runLaxSP S dec file`); for the run functions behind the strict reader it is
   only tested.
   That the protocol with challenges as hash blocks is the library's own construction: a theorem of
   a later file (Run/PlanPullProtoProofs.lean: `planPull_proto`: it is, as a term, the protocol with
   challenges as sampled values, without work, pulled back along the format's samplers, then given
   its tests).
   No statement on soundness. How often the sampler is applied in an evaluation is not counted.
   Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPull
import Run.PlanQSToy

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The verifier `VPC` (Run/PlanQS.lean) with challenges as hash blocks (`ckP`, `chalP`). -/
def VPP (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ckP S.plan.field) (rds S) dec).up) : Bool :=
  VPC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec cm π

def Spec.vpp_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ckP S.plan.field) (rds S) dec).up),
    VPP S dec cm π =
      (verifyOneProtocol (lam := 256) (K := kOf S + 1) (L := LbS (ckP S.plan.field) (rds S) dec)
          (256 + 8 * S.plan.salt) 256 .onl (PSof (ckP S.plan.field) (rds S) dec).up
          (wqS (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ckP S.plan.field) (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).det
        (famP (fun _ => LbS (ckP S.plan.field) (rds S) dec) _root_.Fmt.oracle
          (PDS S (ckP S.plan.field) dec) (kOf S + 1))

theorem vpp_eq : Spec.vpp_eq := fun S dec cm π =>
  vpc_eq S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec cm π

def runOnSP (S : _root_.Fmt.Spec) (dec : View → Bool)
    (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof (ckP S.plan.field) (rds S) dec).up)) : Who :=
  runOnC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec x

/-- The run function with challenges as hash blocks, through the page's own reader (in the head: the
strict reader). -/
def runStrictSP (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runStrictC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

/-- The run function with challenges as hash blocks, through the lenient reader. -/
def runLaxSP (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  runLaxC S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

/-- Whether, on a file, the two choices' run functions give the same outcome behind both readers. -/
def oneVoice (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Bool :=
  runStrictSP S dec file == runStrictS S dec file && runLaxSP S dec file == runLaxS S dec file

end Run.PQ

-- the small description of Run/PlanQToy1.lean
open Run Run.PQ Run.PQ.TS Run.ParseEx in
#guard runStrictSP (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) file == .accepted && runLaxSP (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) file == .accepted
open Run Run.PQ Run.PQ.TS Run.ParseEx in
#guard oneVoice (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) file && [72, 96, 264, 488].all fun i => oneVoice (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) (flip file i)
-- the page's known answer of section 8
open Run Run.PQ Run.PQ.TS in
#guard runStrictSP (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && runLaxSP (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard runStrictSP (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted && runLaxSP (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => oneVoice (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) && runLaxSP (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted
