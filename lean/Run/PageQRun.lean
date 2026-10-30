-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQRun.lean: the generic construction (Run/PlanQS.lean: from a description it makes a
protocol, its wiring and run functions), over the single oracle: a verifier that Lean can evaluate
on a proof file, and a theorem on what it runs.

The compiled verifier (`Compile.Batch.verifyOneProtocol`) asks typed oracles. An encoding of the typed
queries as bit strings (`Rom.OracleCoding`, Rom/Family.lean; here `theImpl` of Run/PageQ.lean's `pageQ`)
puts it over a single oracle on bit strings. The run function here, `run1`, takes a proof file's
bytes to a value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`,
`verifier`.
A description is a value `S : Fmt.Spec` (Fmt/Rules8.lean), a decision a function
`dec : View → Bool`. From a chain's description and a decision, nothing else: the evaluable form of
the compiled verifier at the typed oracle functions that the encoding of the queries (with its
inverse and both laws) reads out of a single oracle on bit strings, BLAKE2b behind it. Definitions
that compute; one theorem; tests.
Run/PlanQS.lean runs the evaluable form of the compiled verifier at typed oracle functions written
directly from the format (a short cut). The form in which the top theorems end is another: the
scheme's algorithms over a single oracle, through an encoding (Rom/Family.lean: `OComp.overOne`).
Here that form is what runs.

Main names:
  `V1 S dec h cm π : Bool`: Run/ThinBits.lean's plain verifier (`Thin.verifyPB`) at
    Run/PlanQS.lean's data, with g := Run/PageQ.lean's `gQ`.
  `Spec.v1_eq`: `V1 S dec h cm π` = ((`Compile.Batch.verifyOneProtocol` .. (`PSof` ..).up (`wqS` ..) .. [cm]
    () π).overOne (`theImpl` (`pageQ` ..))).det `oBits`: for every S, dec, cm, π with the test
    `OKQ S`.
  `run1 S dec file : Who`: the lenient reader at the format's hash, then `V1`; "limits" where the
    description is outside the generic construction's limits or fails `OKQ`.

Tests (#guard). (1) At this library's own small toy's description: on all 21 files of this
library's own small toy (`Fmt.Toy1`) the outcome is that of the short cut (Run/PlanQS.lean:
`runLaxS`). (2) At the format page's own known answer of section 8 (of an edition that is not the
one that ships), a chain whose first round draws elements of the extension field, both fields:
accepted; at the second field alone: with one byte altered, at every eighth byte: never accepted,
and the outcome is the short cut's; the second field's file under the first field's description: not
accepted. The encoding of the queries has one block for a leaf and one for a node, as the top
theorems ask of an encoding: Run/CodingPageOne.lean (`pageQ_leaf1`, `pageQ_node1`).

Limits (what it is not): the files are this library's own or the page's (made by the format page's
reference program), not the programs'. In (2) the decision is "yes". The reader calls the format's
hash directly. `verifyOneProtocol` taken alone belongs to no scheme under a theorem: no soundness is
claimed. Tests leave no theorem. That the evaluator builds no list of verifier messages is a fact
about this compiler: test (2) would not come back otherwise.
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageQ
import Run.PlanQSToy
import Run.DetOverOne
import Fmt.Toy1Files

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The verifier over the single oracle. -/
def V1 (S : _root_.Fmt.Spec) (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up) : Bool :=
  Thin.verifyPB (lam := 256) (K := kOf S + 1) (fun _ => LbS (ck S.plan.field) (rds S) dec)
    (gQ S (ck S.plan.field) dec (kOf S + 1) h) id none (256 + 8 * S.plan.salt) 256 .onl
    (PSof (ck S.plan.field) (rds S) dec)
    (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
    (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

/-- Under the hypotheses below, what runs is the run of the compiled verifier over the single
oracle, all blocks asked. -/
def Spec.v1_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256)
      (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up),
    V1 S dec h cm π =
      ((verifyOneProtocol (lam := 256) (K := kOf S + 1) (L := LbS (ck S.plan.field) (rds S) dec)
          (256 + 8 * S.plan.salt) 256 .onl (PSof (ck S.plan.field) (rds S) dec).up
          (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS (ck S.plan.field) (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).overOne
        (theImpl (pageQ S (ck S.plan.field) dec (kOf S + 1) h))).det oBits

theorem v1_eq : Spec.v1_eq := fun S dec h cm π => by
  rw [det_overOne, ← gQ_eq]
  exact Thin.thin_bits Unit Unit 256 (kOf S + 1) (LbS (ck S.plan.field) (rds S) dec) _ Unit E0
    (256 + 8 * S.plan.salt) 256 .onl (PSof (ck S.plan.field) (rds S) dec)
    (wqS (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π

def run1On (S : _root_.Fmt.Spec) (dec : View → Bool)
    (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up)) : Who :=
  if ok S then
    if h : OKQ S = true then
      match x with
      | some ([cm], π) => if V1 S dec h cm π then .accepted else .verifier
      | _ => .reader
    else .limits
  else .limits

/-- The run over the single oracle, through the lenient reader. -/
def run1 (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1On S dec
    (parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof (ck S.plan.field) (rds S) dec) S
      (TYS S (ck S.plan.field) dec) file)

end Run.PQ

open Run Run.PQ Run.PQ.TS in
#guard OKQ (T1.S (1, 2, 3)) && OKQ (K8 .two) && OKQ (K8 .one)
open Run Run.PQ Run.PQ.TS in
#guard run1 (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) _root_.Fmt.Toy1.honest == .accepted
-- (1) the 21 files of `Fmt.Toy1`: the two honest ones accepted; the outcome is the short cut's,
-- file by file
open Run Run.PQ Run.PQ.TS in
#guard
  let a := _root_.Fmt.Toy1.files.map fun f => run1 (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) f.2.1
  let b := _root_.Fmt.Toy1.files.map fun f => runLaxS (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) f.2.1
  a == b && (a.map fun w => w == .accepted) == (_root_.Fmt.Toy1.files.map fun f => f.2.2.isNone) && (a.filter fun w => w == .verifier).length == 11
-- (2) the page's known answer of section 8: a round that draws elements of the extension field
open Run Run.PQ Run.PQ.TS in
#guard run1 (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && run1 (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => run1 (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted && run1 (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) == runLaxS (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i)
open Run Run.PQ Run.PQ.TS in
#guard run1 (K8 .one) yes _root_.Fmt.Known8.file2 != .accepted
