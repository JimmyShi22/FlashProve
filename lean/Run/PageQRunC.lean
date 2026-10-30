-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PageQRunC.lean: the run over the single oracle (Run/PageQRun.lean) with the choice of challenge
types (a record of type `CK`, called a kit in the code) and the wiring's sampling function as
parameters; and its instance with challenges as hash blocks (`ckP`; the library's "pull")
(Run/PlanPull.lean), at which the conditions on a wiring (`OKG`) hold also where field elements are
drawn (`Spec.planPull_okg`, Run/PlanPull.lean, under its hypotheses).

The compiled verifier (`Compile.Batch.verifyOneProtocol`) asks typed oracles. An encoding of the typed
queries as bit strings (`Rom.OracleCoding`, Rom/Family.lean; here `theImpl` of Run/PageQ.lean's `pageQ`)
puts it over a single oracle on bit strings. The run functions here take a proof file's bytes to a
value of `Who` (Run/PlanQRun.lean): `accepted`, or who refuses: `limits`, `reader`, `verifier`.
A wiring (`ProtocolQueryLayout`, Iop/BatchWire.lean) says, round by round, how oracle messages are laid into
hash trees and how blocks of hash output become verifier messages. Definitions that compute;
theorems; tests.

Why: Run/PageQRun.lean's `V1` stands with challenges as sampled values (`ck`) (the wiring applies
the sampling rule): at a round that draws a field element its verifier messages are not exactly
uniform, so that wiring does not obey the library's conditions on a wiring (`OKG`), and no compiled
theorem's hypothesis is met at it. (Of which hypothesis these words speak, and what is had of the
others, the soundness among them at the relation "everything", and empty: Run/PlanQS.lean, the head,
4.) The form that obeys them is challenges as hash blocks (`ckP`): a round's verifier message is its
blocks, the wiring hands blocks on, reads and decision apply the sampler. The generic construction
from a description, and the encoding of the queries (Run/PageQ.lean: `pageQ`), are generic in that
choice. So the pulled run is an instance, not a copy.

Main names:
  `V1C S C K chal dec h cm π`: the evaluable form of the compiled verifier at Run/PlanQS.lean's
    data for the choice C and the wiring's sampling function chal on K blocks, with g :=
    `gQ S C dec (K + 1) h`.
  `Spec.v1c_eq`: `V1C` .. = ((`Compile.Batch.verifyOneProtocol` .. (`PSof` C ..).up (`wqS` C K chal ..) ..
    [cm] () π).overOne (`theImpl (pageQ S C dec (K + 1) h)`)).det `oBits`: for every S, C, K, chal,
    dec, cm, π with the test `OKQ S`.
  `v1_is`: Run/PageQRun.lean's `V1` is `V1C` with challenges as sampled values (`ck`) (by
    definition).
  `run1C S C K chal dec file : Who`: the lenient reader at the format's hash, then `V1C`.
  `run1P S dec file`: `run1C` with challenges as hash blocks (`ckP`): `ckP`, `chalP` of
    Run/PlanPull.lean, on the description's own number of blocks.

Tests (#guard). With challenges as hash blocks (`ckP`): on all 21 files of this library's own small
toy (`Fmt.Toy1`) the outcome is that of the run with challenges as sampled values (`ck`) (`run1`),
file by file, and the two honest files are accepted; on the format page's known answer of section 8
(a round that draws elements of the extension field): in both fields the honest file is accepted;
at the second field alone: with one byte altered, at every eighth byte: never accepted, and the
outcome is that of `run1`.
The encoding of the queries has one block for a leaf and one for a node, at every choice of
challenge types: Run/CodingPageOne.lean (`pageQ_leaf1`, `pageQ_node1`).

Limits (what it is not): all that Run/PageQRun.lean's head says of its run.
That the two choices of challenge types give one verdict on every file is not proved in this file
(the tests show it on these files): it is stated in Run/PageIsOne.lean, `one_two`: `run1PF S dec
file = run1K S dec file` [not in this library; so here read: not proved in this library], under
tests on the
description and on the file that are stated there.
That the protocol with challenges as hash blocks (`ckP`) is the library's pull of the other, and
that its wiring is the compiler's generic wiring: not shown in this file
(Run/PlanPull.lean's head). The first is a theorem in this form: it is the pull of the protocol
without work at `ck`, then given its tests (`Spec.planPull_proto`, Run/PlanPullProto.lean, with
that head's limits; proved in Run/PlanPullProtoProofs.lean); the second is a theorem for the wiring
with whole paths (`Spec.planPull_wq`, Run/PlanPullWq.lean, with that head's limits; proved in
Run/PlanPullWqProofs.lean), and the wiring of this file, with pruned openings, is not of that form
(that file's head).
Limits: see "To be declared with every use" in the head of Run/ParseBS.lean (`leafSalt`).

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PageQRun
import Run.PlanPull

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch

/-- The verifier over the single oracle, at any choice of challenge types. -/
def V1C (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up) :
    Bool :=
  Thin.verifyPB (lam := 256) (K := K + 1) (fun _ => LbS C (rds S) dec) (gQ S C dec (K + 1) h)
    id none (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec)
    (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
    (fun s => some (.inl s)) 0 [cm] () π

def Spec.v1c_eq : Prop :=
  ∀ (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
      (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256) (π : OneProtocolProof 256 (PSof C (rds S) dec).up),
    V1C S C K chal dec h cm π =
      ((verifyOneProtocol (lam := 256) (K := K + 1) (L := LbS C (rds S) dec) (256 + 8 * S.plan.salt) 256 .onl
          (PSof C (rds S) dec).up (wqS C K chal (rds S) dec)
          (fun p a => some (.inr ⟨Tag.onl, ⟨p, a⟩⟩)) (embPS C (rds S) dec) some
          (fun s => some (.inl s)) 0 [cm] () π).overOne
        (theImpl (pageQ S C dec (K + 1) h))).det oBits

theorem v1c_eq : Spec.v1c_eq := fun S C K chal dec h cm π => by
  rw [det_overOne, ← gQ_eq]
  exact Thin.thin_bits Unit Unit 256 (K + 1) (LbS C (rds S) dec) _ Unit E0
    (256 + 8 * S.plan.salt) 256 .onl (PSof C (rds S) dec) (wqS C K chal (rds S) dec) _ _ some
    (fun s => some (.inl s)) 0 [cm] () π

theorem v1_is (S : _root_.Fmt.Spec) (dec : View → Bool) (h : OKQ S = true) (cm : Dig 256)
    (π : OneProtocolProof 256 (PSof (ck S.plan.field) (rds S) dec).up) :
    V1 S dec h cm π = V1C S (ck S.plan.field) (kOf S) (chalOf S.plan.field (kOf S)) dec h cm π :=
  rfl

def run1COn (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (x : Option (List (Dig 256) × OneProtocolProof 256 (PSof C (rds S) dec).up)) : Who :=
  if ok S then
    if h : OKQ S = true then
      match x with
      | some ([cm], π) => if V1C S C K chal dec h cm π then .accepted else .verifier
      | _ => .reader
    else .limits
  else .limits

/-- The run over the single oracle, at any choice of challenge types. -/
def run1C (S : _root_.Fmt.Spec) (C : CK) (K : ℕ) (chal : ∀ e k, (Fin K → Dig 256) → C.Ch e k)
    (dec : View → Bool) (file : ByteArray) : Who :=
  run1COn S C K chal dec
    (parseLaxWP (m := Id) _root_.Fmt.formatHash (PSof C (rds S) dec) S (TYS S C dec) file)

/-- The run with challenges as hash blocks (`ckP`). -/
def run1P (S : _root_.Fmt.Spec) (dec : View → Bool) (file : ByteArray) : Who :=
  run1C S (ckP S.plan.field) (kOf S) (chalP S.plan.field (kOf S)) dec file

end Run.PQ

open Run Run.PQ Run.PQ.TS in
#guard run1P (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) _root_.Fmt.Toy1.honest == .accepted && run1P (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) _root_.Fmt.Toy1.honest2 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard _root_.Fmt.Toy1.files.all fun f => run1P (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) f.2.1 == run1 (T1.S (1, 2, 3)) (T1.dec (1, 2, 3)) f.2.1
open Run Run.PQ Run.PQ.TS in
#guard run1P (K8 .two) yes _root_.Fmt.Known8.file2 == .accepted && run1P (K8 .one) yes _root_.Fmt.Known8.file1 == .accepted
open Run Run.PQ Run.PQ.TS in
#guard (places _root_.Fmt.Known8.file2).all fun i => run1P (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) != .accepted && run1P (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i) == run1 (K8 .two) yes (_root_.Fmt.flipAt _root_.Fmt.Known8.file2 i)
