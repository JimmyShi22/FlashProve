-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/BatchS.lean: a protocol as the interface's Batch, where Test and Link have no round: the
scheme's whole verifier (`Compile.Batch.V`), on a constant key string and a constant link string, is
the compiled verifier of the Batch's one slot (`vBS`).

Definitions, six statements (Run.PQ.Spec.batch_*); the proofs are in Run/BatchSProofs.lean.
Compile/Batch/ makes a scheme (`argB`), with a key and proofs, from an interface and a wiring. The
interface (`BatchProtocol`, Iop/Batch.lean) has three protocols, called Test, Link and Batch here. The generic
construction (Run/PlanQTypes.lean, Run/PlanQS.lean) makes one protocol from a description of a proof
file's rounds, a choice of challenge types and a decision function (`PSof C ds dec`).

Why: the generic construction's protocol can be put at the interface's Test (`LtS`, Run/PlanQS.lean;
the tag "test"; `vTS`). What a compiled theorem says of an accepted Test string is a property of the
external string under the key; at an encoded index of length 0 that is empty (Run/M1Door.lean). The
place at which a clause has content for a protocol whose witness lies in its own oracle messages is
the interface's Batch. The run functions of the generic construction are defined at this place
(`VPC`, Run/PlanQS.lean, at `LbS`); `Lb`, `LbS`, `Wb` (and the interface `Lo3` with its
placeholders) are in Run/PlanQS.lean.

Main names:
  `Lb B`: the interface without an index of Run/PlanQS.lean (`Lo3`) at: Test := the protocol without
    a round, Link := the protocol without a round, Batch := a given batch protocol B without
    statement and external oracle; one slot; placeholders as honest sides.
  `LbS C ds dec`: `Lb` at `BatchInteractiveOracleProof.ofProto` of the very protocol that is the Test of `LtS` ((PSof
    C ds dec).up.loc, Run/PlanQS.lean): local rounds alone: so the chain never joins and the request
    tree stays idle (by the annotation, as `recomputeChain` of Compile/Batch/Verifier.lean reads it: not
    stated here).
  `Wb K wB`: the wiring: Test's and Link's are empty; Batch's is given; depth 0; 2^0 slots.
  `piT0 n`, `piL0 n`: the constant strings: a chain's salt of n zero bits; no root, no plain part,
    no opening; slot 0; no path.
  `Spec.batch_types`: equations of types, by definition. So every spelling, code and serialiser of
    the generic construction can be used at both places as it is.
  `Spec.batch_test`, `Spec.batch_link`: on `piT0 sFS` and `piL0 sFS`, `vTS` and `vLS` are
    `pure true`: as terms: no query is asked.
  `Spec.batch_V`: the title's statement, at `keyOf p.sFS cm` and `prfOf p.sFS cm' π`.
  `Spec.batch_arg`: the same of the verifier of `argB`.
  `Spec.batch_same`: by it whatever is proved of the Test of `LtS` with its annotation and of one
    slot's wiring (Run/PlanPullProto.lean, Run/PlanPullWq.lean; the conditions on a wiring (`OKG`))
    holds of the generic construction at Batch as it stands; the equations of the whole interface
    and the whole wiring (Run/PlanPullFace.lean, Run/PlanPullJoin.lean [not in this library]) are LtS's alone.

Limits: the scheme is `argB` at (Lb B, Wb K wB), "commit to nothing, prove the Batch's claim". The
index has one value and its encoding no position; in the statements here the key's Test string and
the proof's Link string are the constants `piT0`, `piL0`; what C and P of `argB` put out is not
stated here; cm and cm' are opened under nowhere (if B's first round is local, cm' enters the first
query's head: a reading of the compiled verifier's text: not stated here). On the two constant
strings cm enters no query, since there Test and Link ask none (`Spec.batch_test`,
`Spec.batch_link`).
This file does not say that this (interface, wiring) is a top theorem's (the compiler's own
interface and wiring from data D and work w): not shown. This file does not say any property of the
interface: its honest sides are placeholders (no completeness), and no soundness of B is stated. It
says nothing on key or link strings other than the two constants. It says nothing on a file, a
parser or a run. Hiding (the field `hidden` of `BatchProtocol.Props`, Iop/Batch.lean) is not shown of this
interface, in this file or elsewhere in Run/.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanPullFace
import Compile.Batch.Star

set_option autoImplicit false

namespace Run.PQ
open Iop Rom Compile Compile.Batch Run.Twin

/-- the constant string of a Test without a round -/
def piT0 (n : ℕ) : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto pB) :=
  ⟨List.replicate n false, [], (), fun p => p.elim, fun p => p.elim0, fun _ => false, 0, []⟩
/-- the constant string of a Link without a round -/
def piL0 (n : ℕ) : OneProtocolProof 256 (BatchInteractiveOracleProof.ofProto pL) :=
  ⟨List.replicate n false, [], (), fun p => p.elim,
    fun p => p.elim (·.elim0) (·.elim0), fun _ => false, 0, []⟩

/-- the scheme's key -/
def keyOf {B : BatchInteractiveOracleProof Unit E0} (n : ℕ) (cm : Dig 256) : IVK 256 (Lb B) := ⟨cm, some (piT0 n)⟩
/-- the scheme's proof -/
def prfOf {B : BatchInteractiveOracleProof Unit E0} (n : ℕ) (cm : Dig 256) (π : OneProtocolProof 256 B) : Prf 256 (Lb B) :=
  ⟨0, cm, some (piL0 n), some π⟩

namespace Spec

/-- States: the types of plain parts and of symbols under (`LbS`, onl) are those under (`LtS`,
test). -/
def batch_types : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool),
    PlainPart (Compile.Batch.shapeOf (LbS C ds dec) .onl) (annOf (LbS C ds dec) .onl) =
      PlainPart (Compile.Batch.shapeOf (LtS C ds dec) .test) (annOf (LtS C ds dec) .test) ∧
    SymAny (Compile.Batch.shapeOf (LbS C ds dec) .onl) =
      SymAny (Compile.Batch.shapeOf (LtS C ds dec) .test)

/-- States: a Test without a round: no query; the constant string is accepted. -/
def batch_test : Prop :=
  ∀ (B : BatchInteractiveOracleProof Unit E0) (K : ℕ) (wB : ProtocolQueryLayout 256 K B) (sMT sFS : ℕ) (cm : Dig 256),
    vTS (Wb K wB) sMT sFS cm (piT0 sFS) = pure true

/-- States: a Link without a round: the same. -/
def batch_link : Prop :=
  ∀ (B : BatchInteractiveOracleProof Unit E0) (K : ℕ) (wB : ProtocolQueryLayout 256 K B) (sMT sFS : ℕ) (cm cm' : Dig 256),
    vLS (Wb K wB) sMT sFS cm cm' (piL0 sFS) = pure true

/-- States: on the key `keyOf p.sFS cm` and the proof `prfOf p.sFS cm' π`, the scheme's whole
verifier is the Batch's: `vBS` on cm' and π (exactly: the equation below). -/
def batch_V : Prop :=
  ∀ (B : BatchInteractiveOracleProof Unit E0) (K : ℕ) (wB : ProtocolQueryLayout 256 K B) (p : Params)
      (cm cm' : Dig 256) (π : OneProtocolProof 256 B),
    Compile.Batch.V (Wb K wB) p (keyOf p.sFS cm) () (prfOf p.sFS cm' π) =
      (vBS (Wb K wB) p.sMT p.sFS cm' () π).bind fun c => pure (true && true && c)

/-- States the same of the verifier of the scheme `Compile.Batch.argB (Wb K wB) WP p`, for every WP.
-/
def batch_arg : Prop :=
  ∀ (B : BatchInteractiveOracleProof Unit E0) (K : ℕ) (wB : ProtocolQueryLayout 256 K B) (WP : WireBP (Lb B)) (p : Params)
      (cm cm' : Dig 256) (π : OneProtocolProof 256 B),
    (Compile.Batch.argB (Wb K wB) WP p).V (keyOf p.sFS cm) () (prfOf p.sFS cm' π) =
      (vBS (Wb K wB) p.sMT p.sFS cm' () π).bind fun c => pure (true && true && c)

/-- States what carries over from the Test form. -/
def batch_same : Prop :=
  ∀ (C : CK) (ds : List RD) (dec : View → Bool),
    (LbS C ds dec).onlineBatch = BatchInteractiveOracleProof.ofProto (LtS C ds dec).offline ∧
    ∀ (K : ℕ) (wB : ProtocolQueryLayout 256 K (LbS C ds dec).onlineBatch), (Wb K wB).B = wB

end Spec
end Run.PQ
