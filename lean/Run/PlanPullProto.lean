-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullProto.lean: two terms are equal. One is the generic construction's public-coin IOP
(`InteractiveOracleProof`, Iop/InteractiveOracleProof.lean) whose verifier messages are hash blocks, with proof of work, written
directly. The other is what two steps of the library make of the IOP `Qv` whose verifier messages
are sampled values, without proof of work.

Definitions and one statement (`Run.Spec.planPull_proto`); the proof is in
Run/PlanPullProtoProofs.lean. Many statements of this library are written twice: a definition in the
namespace `Spec` states a proposition, and a theorem of the same name outside that namespace proves
it (lean/GLOSSARY.md).

The generic construction (Run/PlanQTypes.lean, Run/PlanQWire.lean, Run/PlanQS.lean) makes a protocol
(`InteractiveOracleProof`, Iop/InteractiveOracleProof.lean) from a list ds of rounds' data (`PQ.RD`, in the format's terms, Fmt/) and
a decision dec, at any choice of challenge types (`PQ.CK`). The choice `ck f` (Run/PlanDrawsQ.lean)
is challenges as sampled values (the row of `Qv` below). The choice `ckP f` (Run/PlanPull.lean) is
challenges as hash blocks: a round's verifier message is its 256-bit blocks, and reads and decision
apply the round's sampler. `InteractiveOracleProof.pull` (Iop/Pull.lean) puts in each round a sampler's source in the
place of the verifier message. `InteractiveOracleProof.grind` (Iop/Grind.lean) adds the tests of work: nonces, and
test bits that must all be 0. An interface (`BatchProtocol`, Iop/Batch.lean) is the library's record of three
protocols, called Test, Link and Batch, with an encoding and a decoding of an index. More on these
words: the head of Run/PlanPull.lean.

Main names:
  `Qv C ds dec`: the round in front (`PQ.s0`, Run/PlanQS.lean, as a round), then
    Run/PlanQTypes.lean's rounds; reads and decision as in that file's `PQ.Q0`. At `ck f` its
    verifier messages are the values of the format's draws (an element that must not be 0 has a type
    without 0: `DVal`, `NZ`, Run/DrawPage.lean).
  `Spec.planPull_proto`: the title's equation (`InteractiveOracleProof.pull`, then `InteractiveOracleProof.grind`), for every field f,
    ds, dec.

Why: by the library's texts, as read (`BatchProtocol.draws`, Iop/BatchWireDraw.lean; `BatchProtocol.drawsGrind`,
Iop/GrindPull.lean; CompileK/Main.lean, CompileK/GrindMain.lean), the compiler's theorems with
biased samplers and with proof of work are about the interface L₀.drawsGrind W dr gT ..
Its Test is
  (L₀.offline.pull (Samplers.ofDraws _ dr.T)).grind W (gT.pull (Samplers.ofDraws _ dr.T)).
Numbers that are shown of L₀.offline carry over to that protocol by the library's own theorems, under
their hypotheses (the factor of the bias; the work). The protocol that is run (`PQ.PSof`,
Run/PlanQS.lean, at `ckP`, Run/PlanPull.lean) is written directly. Here: the two are one term, in
exactly that form.

Limits: no interface L₀ with `Qv` as its Test, no `DataK`, no `Work` is written down here. They
are in Run/PlanPullFace.lean (`L0`) and Run/PlanPullData.lean [not in this library] (`Dv`, `wv`).
This file says nothing on the wiring of the protocol (Run/PlanPullWq.lean), and nothing on the
interface's honest sides.
It says nothing on any number: nothing is shown of `Qv`: no soundness, no completeness, no hiding.
The run functions of the generic construction stand at the interface `PQ.LbS` (Run/PlanQS.lean), not
at the one for which this file was written. The protocol that is run (`PQ.PSof`, Run/PlanQS.lean) is
`PQ.LbS`'s Batch. This file has no wiring. In the theorems vbs_*, vbsP_*, vbsPF_* of
Run/M1RunTie.lean and its companion files, Run/M2Tie.lean and Run/PlanQSToy.lean, the field B of
`PQ.LbS`'s wiring (`Wb`, Run/PlanQS.lean) is `PQ.wqS` (Run/PlanQS.lean) or `PQ.wqSF`
(Run/PlanQSF.lean). An interface whose Test is this protocol is `PQ.LtS` (Run/PlanQS.lean).
The library's terms on the right of the statement are those of an interface's Test (local forms);
its generic forms for Batch (`BatchInteractiveOracleProof.grind`, `ProtocolQueryLayout.ofDraws`, `ProtocolQueryLayout.grind`) are other terms
at a round with work: no equation with them is stated.

Terms: lean/GLOSSARY.md.
-/
import Run.PlanPull
import Iop.GrindPull

set_option autoImplicit false

namespace Run
open Prob Iop

/-- The protocol without work, at a choice `C` of challenge types (`PQ.CK`). -/
@[reducible] def Qv (C : PQ.CK) (ds : List PQ.RD) (dec : PQ.View → Bool) : InteractiveOracleProof Unit PQ.E0 where
  shape := (PQ.s0 C).up :: PQ.shapeL C ds
  blinded := fun _ => true
  extReads := fun _ _ => ∅
  reads := fun _ ρ _ =>
    (((PQ.wanted ds (PQ.drawnL C ds ρ.2)).filterMap fun nx =>
      (PQ.posAt C ds nx.1 nx.2).map fun p => (Sum.inr p : Empty ⊕ OPos (PQ.shapeL C ds)))).toFinset
  accept := fun _ _ τ => dec (PQ.viewL C ds τ.2.2)

/-- The block samplers, one for each round. -/
def drOf (f : _root_.Fmt.Fld) (ds : List PQ.RD) :
    Shape.Draws 256 ((PQ.s0 (ck f)).up :: PQ.shapeL (ck f) ds) :=
  (bsRound f PQ.e0 .nothing, drawsOf f _ (planL f ds))

/-- The bits of work, on the shape of `Qv`. -/
def g0Of (f : _root_.Fmt.Fld) (ds : List PQ.RD) :
    GBits ((PQ.s0 (ck f)).up :: PQ.shapeL (ck f) ds) :=
  (0, PQ.gL (ck f) ds)

def Spec.planPull_proto : Prop :=
  ∀ (f : _root_.Fmt.Fld) (ds : List PQ.RD) (dec : PQ.View → Bool), (PQ.PSof (ckP f) ds dec).up.loc =
    ((Qv (ck f) ds dec).pull (Samplers.ofDraws _ (drOf f ds))).grind
      ℕ ((g0Of f ds).pull (Samplers.ofDraws _ (drOf f ds)))

end Run
