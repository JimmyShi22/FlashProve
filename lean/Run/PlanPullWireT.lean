-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Run/PlanPullWireT.lean: the wiring of a round in the run with whole paths, with challenges as hash
blocks (`PQ.wireSF`, Run/PlanQSF.lean), is the library's step for a test on the compiler's own
generic wiring of that round. This is the same as Run/PlanPullWire.lean, with the round's
proof-of-work test.

One statement (`Spec.planPull_wireT`) and its proof. The words are explained in the head of
Run/PlanPullWire.lean. An interface (`BatchProtocol`, Iop/Batch.lean) is the library's record of three
protocols, called Test, Link and Batch, with an encoding and a decoding of an index.

By the library's definitions, as read (`DataK.WWk`, CompileK/GrindMain.lean; `WireRB.grindLocal`,
Iop/GrindWire.lean), that is the form of the field at that round of the wiring in the compiler's
theorem with proof of work, at data that were not written down when this file was made (a `DataK`
and a `Work` whose encoder of nonces is `PQ.Dn`, whose bits are the plan's, whose samplers are
`bsRound`'s, whose numbering is `npOf`): not shown here. They are written down in
Run/PlanPullData.lean [not in this library] (`Dv`, `wv`). Its `data_T` states as an equation, for Test's whole wiring,
what is said here "as read" (Run/PlanPullDataProofs.lean [not in this library; so here read: not
proved in this library]). Run/PlanPullWire.lean has the
wiring without the test.

Main names:
  `Spec.planPull_wireT`: the title's equation, for every f, K, d.

Limits: this file says nothing on all rounds together, on the round in front, on a protocol's wiring
(its bounds on openings and depths, its test of equality of positions, the external part) or on an
interface's: so not "the wiring in the compiler's theorem". It does not say that the protocol with
challenges as hash blocks is the library's pull.
The run functions of the generic construction stand at the interface `PQ.LbS` (Run/PlanQS.lean), not
at the one for which this file was written: this protocol is `PQ.LbS`'s Batch, this wiring the field
B of its wiring (in the theorems vbsPF_* of Run/M1RunTiePF.lean and Run/M2Tie.lean; `Wb`,
Run/PlanQS.lean). (Said of the whole protocol and of `PQ.wqSF`, Run/PlanQSF.lean, of which this
file's `PQ.wireSF` is one round's part.) An interface whose Test is this protocol is `PQ.LtS`
(Run/PlanQS.lean).
The library's terms on the right of the statement are those of an interface's Test (local forms);
its generic forms for Batch (`BatchInteractiveOracleProof.grind`, `ProtocolQueryLayout.ofDraws`, `ProtocolQueryLayout.grind`) are other terms
at a round with work: no equation with them is stated.

Terms: lean/GLOSSARY.md.
-/
/- Limits: that a proof file is accepted or refused is no theorem of this library. It is the outcome
   of a `#guard` line, or of an evaluation outside the library, such as a test by Lean's evaluator,
   which leaves no declaration. So nothing that is checked of declarations is checked of such an
   evaluation. No clause of a soundness theorem of Fmt/ and Run/ speaks of a run. -/
import Run.PlanPullWire
import Run.PlanQSF

set_option autoImplicit false

namespace Run
open Prob Iop

def Spec.planPull_wireT : Prop :=
  ∀ (f : _root_.Fmt.Fld) (K : ℕ) (d : PQ.RD), PQ.wireSF (ckP f) K (chalP f K) d =
    (WireRB.ofLocalD 256 K (PQ.roundOf (ck f) d) (PQ.ptOf (ck f) d)
        (bsRound f d.entry d.kind) (npOf d.tree)).grindLocal
      PQ.Dn d.entry.work

theorem planPull_wireT : Spec.planPull_wireT := by
  intro f K d
  rw [planPull_wire]
  rfl

end Run
