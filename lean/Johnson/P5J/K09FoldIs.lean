-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K09FoldIs.lean: THE FIRST CONJUNCT OF `AtMgA.K9Rest` (K09Rest.lean: «there is a laid
list Ld with the facts along the fold») IS THE FIELD «fold» OF THE HEAD WITH THE FACTS
ON EVERY REACHED STATE (`AtMgR`, AtMgR.lean), at the one head's own «reached» and the first
component: held by Lean, so that the sentence «in that field's own form» is no reading. One theorem.

What is said.
  `k9_fold_of_atMgR`: **from `AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) Ld`:
    `FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps`**: its
    field, with `At.links` read as `fullLinks`.

Limits. A PROJECTION. It proves no field of `FoldFacts`; whether the top's head has such an `AtMgR`
in hand is not said here. Nothing on soundness.

-/
import Johnson.P5J.AtMgR
import Johnson.P5J.RowsAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P5J
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (FoldFacts)
open OnBytes.Maker (WholeD)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **THE CONJUNCT IS THAT HEAD's FIELD.** -/
theorem k9_fold_of_atMgR (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (Ld : VerifiableInference.Desc.K12.Door.Laid)
    (R : AtMgR OnBytes.secondHashFunction Z D r Zp Np cF h.toAtMg.rch (fun a => a.1) Ld) :
    FoldFacts h.toAtMg.rch (fun a => a.1) (At.foldD Zp cF Ld) At.reqW fullLinks At.ps :=
  R.fold

end P5J

#print axioms P5J.k9_fold_of_atMgR
