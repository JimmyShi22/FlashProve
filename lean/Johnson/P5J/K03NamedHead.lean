-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03NamedHead.lean: THE LOOKUP ARGUMENT's LAW: THE NAMED TEST namedC FALLS UNDER THE
HEAD. Two theorems.
  `AtMgA.namedC_head`: l < 25 gives `h.namedC l = true`: `K03.namedB` at segment l
    (Johnson/P5J/K03OneOwn.lean) is, line for line, segment l's share of `seatsNamedC`
    (Johnson/P5J/SeatsNamedC.lean), and that test's accept at these terms is the head's own field
    `At.PlanOk.named`.
  `AtMgA.own_of_off`: the ledger's field "own" at link l < 25 from `h.toAtMg.offC = true` alone.
So of the three named tests of Johnson/P5J/K03OneOwnAt.lean one was no debt: namedB is a twin of a
share of a test that the head holds; it was typed without that being seen.
Limits. The head is a premise. Nothing on soundness.

-/
import Johnson.P5J.K03OneOwnAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Maker
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The named test on "own"'s first half accepts under the head.** -/
theorem AtMgA.namedC_head (h : AtMgA o Z D r Zp Np cF x) {l : ℕ} (hl : l < 25) :
    h.namedC l = true :=
  List.all_eq_true.1 h.plan.named l (List.mem_range.2 hl)

/-- **The ledger's "own" at link l, from the one test on the pads.** -/
theorem AtMgA.own_of_off (h : AtMgA o Z D r Zp Np cF x) {l : ℕ} (hl : l < 25)
    (hC : h.toAtMg.offC = true) :
    OwnNamed (At.X Zp) (h.toAtMg.𝔇 h.𝔇).sent (At.num Zp) (_root_.Meaning.tlAt (At.X Zp)) l
      (h.toAtMg.𝔇 h.𝔇).arr (h.toAtMg.𝔇 h.𝔇).ms (h.toAtMg.𝔇 h.𝔇).N :=
  h.own_at hl (h.namedC_head hl) hC

end P5J

#print axioms P5J.AtMgA.namedC_head
#print axioms P5J.AtMgA.own_of_off
