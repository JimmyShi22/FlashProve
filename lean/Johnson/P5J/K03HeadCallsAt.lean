-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K03HeadCallsAt.lean: "THE OUTPUT HEAD's CALLS ARE SEATED" (the closed test
    `callsSeatedC`: the binder hcalls of K3's condition, K03Due5.lean) FROM THE HEAD ALONE:
    `callsC_at_head_all` (Johnson/HB/LLHARD/K6CallsAtHeadAll.lean) in the binder's
    own letters.
  **`k03_hcalls_head`**: AtMgA at secondHashFunction ⟹ callsSeatedC (At.arr Zp) (At.ms Zp Z.lay) (At.N Zp cF)
      (At.X Zp) (At.layout Zp) (At.num Zp) ‹the constant's sent · l3.rad› x.link ‹l3.seat x.link
      false› = true.
  How, in that file's imports: the test's view (`callsSeatedC_view`) · its text at
      the head comes down to eight names in one list of arrays (`callsText_at_head`, `callNamesB`) ·
      these follow from the names' tie at segment 24 (`callNames_of_tie`), which other files have
      in scope
    (`names_tie_head_all`). Here: Lean takes `callsC_at_head_all`'s letters (dAt h).arr | ms | N
        | sent | l3 for the binder's by unfolding.
Limits. A joining: one call. The head h is a premise. The full size alone.
Limits: that file's. A joining of rules. A member of the head is proved at `storedPublicFiles` and `zGap` alone
(at secondHashFunction; side library AtFullSide/Top/). Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.HB.LLHARD.K6CallsAtHeadAll
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The output head's calls are seated: from the head alone.** -/
theorem k03_hcalls_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    VerifiableInference.Desc.Kinds.Head.Law.AtFold.callsSeatedC (At.arr Zp) (At.ms Zp Z.lay)
      (At.N Zp cF) (At.X Zp) (At.layout Zp) (At.num Zp) (h.toAtMg.𝔇 h.𝔇).sent
      (h.toAtMg.𝔇 h.𝔇).l3.rad x.link ((h.toAtMg.𝔇 h.𝔇).l3.seat x.link false) = true :=
  VerifiableInference.Desc.Kinds.Head.Law.callsC_at_head_all h

end P5J

#print axioms P5J.k03_hcalls_head
