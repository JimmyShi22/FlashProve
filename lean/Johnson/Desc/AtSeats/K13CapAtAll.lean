-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K13CapAtAll.lean: KIND K13's PREMISE hCapB, PAID AT THE CLOSED
CONSTANT (P5J.mgAtAll) UNDER THE ACCEPT OF ONE OF THE ENTRY TESTS' COMPARISONS WITH WRITTEN VALUES.
hCapB is the binder capB hA.𝔇.P13 = true of k13_kindA_tight
(Johnson/Desc/AtSeats/K13KindRowA.lean): the three comparisons of the kind's error bounds with the
cap of 128 bits (Johnson/Desc/AtSeats/K13LawCap.lean).

OBJECT. capB at the constant's own letter P13, which is K13.whereOf Zp by unfolding.
USER. k13_kindA_tight's callers: the binder hCapB falls; hP1 comes in (it stands there already for
hPl: Johnson/Desc/AtSeats/K13PlanM3At.lean).
LETTERS. o, Zl, D, r₀, Zp, Np, cF, x₀: the row's own.

One call: capB_in_scope (K13CapInScope.lean). Its five premises, each with its payer:
  the scope and "the public part is made": the head's fields scope and laid.pub
  hs, hf   the two law forms of the comparison: sized_of_made, first_of_made at hP1
           (Johnson/Desc/Ok/PlanWritten/MadeTestLaws.lean)
  hl       "the value is laid": laidPOf_of (Johnson/Desc/Laid/ProofFullLaw.lean) at the head's
           fields laid.value, laid.planOk, laid.data, laid.asks, with laid.run
The closed fact beneath is capB_real (thirteen rows, no proof of work: Lean's kernel); its negative
test is capB_no (at 2 ^ 70 rows the comparisons reject): both in K13LawCap.lean.

What is not claimed. That hP1 accepts at any files. No member of the head hA. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13CapInScope
import Johnson.P5J.MgAtAll
import Johnson.Desc.Ok.PlanWritten.MadeTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.K13.Law

open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (madePinnedAt sized_of_made first_of_made)
open ProofFile (Cl)

/-- **hCapB of k13_kindA_tight, to the letter.** -/
theorem capB_atAll {o : ProofFile.SecondHashFunctionArgument} {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA o Zl D r₀ Zp Np cF x₀)
    (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    capB hA.𝔇.P13 = true :=
  HashBuild.capB_in_scope hA.scope hA.laid.pub (sized_of_made hP1) (first_of_made hP1)
    (hA.laid.run ▸ LPFD.Full.laidPOf_of hA.laid.value hA.laid.planOk hA.laid.data hA.laid.asks)

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.capB_atAll
