--
-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/Desc/K1/Law/PinsAtHead.lean: THE TWO COMPARISONS WITH WRITTEN VALUES THAT THE CONDITION
OF THE KIND K1 NAMES (K1Left: pin1 · pin2), EACH IN THE FIELD's OWN TYPE, FROM THE SHARED HEAD, OVER
THE SECOND ISSUE OF THE PROOF FILE's ENTRY TESTS. Two theorems: calls.

  pin1_atAll     the field pin1: P5J.pins_of_laid's first half at the head.
  pin2_atAll     the field pin2 (ALL THREE chains' cuts into sub-protocols are the written ones):
                 another team's P5J.cutIs_of_laid (Johnson/Goal/Skeleton/CutIsOfLaid.lean) at the
                 head.
What this does. It MOVES the two comparisons into the head: they hold because the head says that
the entry tests accepted, and these ask them. It shows of no files that the entry tests accept.
On which ground. Over the entry tests' second list alone; over the first list the two stay
premises.
What is not claimed. That the head can be met at other files than storedPublicFiles and zGap, or at another hash
than secondHashFunction: no example in Lean. Nothing on soundness.

-/
import Johnson.Goal.Skeleton.PinsOfLaid
import Johnson.Goal.Skeleton.CutIsOfLaid
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.PlanWritten (madePinnedAt cutIs)
open ProofFile (Cl)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : First.Look.Place}

/-- **pin1.** -/
theorem pin1_atAll (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true :=
  (P5J.pins_of_laid h.scope h.laid).1

/-- **pin2.** -/
theorem pin2_atAll (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    cutIs (P5J.F0T OnBytes.secondHashFunction Zp Np cF) = true :=
  P5J.cutIs_of_laid h.scope h.laid

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.pin1_atAll
#print axioms VerifiableInference.Desc.K1.pin2_atAll
