-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/- Johnson/P2LawR/CoreOfPlanAtHead.lean: WHAT STAYS OF THE TESTS ON THE LAST TABLE's PLAN, AT THE
JOIN's OWN LETTERS (`P5J.L0.CoreJ`, Johnson/P5J/L0/PlanAtHead.lean), FROM THE HEAD AND ONE TEST
WITH CODE. One theorem. A joining.

  `core_of_planAt_head`: `core_of_planAt` (Johnson/P2LawR/CoreOfPlanAt.lean) with its premise hy
    (`madePinnedAt … = true`) met from the head by `P5J.AtMg.made_accepts`
    (Johnson/P5J/NumbersAtHead.lean). ONE PREMISE BESIDE THE HEAD IS LEFT:
    tP : `planAtAllB … = true` at the join's letters: at the first stage each member's plan fits:
      what `LLT25.PlanAt` asks beyond the field seats.
    OVERTAKEN: `core_of_two_radii` (Johnson/P2LawR/CoreOfTwoRadii.lean), its two tests on radii met
    by `P5J.AtMg.two_radii` (Johnson/P2LawR/TwoRadiiAtHead.lean), has the same end from the head
    alone: so it is called in Johnson/P2LawR/LastLeftAlone.lean.

Limits. tP is a premise: NOTHING IS EVALUATED HERE. A member of the head is proved at `storedPublicFiles` and
`zGap` alone (at secondHashFunction; side library AtFullSide/Top/). At `OnBytes.secondHashFunction` alone. The
full size alone. Nothing on soundness.

One limit is raised: maxRecDepth to 40000.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P2LawR.CoreOfPlanAt
import Johnson.P5J.NumbersAtHead

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P2Law.Left
open P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker OnBytes.Flat
open OnBytes.Road OnBytes.RunA
open Iop Prob _root_.Run _root_.Run.PQ
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Third (SharedOut firstOfS sharedOfEnd)
open VerifiableInference.Desc.Third.Law
open VerifiableInference.Desc.First (ModelPart Item Numbers)
open _root_.Desc.K14 (St)
open _root_.Desc.K14.Law
open ToldDesc (p14At)
open LLT25

open P2Law.PlanLeft

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The premise C of `planOk₃_at_join`, from the head and one test with code.** -/
theorem core_of_planAt_head (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x)
    (tP : planAtAllB (F0T OnBytes.secondHashFunction Zp Np cF) (p14At Zp).codes (frJ D Zp Np cF)
      H2K.Member.rWFull (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ Np.W).nums.stages (mineJ Z Zp Np cF) = true) :
    ∀ dB dt, L0.StretchJ OnBytes.secondHashFunction D Zp Np cF dB dt →
      L0.CoreJ OnBytes.secondHashFunction Z D Zp Np cF (L0.sevenJ OnBytes.secondHashFunction Zp Np cF) dB dt (L0.ldAt Zp) :=
  core_of_planAt h h.toAtMg.made_accepts tP

end P2Law.Left

#print axioms P5J.AtMg.made_accepts
#print axioms P2Law.Left.core_of_planAt_head
