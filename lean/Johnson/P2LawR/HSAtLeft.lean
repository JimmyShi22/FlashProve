-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P2LawR/HSAtLeft.lean: THE FIELD hS OF WHAT IS LEFT OF THE LAST CHAIN's FIELD AT THE VALUE
(`P5J.AtMgA.LastLeft`, Johnson/P5J/L0/LastFreeT.lean), IN ITS OWN TEXT at o := `OnBytes.secondHashFunction`,
FROM THE HEAD AND ONE NAMED TEST ON THE PLAN. Two theorems. Joinings.

  `laid_at_head`: off the head: `LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r)`: the converse
    `LPFD.Full.laidPOf_of` (Johnson/Desc/Laid/ProofFullLaw.lean) at the head's fields value, planOk,
    data, asks, turned by its field run. Every o.
  `hS_at_left`: (h : `AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x`) (hy) ⊢ the field hS: at every last
    state of the first chain inside its whole last promise, reached at a typed instance and without
    a mark, the handed book numbers the messages as the plan's list of seats does.
    ONE CALL of `Meaning.K2.hS_one_test` (Johnson/LTPileR/SeatsOneTest.lean).
    OFF THE HEAD: the scope · an opening · the test on the list of rounds · `laid_at_head`.
    WHAT STAYS, BY NAME: hy : `madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true`: a
      test with code on written values of the plan.

Limits. hy is shown nowhere here. At `OnBytes.secondHashFunction` alone; in scope alone. That a state is reached
is not said. No example. Nothing on soundness.

One limit is raised: maxRecDepth to 40000.

Terms: lean/GLOSSARY.md.
-/
import Johnson.P5J.L0.LastFreeT
import Johnson.LTPileR.SeatsOneTest
import Johnson.Desc.Laid.ProofFullLaw

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

open VerifiableInference.PlanWritten (madePinnedAt)

variable {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r' : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **The value's own "laid", off the head.** -/
theorem laid_at_head (h : AtMg o Z D r' Zp Np cF) :
    LPFD.Full.proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r') := by
  rw [h.laid.run]
  exact LPFD.Full.laidPOf_of h.laid.value h.laid.planOk h.laid.data h.laid.asks

/-- **The field hS, from the head and one named test.** -/
theorem hS_at_left (h : AtMgA OnBytes.secondHashFunction Z D r' Zp Np cF x)
    (hy : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true) :
    ∀ q y, ocEnd (L0.getL OnBytes.secondHashFunction Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks
    (First.flatPlaces true fullLinks true) q y → h.toAtMg.rc q → ((L0.getL OnBytes.secondHashFunction Zp Np cF)
    q).2.failed = none → ∀ f, firstOfS ((L0.getL OnBytes.secondHashFunction Zp Np cF) q).2 = some f →
    SeatsNumber (At.seats Zp) f.book := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  exact Meaning.K2.hS_one_test h.scope O h.laid.planOk hy (laid_at_head h.toAtMg) Np
    (fun p => ∃ z : LPFD.Full.XF × RecFull, p = (LPFD.Full.instanceAsPlainRecord z).pub)
    (ocEnd (L0.getL OnBytes.secondHashFunction Zp Np cF) (At.N Zp cF) (h.toAtMg.mq h.𝔇) fullLinks
      (First.flatPlaces true fullLinks true))

end P2Law.Left

#print axioms P2Law.Left.laid_at_head
#print axioms P2Law.Left.hS_at_left
