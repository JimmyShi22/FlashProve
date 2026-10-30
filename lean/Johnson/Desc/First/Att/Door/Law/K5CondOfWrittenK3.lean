-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5CondOfWrittenK3.lean: kind K5: **A PAYMENT BENEATH THE KIND's NAMED CONDITION: "REST → CONDITION", WHERE THE HEAD BEARS ITS TEST ON THE LOOKUP ARGUMENTS' SEATS**: the form of k5CondAt_of_written
(Door/Law/K5CondOfWritten.lean) without the field someMem, which is a theorem from that test (someMem_all, Door/Law/K5SentOfK3.lean). It turns nothing of the condition.
Compiled with the whole library.

(Where this and lean/THEOREM.md differ, the page holds.)
ONLY OVER A VERSION OF P5J/MgAtAll.lean WHOSE HEAD HAS THE FIELD k3.

Main name: **k5CondAt_of_writtenK3**: the head · madeRow's accept · the written cut · the listed seats are L · k5WrittenB = true · pads · cells → K5CondAt h L.
IS IT EMPTY HERE? AN IMPLICATION. THAT k5WrittenB IS true IS NOT SHOWN. A MEMBER OF THE HEAD IS PROVED AT storedPublicFiles AND zGap ALONE (AT secondHashFunction; SIDE LIBRARY AtFullSide/Top/).
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.Door.Law.K5CondOfWritten
import Johnson.Desc.First.Att.Door.Law.K5SentOfK3

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace H2K5.Door
open OnBytes OnBytes.Model OnBytes.Maker
open VerifiableInference.Desc VerifiableInference.Desc.First VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K12.Door (Laid)
open VerifiableInference.PlanWritten (madeRow cutFirstFull)
open P5J (AtMgA TS)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Look.Place}
  {h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x}

/-- **REST → CONDITION, someMem paid by the head's own test.** -/
theorem k5CondAt_of_writtenK3 (hm : madeRow Zp = true) (hc : VerifiableInference.PlanWritten.cutOf cF.blocksInOrder = cutFirstFull) {L : Laid}
    (hL : P5J.At.laid? Zp = some L) (hW : k5WrittenB = true) (pads : PadsAll h)
    (cells : ∀ g, g < 12 → ∀ (a : Attention.Plan) (x₁ : Look.Place), (P5J.At.X Zp).A[g]? = some a →
      lookAt (P5J.At.X Zp) (2 * g + 1) false = some x₁ → ∃ idx, K5CellsCond h a x₁ idx) : K5CondAt h L :=
  k5CondAt_of_written hm hc hL hW ⟨pads, cells, fun _ hg _ hx => someMem_all h hg hx⟩

end H2K5.Door

#print axioms H2K5.Door.k5CondAt_of_writtenK3
