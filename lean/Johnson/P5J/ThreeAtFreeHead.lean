-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/ThreeAtFreeHead.lean: `h.Three h.free` FROM THE HEAD AND ONE TEST AT ITS OPENING.
One theorem.

`three_at_free_no_states` (Johnson/P5J/ThreeAtFreeNoStates.lean) leaves hr, hB, hL, T and hNum.
Where the laws ask thirteen rows or more (by the file's rule that tests are only appended:
Johnson/Desc/Laid/ProofAsks.lean; this library's list has fourteen), four of the five have payers
from the head alone.
Here they are called:

  hr: `AtMg.row_at_head` (Johnson/P5J/NumAtHeadCall.lean).
  hL: `AtMg.laid_codes_at_head` (Johnson/P5J/PlanSitsCore.lean): the value is the written `LFull`.
  T: `Second.Seam.planSits_at_N` (Johnson/Second/Seam/PlanSitsInScope.lean), at `LFull`, 4 and 197;
    its pin by `pinnedAt_of_row` from hr, its return of `proofDataAndDecisionOfPublicFiles` by `Sh.laidPOf_at_head`; the 4 is
    the head's index number by `AtMg.indexNo_at` (Johnson/P5J/PlanSitsCore.lean).
  hNum: `AtMg.num_at_head` (Johnson/P5J/NumAtHeadCall.lean), at nW := 197.

  **`three_at_free_head`**: h.Three h.free. WHAT STAYS: hB ALONE: at the head's opening of the files
    one test with code accepts (`sendsAreB` at 358). Its payer: `hB_paid`
    (Johnson/IMR/EndFiveMade.lean), under `madeRow`, which the head holds where the laws ask
    thirteen rows or more.

WHERE THE FOUR WENT. They are not proved of what the maker makes of given public files: THEY HAVE
MOVED INTO THE HEAD. Where the laws ask thirteen rows or more, the head's field `asks` holds two
rows of tests that compare with written values (`madeRow`, `cutRow`); hr, hL, T and hNum follow
from these.
So the price is paid in whether the head can be met, not in a premise here.
Over eight rows these payers do not compile. The numerals are the written values': the full size
alone.
Read against Johnson/P5J/ThreeAtFreeNoStates.lean, Johnson/P5J/NumAtHeadCall.lean,
Johnson/P5J/PlanSitsCore.lean, Johnson/Desc/K14/Law/SharedConstChainOkAtHead.lean and
Johnson/Second/Seam/PlanSitsInScope.lean, which may still turn.
Limits. A joining: it pays nothing by itself. A member of the head is proved at `storedPublicFiles` and `zGap`
alone (at secondHashFunction; side library AtFullSide/Top/).
The weight of the fact on reached states rests on `IM.hEnd_paid`.
At the second hash function `OnBytes.secondHashFunction` alone. No soundness follows from it. Nothing on hiding.

-/
import Johnson.P5J.ThreeAtFreeNoStates
import Johnson.P5J.NumAtHeadCall
import Johnson.Second.Seam.PlanSitsInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

open scoped ENNReal

namespace P5J

open Meaning
open Inst.Model
open OnBytes OnBytes.Road OnBytes.Flat OnBytes.Maker OnBytes.Slice OnBytes.RunA
open OnBytes.Model.Verify (publicOf)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block FileDescription Place Strs Wit)
open VerifiableInference.Desc.First (ModelPart Numbers start)
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain
open _root_.Iop (oneExternalString Tr)
open _root_.Iop.Reduction (steps)
open _root_.Run _root_.Run.PQ

open VerifierAndGoals.AtTheName
open VerifiableInference.Desc (Chain KindName)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)

open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB sendsAreB snAt laidAtCodes
  msgsOfChain)
open Johnson.Desc.First.Walk.Tied (Reach)

open VerifiableInference.PlanWritten (madeRow keyOfScan fullKey)

/-- **`h.Three h.free` from the head and one test at its opening.** -/
theorem three_at_free_head
    (hB : ∀ Bs base A B, IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL
      (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF A B →
      sendsAreB Zp.made.proof.1 358 (snAt Zp Bs.G₀ IM.placesW) = true) : h.Three h.free :=
  three_at_free_no_states h h.toAtMg.row_at_head hB h.toAtMg.laid_codes_at_head
    (by
      rw [h.toAtMg.indexNo_at]
      exact Second.Seam.planSits_at_N h.scope h.laid.pub
        (VerifiableInference.PlanWritten.pinnedAt_of_row h.toAtMg.row_at_head)
        (Desc.K14.Law.Sh.laidPOf_at_head h) cF)
    h.toAtMg.num_at_head

end P5J

#print axioms P5J.three_at_free_head
