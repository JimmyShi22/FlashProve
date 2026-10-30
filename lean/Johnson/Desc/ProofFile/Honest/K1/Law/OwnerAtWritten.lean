-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/Law/OwnerAtWritten.lean: THE SHARED "SENDING" (the kind K1) AND THE
MAKER OF THE BOOK OF COINS: THE MAKER's SEARCH FOR THE INDEX-MASK MESSAGE (ownerOf,
Honest/BookEntries.lean, as spendingBook calls it, Honest/BookAll.lean), AT THE LIBRARY's WRITTEN
DATA: ITS OWNER IS THE OPENING's SENDER; ITS START AMONG THAT PART's COINS IS OUR maskStart
(Honest/K1/MaskLaw.lean) AT MESSAGE NUMBER 4; ITS SEARCH PICKS NUMBER 4. PUBLIC DATA ALONE: the
blocks' places and rounds' names, the sendings' notices, plans, counts, addresses: where a run of
coins begins, never what stands in it. Four theorems; no definition.

The written data. The blocks that the library's written cut and written declared rounds of the first
chain spell (P2Law.ProofPlan.blocksOfRows, Johnson/AtFull/ProofPlan/WrittenDesc.lean; cutFirstFull,
Johnson/Desc/Ok/PlanWritten/CutLit.lean; declProofFull, Johnson/AtFull/ProofPlan/WP.lean) · the
first chain's written sendings (Johnson.G.proofSendsFull, Johnson/G/SendsWritten.lean) · the second
chain's written declared rounds · the opening's written plan K1.parGF with the ride rideOf
(firstFold K1.qFull).

  - idxOwnerW: the owner is ⟨K1.parGF.place, 0⟩, and the start among the coins of E is maskStart
    K1.parGF ‹the ride› 4. By evaluation in Lean's kernel.
  - idxPickW: the first written sending is "link 0, moment 0", and the first of its messages that
    meets isIndexMaskMsg is number 4.
  - idxOwnerW_bites: A NEGATIVE TEST AND MORE: of the opening's messages NUMBER 4 ALONE has that
    start.
  - idxOwnerW_head: UNDER h (the library's head: A HYPOTHESIS), O: the same left side; on the right
    the plan and the ride at the description's own ground: K1.firstPar Bs.G₀.first (K1.gpOf Zp),
    rideOf (firstFold Bs.G₀.first).

For whom. The law on the book asks, as a premise, that "at whichever message the maker's
ownerOf returns" the owner is ⟨J.P.place, 0⟩ and the start is maskStart J.P J.ride n. This is that
sentence AT THE WRITTEN DATA, with n = 4: K1NumAtHead.lean's index_two has the same 4 by the seat.

Limits. IT IS THAT PREMISE's FORECAST, NOT ITS PAYMENT: that the blocks of the head's description,
its rounds and the maker's sendings ARE the written ones is not said here. THE FULL SIZE ALONE.
Evaluations in Lean's kernel (decide +kernel): no compiled code. Nothing on any property.
Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.BookWhole
import Johnson.Desc.ProofFile.Honest.K1.MaskLaw
import Johnson.Desc.ProofFile.Honest.K1.Law.FitsWritten
import Johnson.AtFull.ProofPlan.WrittenDesc
import Johnson.AtFull.ProofPlan.WP
import Johnson.Desc.Ok.PlanWritten.CutLit
import Johnson.G.SendsWritten

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open VerifiableInference.Desc
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K1 (parGF)
open OnBytes.Maker (WholeD)
open _root_.Desc.K14.Law (seatZ secondAt)

/-- **THE MAKER's INDEX-MASK MESSAGE AT THE WRITTEN DATA**: its owner; its start among the coins of
E. -/
theorem idxOwnerW : (ownerOf indexMaskRun
      (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
        P2Law.ProofPlan.declProofFull.1)
      Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
      isIndexMaskMsg).map
      (fun m => (m.owner, m.base.e)) =
    some ((⟨parGF.place, 0⟩ : Addr), maskStart parGF (rideOf (firstFold K1.qFull)) 4) := by
  decide +kernel

/-- The maker's search picks message number 4 of the first written sending. -/
theorem idxPickW : (Johnson.G.proofSendsFull.1.sends.head?.map fun x =>
    (x.label, x.sent.findIdx isIndexMaskMsg)) = some ("link 0, moment 0", 4) := by
  decide +kernel

/-- Of the opening's messages number 4 alone has that start. -/
theorem idxOwnerW_bites : ((List.range parGF.sent.size).filter fun n =>
    decide ((ownerOf indexMaskRun
      (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
        P2Law.ProofPlan.declProofFull.1)
      Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
      isIndexMaskMsg).map (·.base.e) =
      some (maskStart parGF (rideOf (firstFold K1.qFull)) n))) = [4] := by
  decide +kernel

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : First.Look.Place} {Bs : ProofFile.PureBase}
  {base₀ : List (Block S ProofFile.Cl)}

/-- **THE SAME, AT THE PLAN AND THE RIDE OF THE DESCRIPTION's OWN GROUND**, under the head. -/
theorem idxOwnerW_head (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np)) :
    (ownerOf indexMaskRun
      (P2Law.ProofPlan.blocksOfRows VerifiableInference.PlanWritten.cutFirstFull
        P2Law.ProofPlan.declProofFull.1)
      Johnson.G.proofSendsFull.1 P2Law.ProofPlan.declProofFull.2.2 "link 0, moment 0"
      isIndexMaskMsg).map
      (fun m => (m.owner, m.base.e)) =
    some ((⟨(K1.firstPar Bs.G₀.first (K1.gpOf Zp)).place, 0⟩ : Addr),
      maskStart (K1.firstPar Bs.G₀.first (K1.gpOf Zp)) (rideOf (firstFold Bs.G₀.first)) 4) := by
  rw [K1.eG_atAll h O (K1.pin1_atAll h),
    firstFold_shape (q' := K1.qFull) ((K1.hs_atAll h O (K1.pin1_atAll h)).trans ?_)]
  · exact idxOwnerW
  · rfl

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.idxOwnerW
#print axioms ProofFile.Honest.K1.idxPickW
#print axioms ProofFile.Honest.K1.idxOwnerW_bites
#print axioms ProofFile.Honest.K1.idxOwnerW_head
