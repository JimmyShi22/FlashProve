-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K8/AllFrontOfChain.lean: THE SMALLNESS TEST, THE HONEST PROVER's SIDE,
AT THE STANDS OF THE HONEST THREAD: `AllFrontAtStand`
(Johnson/Desc/ProofFile/Honest/K8/ValuesJoin.lean), THE PREMISE hFront OF THAT FILE's THREE
SENTENCES, AT ALL 25 SEGMENTS, FROM ONE NAMED PREMISE: `ChainThread` (K8BehindTop.lean), PAID BY
NOBODY. Two implications; none of the library's goals.

  **`leftListAtStand_of_chain`** the scope · the files read · an opening of the description · l < 25
                   · ChainThread T b c Z l ⊢ LeftListAtStand Lk p T b (LeftOverOfList.lean): at
                   every stand the link's list has an entry for each array of whatever ledger the
                   state in front holds open
  **`allFrontAtStand_of_chain`** these and the description's test on its plan ⊢ AllFrontAtStand Lk p
                   T b
WHAT `ChainThread T b c Z l` ASKS: six fields on the thread: T.ft = 0 · its blocks are the first
chain's own (T.bs = c.blocksInOrder) · its border b is 14 l + (if l = 24 then 11 else 9) · b is within its
blocks · every first state that it begins from is the description's own, at some public part · its
stored words lie below the prime.
By: `listSize_at_batch` (Johnson/Desc/K8/Honest/Lists/ListAtBatch.lean) · `allFrontAtStand_of_list`
(AllFrontAtStandAll.lean) · `reach_at_stand` (FrontOfReach.lean) · the library's IM.ground_gets.
WRITTEN A FURTHER TIME: the lines from a stand to a reached state are those of
`leftOverAtStand_of_two` (LeftOverOfTwo.lean).
ONE DEVICE STANDS IN IT: `attribute [-instance] Inst.Model.Scl.ref`. TACTICS THAT SEARCH: `omega` on
one line, on a number of segments alone.
Limits. AN IMPLICATION STILL: `ChainThread` IS PAID BY NOBODY. NO MEMBER: where there is no stand
all is idle. The three sentences' other premises are not touched. IN SCOPE ALONE: the full size; the
first chain. No prover stands in it.
Nothing is claimed on completeness, soundness or hiding.
-/
import Johnson.Desc.ProofFile.Honest.K8.AllFrontAtStandAll
import Johnson.Desc.K8.Honest.Lists.ListAtBatch

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K8
open OnBytes OnBytes.Model
open OnBytes.Model.Stages (LinkH)
open VerifiableInference VerifiableInference.Desc VerifiableInference.Desc.First
open VerifiableInference.Desc.First.K8.Honest
open ProofFile.Honest.K9 (BatStand)

section
variable {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {F : FileDescription ProofFile.Inst}
  {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Claim)} {c : Chain S Claim}
  {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
  {Lk : Link S Claim} {p : Desc.K9.Where}
  {V W X Pb : Type} {Bk : ProverCoinCounts} {T : Thread Bk S Claim V W X Pb} {b : ℕ}

/-- **THE CLAUSE ON THE LINK's LIST IS PAID AT EVERY STAND, AT ALL 25 SEGMENTS.** -/
theorem leftListAtStand_of_chain (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B)
    {l : ℕ} (hl : l < 25) (C : ChainThread T b c Z l) : LeftListAtStand Lk p T b := by
  intro κ s m En ds y cols s' x z G hSt Fk a0 hF h0
  have e := (IM.ground_gets hS hR O.pub O.blank).1
  have e3 : Bs.G₀.built[l]? = some (Bs.G₀.built[l]'(by rw [e]; omega)) :=
    Array.getElem?_eq_getElem _
  obtain ⟨q, hq⟩ := C.begun κ m
  have r := reach_at_stand (ProofFile.startS Z) q hSt C.len hq C.stored
  rw [C.ft, C.bs, C.border] at r
  exact listSize_at_batch hS hR O hl e3 r Fk a0 hF h0

/-- **THE PREMISE OF THE THREE SENTENCES, AT ALL 25 SEGMENTS, FROM ONE NAMED PREMISE.** -/
theorem allFrontAtStand_of_chain (hS : VerifierAndGoals.InScope P = true)
    (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    {l : ℕ} (hl : l < 25) (C : ChainThread T b c Z l) : AllFrontAtStand Lk p T b :=
  allFrontAtStand_of_list hS hR O hOk hl C (leftListAtStand_of_chain hS hR O hl C)

end

end ProofFile.Honest.K8

#print axioms ProofFile.Honest.K8.leftListAtStand_of_chain
#print axioms ProofFile.Honest.K8.allFrontAtStand_of_chain
