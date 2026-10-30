-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K12/AtFile/WFrontSeats.lean: the first chain's last record in numerals,
under the head AtMgA at the older hash.

  told_at_end      the written cut tells 199 messages
  EndWritten       its counts, the messages' shapes, places, trees' shapes and numbers by the written
                   lists
  endWritten       it holds at the end of the first chain's fold, where there is no mark

Limits.
- The full size alone: the library's written values.
- Nothing on completeness, soundness or what is hidden.
-/
import Johnson.Desc.ProofFile.Honest.K12.AtFile.WFrontTrees
import Johnson.Desc.K12.Door.DoorGives
import Johnson.Desc.K12.Door.MsgShapes
import Johnson.Loose.H2K12.ClosedOfPins354
import Johnson.AtFull.Shape.K1NumbersAtHead
import Johnson.Road.K4.K4PinsSends
import Johnson.IMR.ToldPaid
import Johnson.IMR.CountsAtTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K12.AtFile
open OnBytes OnBytes.Slice
open VerifiableInference.Desc (Block Chain OpenedColumn foldBlocks)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (seatsCarriedB bookInOrderB msgShapesB msgShape_at
  place_of_seats numbers_of_book0 msgsOfChain)
open VerifiableInference.Desc.K13.Law (LFull)
open VerifiableInference.PlanWritten (cutOf cutFirstFull toldOfRow toldBefore_cut)
open Johnson.Desc.First.Walk.Tied (Reach reach_of_fold)
open OnBytes.Maker (WholeD)
open P5J (AtMgA)

set_option maxRecDepth 1000000 in
/-- The written cut tells 199 messages. -/
theorem told_at_end : ((cutFirstFull.take 358).map toldOfRow).sum = 199 := by decide +kernel

/-- **The first chain's last record in numerals.** -/
structure EndWritten (e : S) : Prop where
  msgs : e.st.oracles.size = 199
  places : e.book.place.size = 199
  shape : ∀ o, o < 199 → (e.st.oracles[o]?).map (·.shape) = OnBytes.Road.K4.mW[o]?
  place : ∀ o, o < 199 → e.book.place[o]? = LFull.places[o]?
  number : ∀ (z : ℕ) (T : OnBytes.Tree), e.book.trees[z]? = some T → T.number = z
  seats : seatsCarriedB LFull e.book = true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}

/-- **At the end of the first chain's fold, where there is no mark.** -/
theorem endWritten (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) {pI : ProofFile.InstPub} {e₁ : S}
    {rs r₀ : List Fmt.RoundView} {cols c₀ : List OpenedColumn}
    (hf : foldBlocks 0 cF.blocksInOrder (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀))
    (hm : e₁.failed = none) : EndWritten e₁ := by
  have hlen : cF.blocksInOrder.length = 358 := Johnson.AtFull.Shape.flat_len h
  have hfold : foldBlocks 0 (cF.blocksInOrder.take 358) (ProofFile.startS Zp pI) rs cols = .ok (e₁, r₀, c₀) := by
    rw [← hlen, List.take_length]
    exact hf
  have hreach := reach_of_fold (bs := cF.blocksInOrder) (start := ProofFile.startS Zp) (z := pI) 358
    (by rw [hlen]) _ _ _ _ _ hfold
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have h' := h.toAtMg
  have F := ProofFile.Honest.FirstThread.foldFacts_raw h'
    (fun k (a : ProofFile.InstPub × S) => Reach 0 cF.blocksInOrder (ProofFile.startS Zp) k a) (fun a => a)
    (fun _ _ e => e) (P5J.laid_at_head h') (P5J.startB_at_head h')
    (P5J.sendsB_of_madeRow h' (P5J.madeRow_at_head h'))
  have b1 : bookInOrderB 0 e₁.book e₁.roots = true := F.bookInOrder 358 (pI, e₁) hreach hm
  have b2 : seatsCarriedB LFull e₁.book = true := F.seatsCarried 358 (pI, e₁) hreach hm
  have b3 : msgShapesB (msgsOfChain Zp.made.proof.1) e₁.st = true :=
    F.msgShapes 358 (pI, e₁) hreach hm
  have Wr := H2K12.written354_of_pins h'.scope h'.laid.pub h'.pins.1
    (h'.laid.run ▸ LPFD.Full.laidPOf_of h'.laid.value h'.laid.planOk h'.laid.data h'.laid.asks)
  rw [Wr.sends, OnBytes.Road.K4.msgs_sorted] at b3
  obtain ⟨c1, c2, -⟩ := Meaning.Carry.counts_at_cut_paid h.scope h.reads O pI rs cols 358 (by omega)
    (fun b hb => Johnson.AtFull.Shape.plans_at h b (List.mem_of_mem_take hb)) _ hfold
  have hcut : cutOf cF.blocksInOrder = cutFirstFull := (P5J.pins_of_laid h.scope h.laid).2
  have hsum : ((cF.blocksInOrder.take 358).map Meaning.Carry.toldMsgs).sum = 199 := by
    rw [← Meaning.Carry.toldBefore_eq, toldBefore_cut, hcut]
    exact told_at_end
  have hmsgs : e₁.st.oracles.size = 199 := c1.trans hsum
  have hpl : e₁.book.place.size = 199 := c2.trans hmsgs
  exact ⟨hmsgs, hpl, fun o ho => msgShape_at b3 o (by omega), fun o ho => place_of_seats b2 o
    (by omega), fun z T hT => numbers_of_book0 b1 z T hT, b2⟩

end ProofFile.Honest.K12.AtFile

#print axioms ProofFile.Honest.K12.AtFile.told_at_end
#print axioms ProofFile.Honest.K12.AtFile.endWritten
