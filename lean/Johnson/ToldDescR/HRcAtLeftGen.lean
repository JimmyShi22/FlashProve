-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/HRcAtLeftGen.lean: no soundness is claimed.
A bridge toward hRc_at_free (Johnson/ToldDescR/HRcAtFree.lean): ToldDesc.hRc_at_left_pinned (HRcAtLeftPinned.lean, a file that is not in this library) once more, general in the first table's meaning.
Why. hRc_at_left_own | _pinned (declared nowhere in this library) take two names (KeyHead.getAt · KeyHead.mq_indexIs) from OwnAtHeadKey.lean (not in this library), a file that names h.kf 𝔏 | h.rc 𝔏. Here nothing of the tower above P5J.AtMg is imported: the reader of the statement is written out ((a.1, a.2)), the meaning Mg₁ is a letter, and what was drawn from h.mq 𝔇₀ is one premise: hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC 4 x.2 (hIdx is in it).
  **hRc_at_left_gen**   the head · Mg₁ with hII · hL · K · T · hNum · cutRow · madeRow ⇒ ∀ q y, ocEnd (fun a => (a.1, a.2)) (At.N Zp cF) Mg₁ fullLinks At.ps q y → (EndAt₁ (F0T …) q ∧ K q) → q.2.failed = none → rcLastB 0 (vAt Zp (At.N Zp cF)) L (p14At Zp).codes q.2 = true
Called: what hRc_at_left_own and hRc_at_left_pinned call, but for the two names above.
The full size alone. No member. Nothing on soundness.
-/
import Johnson.ToldDescR.HRcAtLeft
import Johnson.Desc.Last.TwoAtEnd
import Johnson.Desc.Last.IndexAtEndAll
import Johnson.P2LawR.SampleStepAt
import Johnson.IMR.EndTwoPaid
import Johnson.IMR.SendsPlanPinned
import Johnson.IMR.EndFiveMade
import Johnson.Desc.Ok.PlanWritten.CutTestLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ToldDesc
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.K12.Door (Laid msgsOfChain)
open Johnson.Desc.First.Walk.Tied (Reach EndAt₁)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl}

/-- **hRc at the one head, general in the first table's meaning.** -/
theorem hRc_at_left_gen (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {W : Type}
    (Mg₁ : First.Meaning ProofFile.InstPub W)
    (hII : ∀ x, Mg₁.pub .indexIs x = K13.indexIsC 4 x.2)
    {L : Laid} (hL : K12.Door.laidAtCodes Zp.first.codes Zp.made.proof.1 = some L)
    (K : ProofFile.InstPub × S → Prop)
    (T : PlanSits L (msgsOfChain Zp.made.proof.1) (LLT25.vAt Zp (P5J.At.N Zp cF)) 4 197)
    (hNum : (P5J.At.N Zp cF).msgsAt none = 197 + Last.wMsgs Zp)
    (hcut : VerifiableInference.PlanWritten.cutRow (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp = true)
    (hy : VerifiableInference.PlanWritten.madeRow Zp = true) :
    ∀ q y, ocEnd (fun a : ProofFile.InstPub × S => (a.1, a.2)) (P5J.At.N Zp cF) Mg₁ P5J.fullLinks
        P5J.At.ps q y →
      (EndAt₁ (P5J.F0T OnBytes.secondHashFunction Zp Np cF) q ∧ K q) → q.2.failed = none →
      rcLastB 0 (LLT25.vAt Zp (P5J.At.N Zp cF)) L (p14At Zp).codes q.2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hB := Meaning.K2.hB_paid (c := cF) h.scope h.laid.planOk hy
  have hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false := by
    show Zp.first.lin.ownSplitNeeded = false
    rw [(IM.pins hy).2.2.1]
    decide +kernel
  have h358 := ToldDesc.flat_358 h.scope h.reads O
  refine hRc_at_left h hB hL (P5J.At.N Zp cF) K _ ?_
    (VerifiableInference.PlanWritten.cut_of_row hcut).1 (IM.sendsPlanB_pinned hy) T.seatI T.seatW
    (P2Law.sampleStep_at_index hy) (P2Law.sampleStep_at_W hy)
  intro q y ho hq hm
  have e : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) cF.blocksInOrder.length q := hq.1
  have e8 : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 q := by
    rw [h358] at e
    exact e
  exact Last.ownSitsB_at_promise_end h.scope h.reads O
    (handsBack_below 0 cF.blocksInOrder (ProofFile.startS Zp)) (fun a : ProofFile.InstPub × S => (a.1, a.2))
    (fun _ _ => rfl) (P5J.At.N Zp cF) Mg₁ P5J.fullLinks P5J.At.ps Last.pinI_open_full hII hsp T
    hNum
    (fun z s hr hm' => ⟨(Meaning.K2.five_at_end_planOk h.scope O h.laid.planOk
      (hB Bs base _ _ O) hL (z, s) (by rw [h358]; exact hr) hm').2.2.2.2,
      IM.shapesEnd_paid h.scope h.reads O h.laid.planOk (hB Bs base _ _ O) hr hm'⟩)
    q y ho e8 hm

end ToldDesc

#print axioms ToldDesc.hRc_at_left_gen
