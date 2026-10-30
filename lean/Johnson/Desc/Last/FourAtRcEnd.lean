-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/FourAtRcEnd.lean: THE DOOR'S FOUR FACTS UNDER THE ONE HEAD'S `AtMg.rc`, THE ONE FACT ON REACHED STATES THAT STAYS
BEING ASKED AT THE FIRST CHAIN'S LAST STATE ALONE. Two theorems: calls.

  `own_at_head_end`: `own_at_head_two`'s end (Johnson/Desc/Last/OwnAtHead.lean) from hEnd in hTwo's place
    (`ownSitsB_at_promise_end`, Johnson/Desc/Last/TwoAtEnd.lean), with "no split" off the head (`hsp_at_head`).
  **`hR_at_head_end`**: ∀ (q : ProofFile.InstPub × First.S) (y : Strs), ocEnd (fun a => (a.1, a.2)) (At.N Zp cF) (h.mq 𝔇₀)
    fullLinks At.ps q y → h.rc q → q.2.failed = none → FourFacts V q.2.

What stays a premise. hEnd : ∀ z s, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (z, s) → s.failed = none →
seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true · `PlanSits L M V (At.N Zp cF).indexNo nW` ·
hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp. Letters left: V · L · M · nW.
Limits. At o := `OnBytes.secondHashFunction`. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.FourAtRc
import Johnson.Desc.Last.NoSplitAtHead
import Johnson.Desc.Last.TwoAtEnd

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.Desc.Last
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Slice
open VerifiableInference.Desc.Sound
open ToldDesc (PlanSits)
open VerifiableInference.Desc.K12.Door (Laid seatsCarriedB msgShapesB)
open Johnson.Desc.First.Walk.Tied (Reach)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain P5J.TS ProofFile.Cl}

/-- The two own seats sit, the two tests asked at the last state alone. -/
theorem own_at_head_end (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hEnd : ∀ z s, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (z, s) →
      s.failed = none → seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true)
    (T : PlanSits L M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, ocEnd getAt (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps q y → h.rc q →
      (getAt q).2.failed = none → ownSitsB V (getAt q).2 = true := by
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  rintro ⟨z, s⟩ y hoc hrc hm
  have he' : Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) cF.blocksInOrder.length (z, s) := hrc.1
  rw [flat_358 h.scope h.reads O] at he'
  exact ownSitsB_at_promise_end h.scope h.reads O
    (handsBack_and (ToldDesc.handsBack_below 0 cF.blocksInOrder (ProofFile.startS Zp)) h.typed) getAt
    (fun _ _ => rfl) (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps pinI_open_full
    (mq_indexIs h 𝔇₀) (hsp_at_head h) T hNum (fun z s hr hm₂ => hEnd z s hr.1 hr.2 hm₂) (z, s) y hoc
    ⟨hrc.2, he'⟩ hm

/-- **The four facts, under the head's own "reached at the end": three premises, one of them on a reached state, at the
last state alone.** -/
theorem hR_at_head_end (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hEnd : ∀ z s, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 358 (z, s) →
      s.failed = none → seatsCarriedB L s.book = true ∧ msgShapesB M s.st = true)
    (T : PlanSits L M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ (q : ProofFile.InstPub × First.S) (y : Strs),
      ocEnd (fun a : ProofFile.InstPub × First.S => (a.1, a.2)) (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks
        P5J.At.ps q y → h.rc q → q.2.failed = none → FourFacts V q.2 :=
  fun q y hoc hrc hm =>
    four_of_own h _ q hrc.1 hm (own_at_head_end h 𝔇₀ hEnd T hNum q y hoc hrc hm)

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.own_at_head_end
#print axioms VerifiableInference.Desc.Last.hR_at_head_end
