-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Last/FourAtRc.lean: THE DOOR'S FOUR FACTS (`FourFacts`, Johnson/Desc/Last/ShapeDoorFold.lean) INSIDE THE FIRST
TABLE'S LAST PROMISE, UNDER THE ONE HEAD'S `AtMg.rc` (reached at the first chain's end; the public part is a typed
instance's): the premise hR of `sh₃_field`, WHOLE, at the head's own letters. One theorem and two examples.

  **`hR_at_head`**: ∀ (q : ProofFile.InstPub × First.S) (y : Strs), ocEnd (fun a => (a.1, a.2)) (At.N Zp cF) (h.mq 𝔇₀)
    fullLinks At.ps q y → h.rc q → q.2.failed = none → FourFacts V q.2:
    tidy, the book fits and the weights FROM THE HEAD ALONE (`three_at_reach`, Johnson/Desc/Last/FourAtHead.lean);
    the two own seats sit by `own_at_head_two` (Johnson/Desc/Last/OwnAtHead.lean).
  The examples hand it to a binder typed with the tower's reader fun a => (a.1, (fun s => s) a.2), and to one typed with
  `P5J.ocR`.

What stays a premise. hTwo (two tests at border 357, under h.typed z, without a mark) · hsp ·
`PlanSits L M V (At.N Zp cF).indexNo nW` · hNum : (At.N Zp cF).msgsAt none = nW + wMsgs Zp. Letters left: V · L · M · nW.
Limits. At o := `OnBytes.secondHashFunction`. Nothing on soundness or on hiding.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Last.FourAtHead
import Johnson.Desc.Last.OwnAtHead

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

/-- **The four facts, under the head's own "reached at the end".** -/
theorem hR_at_head (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hTwo : ∀ z s₂, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true)
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits L M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ (q : ProofFile.InstPub × First.S) (y : Strs),
      ocEnd (fun a : ProofFile.InstPub × First.S => (a.1, a.2)) (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks
        P5J.At.ps q y → h.rc q → q.2.failed = none → FourFacts V q.2 :=
  fun q y hoc hrc hm =>
    four_of_own h _ q hrc.1 hm (own_at_head_two h 𝔇₀ hTwo hsp T hNum q y hoc hrc hm)

/-- The fit with a binder typed with the tower's reader of a statement. -/
example (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hTwo : ∀ z s₂, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true)
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits L M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, ocEnd (fun a : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub ×
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ => ((a.1, (fun s => s) a.2) :
                      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × P5J.TS))
        (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps q y → h.rc q →
      ((fun a : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub ×
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ => ((a.1, (fun s => s) a.2) :
                      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × P5J.TS)) q).2.failed = none →
      FourFacts V ((fun a : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub ×
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ => ((a.1, (fun s => s) a.2) :
                      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × P5J.TS)) q).2 :=
  hR_at_head h 𝔇₀ hTwo hsp T hNum

/-- The fit with the two later tables' own condition `P5J.ocR`. -/
example (h : P5J.AtMg OnBytes.secondHashFunction Z D r Zp Np cF) {nR : ℕ}
    (𝔇₀ : MgData ProofFile.Inst ProofFile.InstPub P5J.At.Tok numsFull.rows (P5J.colsAt numsFull) nR
      (P5J.At.X Zp))
    {L : Laid} {M : List OracleShape} {V : OwnSeats} {nW : ℕ}
    (hTwo : ∀ z s₂, h.typed z → Reach 0 (cF.blocksInOrder.map Sound.below) (ProofFile.startS Zp) 357 (z, s₂) →
      s₂.failed = none → seatsCarriedB L s₂.book = true ∧ msgShapesB M s₂.st = true)
    (hsp : (K13.whereOf Zp).lin.ownSplitNeeded = false)
    (T : PlanSits L M V (P5J.At.N Zp cF).indexNo nW)
    (hNum : (P5J.At.N Zp cF).msgsAt none = nW + wMsgs Zp) :
    ∀ q y, P5J.ocR (fun a : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub ×
          (P5J.F0T OnBytes.secondHashFunction Zp Np cF).S₁ => ((a.1, (fun s => s) a.2) :
                      (P5J.F0T OnBytes.secondHashFunction Zp Np cF).XiPub × P5J.TS))
        (P5J.At.N Zp cF) (h.mq 𝔇₀) P5J.fullLinks P5J.At.ps h.rc q y →
      q.2.failed = none → FourFacts V q.2 :=
  fun q y ho hm => hR_at_head h 𝔇₀ hTwo hsp T hNum q y ho.1 ho.2 hm

end VerifiableInference.Desc.Last

#print axioms VerifiableInference.Desc.Last.hR_at_head
