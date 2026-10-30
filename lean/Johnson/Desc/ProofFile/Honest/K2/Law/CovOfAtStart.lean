-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K2/Law/CovOfAtStart.lean: UNDER THE LIBRARY's HEAD: WHERE THE
DESCRIPTION's TEST ON THE INSTANCE SAYS YES (`FileDescription.okStart`), THE COVERED POSITIONS THAT THE
DATA OF THE MESSAGES "U3" ARE MADE OF (`covOf`, Johnson/HonestTrace/U3Rows.lean, of other authors)
ARE THERE AND PASS THE TEST ON THEIR SIZES AT THE HEAD's NUMBER OF POSITIONS. PUBLIC DATA ALONE: the
public part, the ground, an instance's request. Two lemmas with their proofs; no definition; none of
the library's goals.

  `vocab_pos`               under the head and the opening: the vocabulary is not empty
  `covOf_sized_of_okStart`  under the head and the opening, at the description's own ground: the
                            test's yes ⊢ ((covOf Zp Bs.G₀ ξ).toOption.getD default).sized
                            Bs.G₀.W.hS.T = true

Why. By reading, that Bool is all that the kind's public test on a filling (`publicOk`,
Honest/K2/Sim.lean) reads of the instance at the frame's authors' data `widerRows`
(Honest/AtPureWider.lean), and it reads it at one place of 25.

By. `reqOk_of_okStart` (Johnson/AtFull/Shape/ReqOkOfStart.lean) · `IM.Open.W`, `IM.Open.public`
(Johnson/IMR/SeatOpen.lean) · `nums_at` (Johnson/AtFull/Shape/ReqReplyReach.lean): the two numbers
of positions are one · `coveredAt_of_reqOk`, `coveredAt_sized` (CoveredAtReturns.lean of this
folder) · in `vocab_pos`: `V_public` (Johnson/Goal/Meaning/HeadStartScope.lean), `hS_in_scope`
(Johnson/Goal/Meaning/HeadShapeScope.lean). THE THREE LINES OF `vocab_pos` stand inside the proof of
the library's `LPFK9` lemma on the maker's base (Johnson/LPFK9R/BaseOfPubWhole.lean): no theorem
states them.

WHAT IT IS NOT. NOT `publicOk`: FROM THIS Bool TO "the data lay the array U3 at the head's message"
IS A STEP THAT IS NOT HERE; that the data lay every other array that the kind's sides read is not
said either. Nothing on the reply, the weights or a trace.

Limits. The full size and the format's second hash function, as the head has them. It imports a file under
Johnson/Goal/Meaning/ straight, and takes that file's own imports. Nothing on any property.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.CoveredAtReturns
import Johnson.AtFull.Shape.ReqOkOfStart
import Johnson.AtFull.Shape.ReqReplyReach
import Johnson.Goal.Meaning.HeadShapeScope
import Johnson.HonestTrace.U3Rows

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K2.Law
open VerifiableInference.Desc (Block Chain)
open VerifiableInference.Desc.First (S)
open OnBytes.HonestTrace.U3 (covOf)
open P5J (AtMgA F0T)
open _root_.Desc.K14.Law (secondAt seatZ)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S ProofFile.Cl} {x : VerifiableInference.Desc.First.Look.Place}
  {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}

/-- Under the head and the opening the vocabulary is not empty. -/
theorem vocab_pos (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) : 0 < Zp.p.X.P.h.V := by
  have hp := O.public
  rw [O.W] at hp
  rw [VerifiableInference.Desc.Kinds.Head.Law.InScope.V_public hp,
    Meaning.HeadS.hS_in_scope h.scope h.reads hp]
  exact Nat.le_of_ble_eq_true rfl

/-- **Where the test on the instance says yes, the covered positions are there and fit.** -/
theorem covOf_sized_of_okStart (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (O : IM.Open OnBytes.secondHashFunction Z.pol Z.lay Z.KL (F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base cF
      (seatZ Zp Np) (secondAt Zp Np)) {ξ : ProofFile.Inst}
    (hx : (F0T OnBytes.secondHashFunction Zp Np cF).okStart ξ = true) :
    ((covOf Zp Bs.G₀ ξ).toOption.getD default).sized Bs.G₀.W.hS.T = true := by
  obtain ⟨cov, hc⟩ := coveredAt_of_reqOk (Johnson.AtFull.Shape.reqOk_of_okStart hx) (vocab_pos h O)
  have hs := coveredAt_sized hc
  obtain ⟨_, _, _, eT, _, _⟩ := Johnson.AtFull.Shape.nums_at h
  unfold covOf
  rw [O.W, hc]
  show cov.sized Zp.p.X.hS.T = true
  rw [eT]
  exact hs

end ProofFile.Honest.K2.Law

-- Each line below should name no more than propext, Classical.choice and Quot.sound.
#print axioms ProofFile.Honest.K2.Law.vocab_pos
#print axioms ProofFile.Honest.K2.Law.covOf_sized_of_okStart
