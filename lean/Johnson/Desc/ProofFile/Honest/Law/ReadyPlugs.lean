-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/Law/ReadyPlugs.lean: the sixteen payments of `OnlinePayments`
(Honest/Law/ReadyAtOnline.lean), each laid in from its kind's own theorem. No definition; two
theorems.

  `onlinePayments_at_return`  under the head, at a return of the maker, all sixteen stand
  `ready_online_at_return`    so `ready` returns at every index in range and request with a trace

«The head» is `P5J.AtMgA`, the structure that says what the public files make.

Limits.
  * What is paid is that `chainSteps` returns at the members. Nothing here says that a part plays, or
    that a verifier accepts, or that no side lacks: a kind with no side pays for nothing.
  * That the maker returns is a premise (hA).
  * This file proves nothing about soundness, completeness, hiding or any other property of the
    protocol.
-/
import Johnson.Desc.ProofFile.Honest.Law.ReadyAtOnlineHolder
import Johnson.Desc.ProofFile.Honest.K5.Law.KindPaysAtTerm
import Johnson.Desc.ProofFile.Honest.K13.Law.KindPaysAtTerm
import Johnson.Desc.ProofFile.Honest.K1.Pay.Pays
import AtFullSide.Honest.K3.Term.LookupKindPaysAtTheTerm
import AtFullSide.K2.LendsAtTheTerm
import AtFullSide.K4.KindPaysAtTerm
import Johnson.Desc.ProofFile.Honest.K7.Law.KindPaysAtTerm
import AtFullSide.K8.KindPaysAtFill
import AtFullSide.K10.PaysOnline
import AtFullSide.K11.OwedAtTheOnline
import AtFullSide.K12.PaysFirst
import AtFullSide.K12.PaysShared
import AtFullSide.K12.PaysLast
import Johnson.Desc.ProofFile.Honest.K6.Term.KindPaysAtTerm
import AtFullSide.K14.SixPayAtBase

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace ProofFile.Honest.Term
open AtPublicFiles.AtFiles AtPublicFiles.Cut AtPublicFiles.Bridge
open VerifiableInference.Desc (KindName Chain)

variable {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain P5J.TS ProofFile.Cl} {x₀ : VerifiableInference.Desc.First.Look.Place}
  {returned : OnlineReturn Z}

/-- **Under the head, at a return, all sixteen payments stand.** -/
theorem onlinePayments_at_return (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) : OnlinePayments returned := by
  have eF := (atPure_at_laid h.laid hA).2
  have shared : ∀ κ : KindName, κ ≠ .K12 →
      KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared κ := by
    intro κ hκ
    rw [eF]
    exact AtFullSide.K14.kindPays_through h matrixInput id (tableCoins Z) matrixInput.dummy
      OnBytes.secondHashFunction OnBytes.HonestTrace.Sz.ref openHonest hA κ hκ
  have k1 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K1 :=
    kindPays_first_at_own_description hA fun A₀ h₀ =>
      (K1.Pay.k1_pays matrixInput OnBytes.HonestTrace.Sz.ref openHonest h h₀).1
  have k2 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K2 := by
    rw [eF]
    exact kindPays_first_of_base_return hA fun A₀ h₀ =>
      AtFullSide.K2.Term.k2Lends matrixInput OnBytes.HonestTrace.Sz.ref openHonest h h₀
  have k8 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K8 := by
    rw [eF]
    refine kindPays_first_of_base_return hA fun A₀ h₀ => ?_
    have h' : P5J.AtMgA OnBytes.secondHashFunction Z D r A₀.Z Np cF x₀ := by
      rw [(atPure_at_laid h.laid h₀).1]
      exact h
    exact AtFullSide.K8.k8_kindPays h₀ h' fun M hM =>
      ((lot_alone _ _ _ _ (onlyK8 _ _ _ _) _ _) M hM).symm.imp id fun e => by
        subst e
        rfl
  have k12 : KindPays returned.B 0 returned.F.first.blocksInOrder returned.H.first .K12 :=
    kindPays_first_at_own_description hA fun A₀ h₀ =>
      AtFullSide.K12.firstTest_pays h matrixInput OnBytes.HonestTrace.Sz.ref openHonest h₀
  have k12Shared : KindPays returned.B 1 returned.F.shared.blocksInOrder returned.H.shared .K12 :=
    kindPays_shared_at_own_description hA fun A₀ h₀ =>
      AtFullSide.K12.sharedTests_pay h matrixInput OnBytes.HonestTrace.Sz.ref openHonest h₀
  have k12Second : KindPays returned.B 2 returned.F.second.blocksInOrder returned.H.second .K12 :=
    kindPays_second_at_own_description hA fun A₀ h₀ =>
      AtFullSide.K12.lastChain_pays h matrixInput OnBytes.HonestTrace.Sz.ref openHonest h₀ _
  exact ⟨k1, k2, AtFullSide.Honest.K3.Term.lookupKindPaysAtTheTerm h hA,
    AtFullSide.K4.kindPays_k4_at_return h hA, K5.kindPays_k5_at_return h hA,
    K6.Term.kindPaysAtTheReturn h hA, K7.kindPays_k7_at_return h hA, k8, AtFullSide.K10.kindPays_k10_at_return h hA,
    AtFullSide.K11.kindPays_k11_at_return h hA, k12,
    K13.kindPays_k13_at_return h hA, shared _ (by decide), shared _ (by decide), k12Shared,
    k12Second⟩

/-- **`ready` returns at the return, at every index in range and every request with a trace.**
Conditional on the head and on the return. -/
theorem ready_online_at_return (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (hA : onlineMaker Z = .ok returned) {w₀ : FullSizeMatrix} {x : ProofFile.Inst}
    (hi : returned.H.inRange w₀ = true) (ht : (returned.H.trace w₀ x).isSome = true)
    (rc : (protocolAtFiles Z).EncodingRandomness) (k : Coins returned.B) :
    ∃ R, ready returned.F returned.B returned.H w₀ rc x k = .ok R :=
  ready_online h hA (onlinePayments_at_return h hA) hi ht rc k

end ProofFile.Honest.Term

#print axioms ProofFile.Honest.Term.onlinePayments_at_return
#print axioms ProofFile.Honest.Term.ready_online_at_return
