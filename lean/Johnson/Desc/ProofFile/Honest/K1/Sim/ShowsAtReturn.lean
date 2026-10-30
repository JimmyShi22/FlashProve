-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/ProofFile/Honest/K1/Sim/ShowsAtReturn.lean: the shared "sending" (the kind K1): AT WHAT THE
MAKER onlineProverFromPublicFiles RETURNS, AT ANY FILLING, EVERY ONE OF THE 52 JOBS FITS ITS PLACE, AND SO ITS SENDER SHOWS
SOMETHING AT EVERY COIN: exact and fresh at these rows never read "none = none". Two theorems; no
definition.

  fits_at_return        where the gate accepts: sendFits J.P J.ride = true at each of the 52 jobs
  shows_some_at_return  at each job's side: its one member is the sender beside its simulator; at
                        every state m, every list of challenges that the side's own rounds can draw,
                        all positions and EVERY coin, what the sender shows is some (shownR …), and
                        what the simulator tells is some (shownR … at no data)

By what. fits_at_lots_plan (Johnson/SendSim/Seat/RideFitsW.lean), plan_of_live
(Johnson/SendSim/Seat/ReadsAtLive.lean), showsAt, tellsAt (Johnson/SendSim/At/Shows.lean),
members_seated (Johnson/SendSim/At/Member.lean), seatedAt_job (Johnson/SendSim/Seat/AtDescStands.lean).

Limits. No premise on the state: On is True. All limits of AtFill.lean. No distribution is named here.
No property of the protocol is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K1.Sim.AtFill
import Johnson.SendSim.Seat.RideFitsW
import Johnson.SendSim.At.Shows

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K1.Sim
open VerifiableInference.Desc
open OnBytes.SendSim.At OnBytes.SendSim.Seat

variable {W₀ W₀' Rc' : Type}

/-- **EVERY ONE OF THE 52 JOBS FITS ITS PLACE.** -/
theorem fits_at_return {Z : VerifierAndGoals.PublicFiles} (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true)
    (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments) {P : OnlineProverParts W₀' Rc' Cells Unit Unit}
    {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G, sendFits J.P J.ride = true := by
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  rw [← hG]
  intro J hJ
  obtain ⟨D, hD⟩ := job_mem hJ
  exact fits_at_lots_plan Op (plan_of_live hL Op).1 _ D hD

/-- **AT EVERY COIN THE SENDER SHOWS SOMETHING, AND ITS SIMULATOR TELLS SOMETHING.** -/
theorem shows_some_at_return {Z : VerifierAndGoals.PublicFiles}
    (hL : FlashProve.protocolDataWellFormed (VerifierAndGoals.asDescriptionFiles Z) = true) (I : WiderIn W₀) (g : W₀' → W₀)
    (rd : Rc' → IndexCommitterCoins) (S : OnBytes.HonestTrace.Sz) (O : OnlineProverArguments)
    {P : OnlineProverParts W₀' Rc' Cells Unit Unit} {A : OnlineProverWithDescription W₀' Rc' Cells Unit Unit}
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A)
    (φ : Face (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Inst)
    (fs : List (Fall A.F.S₁)) :
    ∀ J ∈ k1Jobs OnBytes.secondHashFunction S O A.Z A.G,
      ∀ σ : Side A.F.S₁ A.F.Cl (Local W₀' Rc' Inst Cells) (Local W₀' Rc' Inst Cells) Unit Inst,
      Side.seated A.F.first.blocksInOrder (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                   (witAt I g rd A.Z) J).place (jobRow (V := Local W₀' Rc' Inst Cells) (Pb := Inst)
                   (witAt I g rd A.Z) J).row fs = some σ →
      σ.members = [memberAt σ (jobOver J (witAt I g rd A.Z))] ∧
      ∀ (m : Mid (Local W₀' Rc' Inst Cells) Unit) (front : Before) (ds : List Fmt.Drawn)
        (asks : List (List (List Nat))) (c : Cs (dueR J.P J.ride)),
        drawsFit σ.block.rounds ds = true →
        σ.shows φ (memberAt σ (jobOver J (witAt I g rd A.Z))) (c, (), ()) m ds asks =
            some (shownR J.P J.first J.ride
              ((jobOver J (witAt I g rd A.Z)).data m.st.input (frontOf m)) ds asks c) ∧
          (memberAt σ (jobOver J (witAt I g rd A.Z))).tells φ c m.st.input front ds asks =
            some (shownR J.P J.first J.ride (fun _ _ _ => none) ds asks c) := by
  intro J hJ σ hσ
  have hf : sendFits (jobOver J (witAt I g rd A.Z)).P (jobOver J (witAt I g rd A.Z)).ride = true :=
    fits_at_return hL S O hA J hJ
  obtain ⟨Bs, base, c, S₂, S₃, Op, hG⟩ := open_at hA
  rw [← hG] at hJ
  obtain ⟨D, hD⟩ := job_mem hJ
  have hSe : Seated σ (jobOver J (witAt I g rd A.Z)) :=
    seatedAt_job Op (witAt I g rd A.Z) (lotNo OnBytes.secondHashFunction A.Z) D hD hσ
  refine ⟨members_seated hSe, fun m front ds asks c hd => ⟨?_, ?_⟩⟩
  · have h := showsAt _ _ _ _ _ _ φ σ (jobOver J (witAt I g rd A.Z)) hSe m ds asks c hd
    rw [if_pos hf] at h
    exact h
  · have h := tellsAt _ _ _ _ _ _ φ σ (jobOver J (witAt I g rd A.Z)) hSe m.st.input front ds asks c
      hd
    rw [if_pos hf] at h
    exact h

end ProofFile.Honest.K1.Sim

#print axioms ProofFile.Honest.K1.Sim.fits_at_return
#print axioms ProofFile.Honest.K1.Sim.shows_some_at_return
