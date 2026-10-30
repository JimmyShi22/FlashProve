-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsKeyChains
import Johnson.Desc.Key.Desc
/-
Johnson/Desc/K12/Law/SitsKey.lean: THE PROXIMITY TEST SITS IN THE KEY FILE's DESCRIPTION
(Johnson/Desc/Key/Desc.lean: descriptionFromSource X N P · descriptionFromPlan m) AT ITS FOUR PLACES, and what that
description's yes gives there. All beneath lies in the library's tree. Over
Johnson/Desc/K12/Law/SitsKeyChains.lean. NO SOUNDNESS IS
CLAIMED. NOTHING ON HIDING. NO NEW MATHEMATICS.
  (That descriptionFromPlan m = .ok F gives F = descriptionFromSource X N P at sourceOf m · rangesNumbers m · laterPlaces m is
      Key.descOfMade_is: Johnson/Desc/Key/SlotIs.lean: not typed again here.)
  key_atR | atU | atO | atW     (descriptionFromSource X N P).runEnd's yes ⇒ AtCut at the written cut: NO OTHER
      PREMISE.
LIMITS. That no other entry bears the kind K12 is not typed. NO RUN; no closed member. All limits of
Sits.lean: A YES, NOT A PRICE.
-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)
open H2K.Pub (Letters)

/-! ### the instance -/

/-- AT THE RANGES' TEST. -/
theorem key_atR (L : Letters) (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (x : Key.Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂ × (Key.descriptionFromSource X N P).S₃)
    (h : (Key.descriptionFromSource X N P).runEnd x v₁ v₂ v₃ = .ok e) :
    AtCut L (Key.rangesParams N) 0 (keyFirstPre X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N)
      (rngEntry X.Y.k.oneTime N) (keyFirstPost X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N)
      (Key.enterAndAsk (Key.enterRanges X.Y.k.oneTime) (Key.rangesParams N)) Key.leaveRanges
      ((Key.descriptionFromSource X N P).start₁ ((Key.descriptionFromSource X N P).pub x)) e.1 (withEmptySealRound v₁) :=
  run_atCut1 L (Key.rangesParams N) (Key.descriptionFromSource X N P) x v₁ v₂ v₃ e h _ _ _ _ _
    (keyFirst_cut X.Y.k.oneTime X.Y.D.1 X.Y.told.1 X.set N) (rngEntry_sits X.Y.k.oneTime N)

/-- AT THE SHARED CHAIN's TEST ON G_u. -/
theorem key_atU (L : Letters) (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (x : Key.Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂ × (Key.descriptionFromSource X N P).S₃)
    (h : (Key.descriptionFromSource X N P).runEnd x v₁ v₂ v₃ = .ok e) :
    AtCut L (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) 0 (keySharedPre X.chains P) (keyGu P)
      ((P.O.toList.map keyOmega) ++ [keySharedEnd X.chains P])
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave
      ((Key.descriptionFromSource X N P).start₂ ((Key.descriptionFromSource X N P).pub x)) e.2.1 v₂ :=
  run_atCut2 L _ (Key.descriptionFromSource X N P) x v₁ v₂ v₃ e h _ _ _ _ _ (keyShared_cut X.chains P)
    (keyGu_sits P)

/-- AT THE SHARED CHAIN's TEST ON G_omega, where the plan has one. -/
theorem key_atO (L : Letters) (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (nO : H2U.PlaceNums) (hO : P.O = some nO) (x : Key.Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂ × (Key.descriptionFromSource X N P).S₃)
    (h : (Key.descriptionFromSource X N P).runEnd x v₁ v₂ v₃ = .ok e) :
    AtCut L (pGomega nO) 0 (keySharedPre X.chains P ++ [keyGu P]) (keyOmega nO)
      [keySharedEnd X.chains P] (Seat.enter (·.gOmega) fun _ => none) Seat.leave
      ((Key.descriptionFromSource X N P).start₂ ((Key.descriptionFromSource X N P).pub x)) e.2.1 v₂ :=
  run_atCut2 L _ (Key.descriptionFromSource X N P) x v₁ v₂ v₃ e h _ _ _ _ _ (keyShared_cut_omega X.chains P nO hO)
    (omegaEntry_sits Key.Claim nO)

/-- AT THE LAST CHAIN's OWN TEST. -/
theorem key_atW (L : Letters) (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (x : Key.Xi) (v₁ v₂ v₃ : Fmt.View)
    (e : (Key.descriptionFromSource X N P).S₁ × (Key.descriptionFromSource X N P).S₂ × (Key.descriptionFromSource X N P).S₃)
    (h : (Key.descriptionFromSource X N P).runEnd x v₁ v₂ v₃ = .ok e) :
    ∃ s₃, (Key.descriptionFromSource X N P).start₃ ((Key.descriptionFromSource X N P).pub x) e.1 e.2.1 = .ok s₃ ∧
      AtCut L (pOwnK P) (Key.descriptionFromSource X N P).lastChainFirstTreeNumber
        (secondPre Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'))
        (ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk'))
        [secondEnd Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')] enterOwn
        leaveOwn
        s₃ e.2.2 v₃ :=
  run_atCut3 L _ (Key.descriptionFromSource X N P) x v₁ v₂ v₃ e h _ _ _ _ _ (keySecond_cut X.chains P)
    (ownEntry_sits Key.Claim _)

end H2K.JointK

#print axioms H2K.JointK.key_atR
#print axioms H2K.JointK.key_atU
#print axioms H2K.JointK.key_atO
#print axioms H2K.JointK.key_atW
