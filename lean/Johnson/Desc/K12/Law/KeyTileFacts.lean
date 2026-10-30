-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.K12.Law.SitsKey
import Johnson.Desc.K12.Coin.Alike
/-
Johnson/Desc/K12/Law/KeyTileFacts.lean: THE PROXIMITY TEST's THREE LATER SEATS IN THE KEY FILE's
DESCRIPTION (Johnson/Desc/Key/Desc.lean: Key.descriptionFromSource X N P): WHAT THE GENERAL LEMMAS ON A DESCRIPTION's
OWN TILING ASK OF A SEAT, PAID FROM THE DESCRIPTION's TEXT: the flat lists' cuts at the description
itself · each entry is alike to the kind's block inside its two doors · it keeps the kind's «before»
· something stands behind the shared chain's first test. Over SitsKeyChains.lean's cuts. General in
X, N, P. BOOK-KEEPING. NO SOUNDNESS IS CLAIMED. NOTHING ON HIDING.
  key_shared_flat | key_shared_flat_omega | key_second_flat     the cuts, of (Key.descriptionFromSource X N P)'s own
      fields.
  keyGu_alike | keyOmega_alike     Coin.Alike (the kind's block inside the seat's two doors) (the
      entry). (The proof file's like, general in the claims' type, stands in a file over that
      file's whole cone: H2K12/TileAtGu.lean's guEntry_alike | omegaEntry_alike: one line each, as
      here. At the own test: H2K12/OwnEntryAlike.lean's ownEntry_alike_of, general in the claims'
      type and the block: called by whoever needs it.)
  keyGu_keeps          the entry keeps the kind's block's «before» and rounds (at Omega and at the
      own test: SitsChains.lean's omegaEntry_keeps | ownEntry_keeps, general in the claims' type).
  key_shared_behind    the list behind the test on G_u is not empty.
WHAT IT IS NOT: that the kind's own test on the plan holds at the places (H2K12/SitsRowKey.lean:
RowK12Key.plans) · nothing on the places' numbers (free · the first tree · the bounds) · nothing on
the first chain's test on the ranges · no run.

-/
set_option autoImplicit false
namespace H2K.JointK
open VerifiableInference.Desc VerifiableInference.Desc.K12
open VerifiableInference.Desc.K12.Seat (onGu onGomega enterOwn leaveOwn onOwn)

theorem key_shared_flat (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    (Key.descriptionFromSource X N P).shared.blocksInOrder =
      keySharedPre X.chains P ++ keyGu P ::
        ((P.O.toList.map keyOmega) ++ [keySharedEnd X.chains P]) :=
  keyShared_cut X.chains P

theorem key_shared_flat_omega (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)
    (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (Key.descriptionFromSource X N P).shared.blocksInOrder =
      (keySharedPre X.chains P ++ [keyGu P]) ++ keyOmega nO :: [keySharedEnd X.chains P] :=
  keyShared_cut_omega X.chains P nO hO

theorem key_second_flat (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces) :
    (Key.descriptionFromSource X N P).second.blocksInOrder =
      secondPre Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') ++
        ownEntry Key.Claim (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk') ::
          [secondEnd Key.Claim (Key.thirdPar X.chains) (proximityTestKind guardedProximityTestParts (pOwnK P) : Blk')] :=
  keySecond_cut X.chains P

theorem keyGu_alike (P : Key.LaterPlaces) :
    Coin.Alike
      ((proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk').inside (Seat.enter (·.gU)
                                                           (·.firstMask)) Seat.leave)
      (keyGu P) :=
  (Coin.alike_retype _).trans (Coin.alike_plan _ _)

theorem keyOmega_alike (nO : H2U.PlaceNums) :
    Coin.Alike
      ((proximityTestKind guardedProximityTestParts (pGomega nO) : Blk').inside (Seat.enter (·.gOmega) fun _ => none) Seat.leave)
      (keyOmega nO) :=
  (Coin.alike_retype _).trans (Coin.alike_plan _ _)

theorem keyGu_keeps (P : Key.LaterPlaces) :
    H2K.Made.Keeps (keyGu P) (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U) : Blk') := ⟨rfl, rfl⟩

theorem key_shared_behind (c : OnBytes.Model.Verify.Chains) (P : Key.LaterPlaces) :
    ∃ b' post', (P.O.toList.map keyOmega) ++ [keySharedEnd c P] = b' :: post' := by
  cases P.O with
  | none => exact ⟨_, _, rfl⟩
  | some nO => exact ⟨_, _, rfl⟩

end H2K.JointK

#print axioms H2K.JointK.key_shared_flat
#print axioms H2K.JointK.key_second_flat
#print axioms H2K.JointK.keyGu_alike
#print axioms H2K.JointK.keyOmega_alike
#print axioms H2K.JointK.keyGu_keeps
