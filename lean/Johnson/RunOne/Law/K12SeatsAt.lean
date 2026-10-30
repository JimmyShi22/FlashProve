-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12SeatsAt.lean: THE THREE LATER PROXIMITY TESTS OF A KEY FILE ARE BLOCKS OF ITS DESCRIPTION's FLAT LISTS, EACH AT A NAMED SEAT. Statements with proofs.

OBJECT. `(FK X N P).shared.blocksInOrder` and `(FK X N P).second.blocksInOrder` (Johnson/RunOne/Sound/KeyAtFK.lean: the key file's description, Johnson/Desc/Key/Desc.lean, at the records): the lists of blocks that the verifier's fold runs over.
USER. The premise "the chain's flat list holds the term at seat i" of the laws at the three later seats (Johnson/RunOne/Law/K12SeatGood.lean: seat_shared, seat_own).
LETTERS. X, N, P are free; at Omega's test nO with P.O = some nO.

  fk_U_at: behind the shared chain's first block and its blocks of the test on the table stands the test on the folded row's group, in the flat list's dress.
  fk_O_at: behind it Omega's test, where the places name one.
  fk_own_at: seat 2 of the last chain holds the test on the own group, with the stamp of its place in that chain (`Third.ownAt`: the place alone turns).
  hb_U, hb_O, hb_own: the same three, written in the very form of the premise `hb` of `seat_shared` and `seat_own`: so that premise can be met, at these seats and these places' numbers.
The ranges' test's seat is `fk_rng_at` (Johnson/RunOne/Sound/KeyMapAtFK.lean).
Limits. Nothing on what these blocks decide. Where the places name no test for Omega (P.O = none) the description has none; that P.O is some nO at a real plan is shown nowhere: hO has no payer. The seats' numbers are terms (1 + the number of the table's blocks + j): that they are 9 and 10 at a real plan is not shown. hb_U, hb_O, hb_own are typed here by hand in the laws' form; that the laws take them: Johnson/RunOne/Law/K12SeatsBound.lean [not in this library]. Nothing on soundness, nothing on hiding.

-/
import Johnson.RunOne.Sound.KeyLaterAtFK

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.Law.K12SeatsAt
open VerifiableInference.Desc VerifiableInference.Desc.K12
open Johnson.RunOne.Sound

variable (X : Key.Source) (N : H2U.PlaceNums) (P : Key.LaterPlaces)

/-- The shared chain's blocks of the test on the table. -/
abbrev tableBlocks : List (Block _root_.Desc.K14.St Unit) :=
  _root_.Desc.K14.blocksOr (Key.sharedPar X.chains (Key.beforeSharedPoint P))

theorem shared_tail (j : ℕ) :
    (FK X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + j)]? =
      ((Key.sharedTests P).map atClaim ++ [atClaim (Key.sharedChain X.chains P).last])[j]? := by
  rw [fk_shared_at X N P]
  show (((tableBlocks X P) ++ Key.sharedTests P).map atClaim ++ [_])[_]? = _
  rw [List.map_append, List.append_assoc]
  exact getElem?_append_at _ _ _ j (List.length_map _)

/-- **The test on the folded row's group.** -/
theorem fk_U_at :
    (FK X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 0)]? =
      some (atClaim (Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U)))) :=
  (shared_tail X N P 0).trans rfl

/-- **Omega's test.** -/
theorem fk_O_at (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (FK X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 1)]? =
      some (atClaim (Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO)))) := by
  rw [shared_tail X N P 1]
  unfold Key.sharedTests
  rw [hO]
  rfl

/-- **The test on the own group.** -/
theorem fk_own_at : (FK X N P).second.blocksInOrder[2]? = some (atClaim (Third.ownAt (Key.ownTest P))) :=
  (congrArg (fun c : Chain _ Key.Claim => c.blocksInOrder[2]?) (fk_second_is X N P)).trans rfl

/-! ## The three statements in the very form in which the laws at these seats ask them -/

/-- The premise `hb` of `seat_shared` (Johnson/RunOne/Law/K12SeatGood.lean
[not in this library]) at own := false. -/
theorem hb_U :
    (FK X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 0)]? =
      some (bareB (Block.retype (Cl := Unit) (Cl' := Key.Claim)
        (if false then Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U))
          else Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 9, .K12⟩ P.U))))) :=
  fk_U_at X N P

/-- The same at own := true. -/
theorem hb_O (nO : H2U.PlaceNums) (hO : P.O = some nO) :
    (FK X N P).shared.blocksInOrder[1 + ((tableBlocks X P).length + 1)]? =
      some (bareB (Block.retype (Cl := Unit) (Cl' := Key.Claim)
        (if true then Seat.onGomega (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))
          else Seat.onGu (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨2, none, 10, .K12⟩ nO))))) :=
  fk_O_at X N P nO hO

/-- The premise `hb` of `seat_own`. -/
theorem hb_own :
    (FK X N P).second.blocksInOrder[2]? = some (bareB (Block.retype (Cl := Unit) (Cl' := Key.Claim)
               (Third.ownAt (Seat.onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ P.W) : Block T12 Unit))))) :=
  fk_own_at X N P

end Johnson.RunOne.Law.K12SeatsAt

#print axioms Johnson.RunOne.Law.K12SeatsAt.shared_tail
#print axioms Johnson.RunOne.Law.K12SeatsAt.fk_U_at
#print axioms Johnson.RunOne.Law.K12SeatsAt.fk_O_at
#print axioms Johnson.RunOne.Law.K12SeatsAt.fk_own_at
#print axioms Johnson.RunOne.Law.K12SeatsAt.hb_U
#print axioms Johnson.RunOne.Law.K12SeatsAt.hb_O
#print axioms Johnson.RunOne.Law.K12SeatsAt.hb_own
