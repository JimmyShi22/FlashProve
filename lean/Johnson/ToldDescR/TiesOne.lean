-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/ToldDescR/TiesOne.lean: no soundness is claimed.
The first tie at the law's own names. TiesAtSeat.lean says the first tie (takenOf_eq) at copies pairAt' | tkOf' of pairAt | tkOf (Johnson/Desc/K12/Coin/FirstOpensSets.lean). Here both files load in one module: Lean says that the copies are the originals, and the tie is said at the originals.
  pairAt'_eq | tkOf'_eq   the copies are the originals: rfl
  **takenOf_tkOf**        enterOwn s = .ok t → takenOf s = Coin.tkOf t s.loc.omega
Who reads each letter. s: the last chain's record; t: fixed by its equation.
Does not show. That a tree's number in the book is its place in its chain's order of sending. Nothing on soundness.
-/
import Johnson.ToldDescR.TiesAtSeat
import Johnson.Desc.K12.Coin.FirstOpensSets

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ToldDesc
open VerifiableInference.Desc.K12 (T12)
open VerifiableInference.Desc.K12.Seat (enterOwn)
open VerifiableInference.Desc.Third (S₃ takenOf)

theorem pairAt'_eq : pairAt' = VerifiableInference.Desc.K12.Coin.pairAt := rfl

theorem tkOf'_eq : tkOf' = VerifiableInference.Desc.K12.Coin.tkOf := rfl

/-- **The first tie, at the law's own list.** -/
theorem takenOf_tkOf (s : S₃) (t : T12) (h : enterOwn s = .ok t) :
    takenOf s = VerifiableInference.Desc.K12.Coin.tkOf t s.loc.omega :=
  (takenOf_eq s t h).trans (congrFun (congrFun tkOf'_eq t) s.loc.omega)

end ToldDesc

#print axioms ToldDesc.pairAt'_eq
#print axioms ToldDesc.tkOf'_eq
#print axioms ToldDesc.takenOf_tkOf
