-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
-- Johnson/Desc/First/Att/Door/Law/DoorTie.lean: THE SHEET's FOUR SMALL Bools ARE THE LEMMAS' Bools, BY LEAN.
import Johnson.Desc.First.Att.Door.DoorBools
import Johnson.Desc.First.Att.K05BehindLay3

set_option autoImplicit false

namespace H2K5.Door
open VerifiableInference.Desc.First

theorem freeFromB_is (s : S) : freeFromB s = Att.P.freeFromB s := rfl
theorem freeAboveB_is (n : Nat) (s : S) : freeAboveB n s = Att.P.freeAboveB n s := rfl
theorem callerIn3B_is (first : Nat) (s : S) : callerIn3B first s = Att.P.k5CallerIn3 first s := rfl
theorem linkFreshB_is (arr : Array (Nat × String)) (s : S) : linkFreshB arr s = Att.P.linkFreshB arr s := rfl

#print axioms freeFromB_is
#print axioms freeAboveB_is
#print axioms callerIn3B_is
#print axioms linkFreshB_is

end H2K5.Door
