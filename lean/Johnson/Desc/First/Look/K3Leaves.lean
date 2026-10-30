-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Look/K3Leaves.lean: the kind "lookup" (K3): WHICH READERS OF THE VERIFIER's STATE
AN ACCEPT OF EITHER LOOKUP LEAVES, in the sense of Johnson/Desc/First/PubFoot.lean (a footprint an
item, a footprint a kind; «the item stays» is then a test on two lists). One list,
two theorems, one evaluation. NO SOUNDNESS IS CLAIMED.

Main names.
  k3Keeps := [st, out, frame, link]: four of the seven readers.
  sameBut_leaves: SameBut s s' (K3CallsTurns.lean: what both lookups' accepts are shown to give) →
    SameOn D k3Keeps s s', at every D.
  sameBut_rides: so every public item of a list Q with ridesB D.runs k3Keeps Q = true that passed
    the composed test at s passes it at s', where base says the same of Q's items at both: one call
    of rides_of_B.
  k3_three_ride: ridesB runs k3Keeps [unheard, indexIs, indexThere] = true, at every map of names.
NOT LEFT, AT THE DIGITS: fork (the accept lays the ledger anew) · tl (what the lookup's verifier has
heard is laid there). NOT LOOKED AT: row.
OBJECT. No sub-protocol's text: SameBut, and the readers of PubFoot.lean.
USER. Johnson/Desc/Sound/MgAt/K3DigitsOthers.lean and K3HeadBehindAt.lean call sameBut_rides at
k3_three_ride.
LETTERS. s, s'; D, base, z, Q, q.
IS IT EMPTY? SameBut is had at both lookups' seated accepts (k3_digits_seated_turns and its like at
the calls).
Compiled with the whole library.
(Where this and lean/THEOREM.md differ, the page holds.)
Limits. Of the eleven or twelve public items of other kinds that a working list (not named here)
gives behind the digits' sub-protocol the rule takes three. ledger and freeAbove read the ledger,
which is not left: K3KeeperRides.lean keeps them by hand. formsIn is not booked in footOf.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.PubFoot
import Johnson.Desc.First.Look.K3CallsTurns

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.OnPublicFiles
open VerifiableInference.Desc.First (Rdr SameOn Pub PubData pubAll ridesB rides_of_B)

/-- The readers that an accept of either lookup leaves. -/
def k3Keeps : List Rdr := [.st, .out, .frame, .link]

/-- **What leaves all that SameBut names leaves these four readers.** -/
theorem sameBut_leaves (D : PubData) {s s' : Desc.First.S} (T : SameBut s s') :
    SameOn D k3Keeps s s' := by
  intro r hr
  simp only [k3Keeps, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact T.st
  · exact T.out
  · exact congrArg (·.frame) T.check
  · exact T.link

/-- **So every booked item that reads these alone stays.** -/
theorem sameBut_rides {P : Type} (D : PubData) (base : Pub → P × Desc.First.S → Bool)
    (Q : List Pub) (hQ : ridesB D.runs k3Keeps Q = true) (z : P) {s s' : Desc.First.S}
    (T : SameBut s s') (hb : ∀ q ∈ Q, base q (z, s') = base q (z, s)) (q : Pub) (hq : q ∈ Q)
    (ht : pubAll D base q (z, s) = true) : pubAll D base q (z, s') = true :=
  rides_of_B D base k3Keeps Q hQ z s s' (sameBut_leaves D T) hb q hq ht

theorem k3_three_ride (runs : Nat → Nat → String → List (Nat × String)) :
    ridesB runs k3Keeps [.unheard, .indexIs, .indexThere] = true := rfl

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.sameBut_leaves
#print axioms VerifiableInference.OnPublicFiles.sameBut_rides
#print axioms VerifiableInference.OnPublicFiles.k3_three_ride
