-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MoreAtEQ.lean (over TieTwo.lean): THE FIELD «more» OF Hands | HandsR AT E
:= EQ («in order» and the public items' test of the table of joints' promise, at the public part
z), SPLIT INTO WHAT RIDES AND WHAT IS MADE. A rule over letters, free of the kind. NO BLOCK
IMPORTS THIS FILE.
  more_of_pub   X k at E := EQ in front · «in order» rides · every public item that is asked
                behind AND was asked in front rides · every public item that is asked behind and
                was not asked in front holds behind ⟹ EQ Mg links ps z (k + 1) s' = true
«Asked at a border»: open there, or tied to an item that is open there (pubAt … ++ pubOfItems
(openAt …)). CALLED: pubHeld_of (Johnson/Desc/First/PromiseRides.lean).
LIMITS. A rule: which items these are at a switch, and that each rides or is made, is the work. No
soundness is claimed.
-/
import Johnson.P1K2R.TieTwo

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace P1K2
open VerifiableInference.Desc (Place)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub Meaning pubHeld pubOfItems pubHeld_of)
open IM (XK xk_parts openAt)

variable {P W : Type}

theorem more_of_pub {N : Numbers} {Mg : Meaning P W} {links : List ModelPart} {ps : List Place} {z : P}
    {k : Nat} {s s' : S} (hx : XK N links ps (EQ Mg links ps z) k s = true)
    (hIn : Mg.inOrder (z, s) = true → Mg.inOrder (z, s') = true)
    (hk : ∀ q ∈ pubAt Mg links ps (k + 1) ++ pubOfItems (openAt links ps (k + 1)),
      q ∈ pubAt Mg links ps k ++ pubOfItems (openAt links ps k) → Mg.pub q (z, s) = true →
      Mg.pub q (z, s') = true)
    (hm : ∀ q ∈ pubAt Mg links ps (k + 1) ++ pubOfItems (openAt links ps (k + 1)),
      ¬ q ∈ pubAt Mg links ps k ++ pubOfItems (openAt links ps k) → Mg.pub q (z, s') = true) :
    EQ Mg links ps z (k + 1) s' = true := by
  have c5 := (xk_parts hx).2.2.2.2
  unfold EQ at c5 ⊢
  rw [Bool.and_eq_true] at c5 ⊢
  exact ⟨hIn c5.1, pubHeld_of Mg _ _ _ _ (z, s) (z, s') c5.2 hk hm⟩

end P1K2

#print axioms P1K2.more_of_pub
