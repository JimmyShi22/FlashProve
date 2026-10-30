-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Tw/K2C/PubRides.lean: code switching (the kind K2): THE THREE PUBLIC ITEMS THAT ARE
ASKED ON BOTH SIDES OF A SWITCH («unheard» · «indexIs» · «indexThere») STAY TRUE ACROSS A STEP
THAT LEAVES WHAT GOES ON TO THE LATER CHAINS (s.out) AND TAKES NO ORACLE MESSAGE AWAY, at the
composed public tests (pubAll, Johnson/Desc/First/PubAll.lean). NO BLOCK IMPORTS THIS
FILE.
  pub_rides3   s'.out = s.out · every oracle message's number that is there in front is there
               behind ⟹ each of the three tests, true at (z, s), is true at (z, s')
WHY NOT rides_of_B (Johnson/Desc/First/PubFoot.lean): «indexThere» is booked there as reading the
WHOLE statement, which a switch turns; its test reads only whether one number is there. Which items
are asked around a switch: by Lean's kernel at the written list (Johnson/P1K2R/MoreAtSwitch.lean).
No soundness is claimed.
-/
import Johnson.Desc.First.PubAllAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open VerifiableInference.Desc.K13 (indexIsC indexThereC)

theorem pub_rides3 {P : Type} (D : PubData) (base : Pub → P × S → Bool) (z : P) {s s' : S}
    (ho : s'.out = s.out)
    (ht : ∀ j : Nat, (s.st.oracles[j]?).isSome = true → (s'.st.oracles[j]?).isSome = true)
    (q : Pub) (hq : q ∈ [Pub.unheard, Pub.indexIs, Pub.indexThere])
    (h : pubAll D base q (z, s) = true) : pubAll D base q (z, s') = true := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl
  · rw [pubAll_unheard] at h ⊢
    show unheardB s' = true
    have h' : unheardB s = true := h
    unfold unheardB at h' ⊢
    rw [ho]
    exact h'
  · rw [pubAll_indexIs] at h ⊢
    show indexIsC D.N.indexNo s' = true
    have h' : indexIsC D.N.indexNo s = true := h
    unfold indexIsC at h' ⊢
    rw [ho]
    exact h'
  · rw [pubAll_indexThere] at h ⊢
    show indexThereC s' = true
    have h' : indexThereC s = true := h
    unfold indexThereC at h' ⊢
    rw [ho]
    exact ht _ h'

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.pub_rides3
