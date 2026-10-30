-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/LibTab.lean: THE PREMISE "OUR TABLE IS THE LIBRARY's EX ON 16 BITS" (Law/LibJoin.lean's join; Law/LibWhole.lean, LibParts.lean, LibLetters.lean, K06Means.lean carry it), PAID AT THE TABLE OF LEMMA 1 AS K6's FILES MAKE IT OFF THE ROWS OF CALL 3 (HeadTables.lean: tabOf row), WHERE THESE ROWS ARE THE VERIFIER's OWN TABLE OF EXPONENTIALS AT F = 24, sh = 8, sT = 4: STATED AND PROVED, over
Johnson/Road/HeadTabs.lean (rowFE: row u of that table as a number; tauFE_getD: the verifier's array holds it; rowFE_lt).
  tab_EX          row 3 u = Hd.rowFE u below 2^16 ⇒ (tabOf row u : Int) = Inst.Model.EX u below 2^16.
  tab_EX_of_tau   the same where row 3 u is the word number u of the verifier's array Model.Head.tauFEOf 24 8 4, as a number.
WHAT IT DOES NOT SAY. That the rows which the lookup's law speaks of at call 3 ARE that array's words (the call's record: isLut_of_layout | cl_of_layoutH say what a layout's records hold; the lookup's files' caller reads its own record): NOT TIED HERE. The three numbers 24, 8, 4 alone. No chance in it.

-/
import Mathlib
import Johnson.Road.HeadTabs
import Johnson.Desc.Kinds.HeadTables

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.Came

/-- **Our table off the verifier's rows is the library's EX.** -/
theorem tab_EX (row : Nat → Nat → Nat) (h3 : ∀ u, u < 2 ^ 16 → row 3 u = OnBytes.Road.Hd.rowFE u) :
    ∀ u, u < 2 ^ 16 → (tabOf row u : Int) = Inst.Model.EX u := by
  intro u hu
  unfold tabOf
  rw [if_pos hu, h3 u hu]
  unfold OnBytes.Road.Hd.rowFE Inst.Model.EX
  rw [Nat.shiftRight_eq_div_pow, Nat.shiftLeft_eq,
    Nat.add_mul_div_right _ _ (by norm_num : 0 < 2 ^ 16), Nat.div_eq_of_lt hu, Nat.zero_add]
  norm_num

/-- The same, off the verifier's own array. -/
theorem tab_EX_of_tau (row : Nat → Nat → Nat)
    (h3 : ∀ u, u < 2 ^ 16 → row 3 u = ((OnBytes.Model.Head.tauFEOf 24 8 4).getD u 0).toNat) :
    ∀ u, u < 2 ^ 16 → (tabOf row u : Int) = Inst.Model.EX u :=
  tab_EX row fun u hu => by
    have hu' : u < 65536 := hu
    have hb := OnBytes.Road.Hd.rowFE_lt hu'
    rw [h3 u hu, OnBytes.Road.Hd.tauFE_getD hu']
    exact UInt64.toNat_ofNat_of_lt' (lt_trans hb (by decide))

end VerifiableInference.Desc.Kinds.Head.Law.Came

#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tab_EX
#print axioms VerifiableInference.Desc.Kinds.Head.Law.Came.tab_EX_of_tau
