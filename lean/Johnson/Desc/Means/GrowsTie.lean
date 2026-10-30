-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Means/GrowsTie.lean: a statement that has grown out of another is a later statement in
the sense of the laws on what a row means.

Grows (Johnson/Desc/Grows.lean) says of two statements that no group and no oracle message was
dropped or turned. Extends (Johnson/Desc/Means/Keeps.lean) asks less: the same codes, and every
oracle message there with its shape. So what is shown under Extends holds under Grows: a row that
has passed the tests says in the grown statement what it said, and passes the tests at the grown
group.

Main theorems: extends_of_grows, says_grows, rowIn_grows.

What is not claimed. Grows says nothing on rows: that the grown statement still has the rows of the
earlier one is not shown here.

-/
import Johnson.Desc.Grows
import Johnson.Desc.Means.Keeps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Means

open Model (Reading)
open VerifiableInference.Desc (Grows)

variable {S S' : Statement} {G G' : Group} {row : Row}

/-- A statement that has grown out of another is a later statement. -/
theorem extends_of_grows (h : Grows S S') : Extends S S' :=
  ⟨h.1, fun o x hx => by
    obtain ⟨x', hx', g⟩ := h.2.2 o x hx
    exact ⟨x', hx', g.1⟩⟩

/-- A row that has passed the tests says in the grown statement what it said. -/
theorem says_grows {K : Type} [CommRing K] (ρ : Reading K) (h : Grows S S')
    (hr : RowIn S G row) (m : Words K) : Says ρ S' row m ↔ Says ρ S row m :=
  says_extends ρ (extends_of_grows h) hr m

/-- A row that has passed the tests at a group passes them at the group that has grown out of
it. -/
theorem rowIn_grows (h : Grows S S') {g : Nat} (hG : S.groups[g]? = some G)
    (hr : RowIn S G row) : ∃ G', S'.groups[g]? = some G' ∧ RowIn S' G' row := by
  obtain ⟨G', hG', gg⟩ := h.2.1 g G hG
  refine ⟨G', hG', RowIn.extends (G := G) (extends_of_grows h) (fun o ho => ?_) hr⟩
  exact Array.mem_toList_iff.2 (gg.2.2.2 o (Array.mem_toList_iff.1 ho))

end OnBytes.Means
