-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Close/Law/ViewAt.lean: WHAT THE VIEW OF A MEMBER OF A SHAPE OF THE PROGRAMS
(`membPort`, Johnson/Top/H/MemberOf.lean) MAKES OF A FORM, AT AN INDEX. Theorems.

Why. The tie of a member's sample row (Johnson/Desc/First/Close/Law/SampleTie.lean) comes down to
the member's view's form at (row, place). At the members that the programs have, the view moves
nothing: it is made of pieces that carry a form as it is, along an equation of codes.

What is said.
  `membPort_fm_main`, `membPort_fm_mask`: **the carried form at (row r, place x) is the form at the
    same row of the member's own table, at the place with the same number.** The two places have
    different types (the stage's code, the member's own code: equal where the table has a row): so
    the statement takes a place x' of the member's own code with x'.val = x.val.
  Beneath: `tabSame_fm`, `maskSame_fm`, `mainAt_fm`, `maskAt_fm`: the pieces. A table without a row
    has no index.

Limits. On forms alone: nothing on words, messages or the laws of a change of shape.

-/
import Johnson.Top.H.MemberOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Close
open OnBytes.Slice Cb Johnson.Pack Johnson.Top.H

section Tables
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (pos : Fin (2 ^ a) → Fin (2 ^ a'))

/-- A table of main rows under the stage's own code: the carried form at (row, place) is the form at
the same row and the place with the same number. -/
theorem tabSame_fm (e : C' = C) (v : Fin n × Fin C'.l → GE) (r : Fin n) (x : Fin C.l)
    (x' : Fin C'.l) (hx : x'.val = x.val) :
    (tabSame C C' a a' n pos e).fm v (r, x) = v (r, x') := by
  subst e
  obtain rfl : x' = x := Fin.ext hx
  rfl

/-- The like of a table of mask rows. -/
theorem maskSame_fm (e : C' = C) (v : Fin n × Fin C'.l → GE) (r : Fin n) (x : Fin C.l)
    (x' : Fin C'.l) (hx : x'.val = x.val) :
    (maskSame C C' a a' n e).fm v (r, x) = v (r, x') := by
  subst e
  obtain rfl : x' = x := Fin.ext hx
  rfl

end Tables

section Port
variable (cs : OnBytes.Codes) (sh : OnBytes.OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

theorem mainAt_fm (v : Fin sh.mainRows × Fin (cMain cs sh).l → GE) (r : Fin sh.mainRows)
    (x : Fin s.C.l) (x' : Fin (cMain cs sh).l) (hx : x'.val = x.val) :
    (mainAt cs sh s hM).fm v (r, x) = v (r, x') := by
  unfold mainAt
  split
  · next h0 => exact absurd r.isLt (by omega)
  · exact tabSame_fm _ _ _ _ _ _ _ v r x x' hx

theorem maskAt_fm (v : Fin sh.maskRows × Fin (cMask cs sh).l → GE) (r : Fin sh.maskRows)
    (x : Fin s.Z.l) (x' : Fin (cMask cs sh).l) (hx : x'.val = x.val) :
    (maskAt cs sh s hZ).fm v (r, x) = v (r, x') := by
  unfold maskAt
  split
  · next h0 => exact absurd r.isLt (by omega)
  · exact maskSame_fm _ _ _ _ _ _ v r x x' hx

/-- **THE VIEW OF A MEMBER OF A SHAPE OF THE PROGRAMS, AT A MAIN ROW**: the carried form at (row,
place) is the form at the same row of the member's own main table, at the place with the same
number. -/
theorem membPort_fm_main
    (v : (Fin sh.mainRows × Fin (cMain cs sh).l) ⊕ (Fin sh.maskRows × Fin (cMask cs sh).l) → GE)
    (r : Fin sh.mainRows) (x : Fin s.C.l) (x' : Fin (cMain cs sh).l) (hx : x'.val = x.val) :
    (membPort cs sh em s oM oZ hM hZ).view.fm v (.inl (r, x)) = v (.inl (r, x')) :=
  mainAt_fm cs sh s hM (fun j => v (.inl j)) r x x' hx

/-- **AT A MASK ROW**: the like. -/
theorem membPort_fm_mask
    (v : (Fin sh.mainRows × Fin (cMain cs sh).l) ⊕ (Fin sh.maskRows × Fin (cMask cs sh).l) → GE)
    (r : Fin sh.maskRows) (x : Fin s.Z.l) (x' : Fin (cMask cs sh).l) (hx : x'.val = x.val) :
    (membPort cs sh em s oM oZ hM hZ).view.fm v (.inr (r, x)) = v (.inr (r, x')) :=
  maskAt_fm cs sh s hZ (fun j => v (.inr j)) r x x' hx

end Port

end VerifiableInference.Desc.First.Close

#print axioms VerifiableInference.Desc.First.Close.tabSame_fm
#print axioms VerifiableInference.Desc.First.Close.maskSame_fm
#print axioms VerifiableInference.Desc.First.Close.mainAt_fm
#print axioms VerifiableInference.Desc.First.Close.maskAt_fm
#print axioms VerifiableInference.Desc.First.Close.membPort_fm_main
#print axioms VerifiableInference.Desc.First.Close.membPort_fm_mask
