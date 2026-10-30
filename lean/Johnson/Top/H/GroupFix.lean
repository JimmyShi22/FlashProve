-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Top/H/GroupFix.lean: a code word close to an arranged word of a group of sent messages is
arranged: the condition `Reshape.Fix` at the changes of shape of Johnson/Top/H/MemberOf.lean, at a
family, and at the whole arrangement.

`Reshape.Fix ρ e` (Cb/Ld/LdBatShape.lean) says: a pair of message and tail whose encoding is
within e of a new word is of the new shape: going back and forth gives it again. The library shows
it of the arrangement of a group below the distances of the two codes, if it holds of the members'
changes of shape (`ldGroup_shape_laws`, Cb/Ld/LdGroupFold.lean). At the members of the programs
nothing moves in messages and tails, so it holds at every radius. Statements and proofs.
Main names:
  `tabSame_fix`, `tabNone_fix`, `maskSame_fix`, `tabVoid_fix`, `pairAt_fix`: the five changes of
    shape, at every radius.
  `mainAt_fix`, `maskAt_fix`, `membPort_fix`: the two tables and the member of a shape of the
    programs.
  `Rows.rho_fix`: under `Rows.Good`, a radius below the stage's distance and `Fix` of every
    member's change of shape: `Fix` of the arrangement `R.Sh.rho` at that radius.
  `Fam.FixAt`, `Fam.FixAt.sub`, `Fam.rho_fix`: the same for a family
    (Johnson/Top/H/Families.lean).
Limits: no family of a file is treated here. Nothing on a form or on weights at corners that hold
no row.

-/
import Johnson.Top.H.Families

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Top.H
open OnBytes OnBytes.Slice Cb Johnson.Pack

section Tables
variable (C C' : Fmt.M1.Code) (a a' n : ℕ) (pos : Fin (2 ^ a) → Fin (2 ^ a'))

theorem tabSame_fix (e : C' = C) (r : ℕ) : (tabSame C C' a a' n pos e).Fix r := by
  subst e
  exact fun _ _ _ => rfl

theorem tabNone_fix (h0 : n = 0) (r : ℕ) : (tabNone C C' a a' n pos h0).Fix r :=
  fun _ _ _ => Prod.ext (funext fun j => absurd j.1.isLt (by omega))
    (funext fun q => absurd q.1.isLt (by omega))

theorem maskSame_fix (e : C' = C) (r : ℕ) : (maskSame C C' a a' n e).Fix r := by
  subst e
  exact fun _ _ _ => rfl

end Tables

theorem tabVoid_fix {P P' : Type} [Finite P] (A : LdCode GE P') (D : LdCode GE P) (pos : P → P')
    (n : ℕ) (h0 : n = 0) (r : ℕ) : (tabVoid A D pos n h0).Fix r :=
  fun _ _ _ => Prod.ext (funext fun j => absurd j.1.isLt (by omega))
    (funext fun q => absurd q.1.isLt (by omega))

theorem pairAt_fix {P P' : Type} [Finite P] (A B : LdCode GE P') (pos : P → P') (r : ℕ) :
    (pairAt A B pos).Fix r := fun _ _ _ => rfl

section Port
variable (cs : Codes) (sh : OracleShape) (em : ℕ) (s : Sg) (oM oZ : ℕ)
  (hM : sh.mainRows ≠ 0 → cMain cs sh = s.C) (hZ : sh.maskRows ≠ 0 → cMask cs sh = s.Z)

theorem mainAt_fix (r : ℕ) : (mainAt cs sh s hM).Fix r := by
  unfold mainAt
  split
  · exact tabNone_fix _ _ _ _ _ _ _ r
  · exact tabSame_fix _ _ _ _ _ _ _ r

theorem maskAt_fix (r : ℕ) : (maskAt cs sh s hZ).Fix r := by
  unfold maskAt
  split
  · exact tabVoid_fix _ _ _ _ _ r
  · exact maskSame_fix _ _ _ _ _ _ r

/-- The member of a shape of the programs, at every radius. -/
theorem membPort_fix (hA : aOf cs sh ≤ s.C.a) (r : ℕ) :
    (membPort cs sh em s oM oZ hM hZ).view.Fix r :=
  (ldShape_comp GE s.Ps _ _ _ _ _ (pairAt_laws _ _ _)
    (ldShape_comp GE s.Ps _ _ _ _ _
      (ldShape_pairL GE s.Ps _ _ _ _ (mainAt_laws cs sh s hM)).1
      (ldShape_pairR GE s.Ps _ _ _ _ (maskAt_laws cs sh s hZ hA)).1).1).2 r (pairAt_fix _ _ _ r)
    ((ldShape_comp GE s.Ps _ _ _ _ _
      (ldShape_pairL GE s.Ps _ _ _ _ (mainAt_laws cs sh s hM)).1
      (ldShape_pairR GE s.Ps _ _ _ _ (maskAt_laws cs sh s hZ hA)).1).2 r
      ((ldShape_pairL GE s.Ps _ _ _ _ (mainAt_laws cs sh s hM)).2 r (mainAt_fix cs sh s hM r))
      ((ldShape_pairR GE s.Ps _ _ _ _ (maskAt_laws cs sh s hZ hA)).2 r
        (maskAt_fix cs sh s hZ r)))

end Port

/-- The whole arrangement. -/
theorem Rows.rho_fix {S : Sig GE} (R : Rows S) (h : R.Good) {e : ℕ} (he : e < R.s.d)
    (hv : ∀ a, (R.view a).Fix e) : R.Sh.rho.Fix e :=
  (ldGroup_shape_laws GE S R.G R.Sh (R.sh_ok h)).2 R.s.d R.s.d e (Sg.fit_cM h.sized).dist he
    (Sg.fit_cZ h.sized).dist he ((ldShape_fam GE R.s.Ps R.G.A _ _ R.view h.view).2 e hv)

namespace Fam
variable {S : Sig GE} {s : Sg} (F : Fam S s)

/-- `Fix` of every member's change of shape. -/
def FixAt (e : ℕ) : Prop := ∀ o k, (F.mb o k).view.Fix e

variable {F}

theorem FixAt.sub {e : ℕ} (h : F.FixAt e) (kp : S.O → Prop) [DecidablePred kp] :
    (F.sub kp).FixAt e := fun a k => h a.1 k

theorem rho_fix (e : ℕ) (hs : s.Sized) (h1 : 1 ≤ s.h + s.g) (h : F.Ok) (he : e < s.d)
    (hv : F.FixAt e) : (F.rows e).Sh.rho.Fix e :=
  Rows.rho_fix (F.rows e) (Fam.good e hs h1 h) he fun a => hv a.1 a.2

end Fam

end Johnson.Top.H

#print axioms Johnson.Top.H.membPort_fix
#print axioms Johnson.Top.H.Rows.rho_fix
#print axioms Johnson.Top.H.Fam.rho_fix
