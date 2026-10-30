-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoLookPubZ.lean.
The share of the lookup on the digits in a sub-proof's public record, as a value.

Main names:
  `lookPubZ tl en mk next rd₀ St`: the record `LookPub` (OnBytes/Tie/Pv/Lookup/Ends/FoLookPub.lean):
    the public numbers are the smallness test's own (`tl.f9`); the layout is `digL5`
    (OnBytes/Tie/Pv/Lookup/Digits/PortEnds.lean) at the addresses en of the arrays' entries and mk
    of the mask row's, with the first slot next. It is free in the statements' type St, in the type
    J₀ of the entries and in the base reading M₀.
  `lookPubZ_ok`: `LookPubOK` at the arguments with which the byte-level verifier calls `Forest.pad`
    for the digits, with lm := 5, if `ShapeOf` holds of `tl.f9`.
  `lookPubZ_look7`: so `FoNums.ok` of its public numbers.
  `lookPubZ_in`: what the typed block's own joint before says at this value: what rides, and the
    digits' claim `DigIn` (OnBytes/Tie/Pv/Lookup/Digits/PortKnow5.lean), under the test
    `shapeTest2`.

Limits: `ShapeOf` of `tl.f9` is a premise: of the records that Verify.publicOf returns `Made` is
shown (Fo.Pub.public_made, OnBytes/Tie/Pv/Lookup/Ends/FoMadePublic.lean), which leaves Forest.pubAsk
out. en, mk and next are free: no clause asks that different places are different entries; that next
is the lookup's first slot in a run is not said here (Fo.Next0.planned_door0,
OnBytes/Tie/Pv/Lookup/Ends/FoNext0.lean, has next 0 in the plans of attention and the layers). No
statement uses the record yet.
Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoLookPub
import OnBytes.Tie.Pv.Lookup.Digits.PortKnow5

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Fo.Pub2
open OnBytes OnBytes.Model OnBytes.DgP Cb Cb.Fo Cb.LdLkp Iop IOR

variable {M₀ J₀ : Type} [Fintype J₀] [DecidableEq J₀]

/-- The digits' share of the public record. -/
def lookPubZ (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (next : ℕ) (rd₀ : M₀ → J₀ → Cb.Gl.E)
    (St : Type) : LookPub M₀ St where
  h := tl.f9
  J₀ := J₀
  L := digL5 Cb.Gl.E tl en mk next St
  rd₀ := rd₀

theorem lookPubZ_ok (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (next : ℕ)
    (rd₀ : M₀ → J₀ → Cb.Gl.E) (St : Type)
    (hS : ShapeOf #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb tl.f9) :
    LookPubOK (lookPubZ tl en mk next rd₀ St) #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb 5 next mk
      (plV tl en) where
  shape := hS
  lm5 := le_refl 5
  lmT := Nat.le_add_left 5 _
  masks := fun _ => rfl
  cells := fun t k j _ => digL5_cell en mk next St t k j

theorem lookPubZ_look7 (tl : HTailF2) (en : Ent3 → J₀) (mk : ℕ → J₀) (next : ℕ)
    (rd₀ : M₀ → J₀ → Cb.Gl.E) (St : Type)
    (hS : ShapeOf #[tl.z1.call, tl.z2.call] tl.f9.pub tl.lidb tl.f9) :
    FoNums.ok (lookPubZ tl en mk next rd₀ St).h = true :=
  (lookPubZ_ok tl en mk next rd₀ St hS).ok

/-- The typed block's own joint before, at this value. -/
theorem lookPubZ_in {tl : HTailF2} {pp : ℕ} (h : shapeTest2 tl pp = true) (en : Ent3 → J₀)
    (mk : ℕ → J₀) (next : ℕ) (rd₀ : M₀ → J₀ → Cb.Gl.E) {St Kc M Wp : Type} {Ex : ExtSpec}
    (R0 : Rels Kc St Ex (M × Wp)) (rd : M → M₀) :
    forIn Cb.Gl.E (lookPubZ tl en mk next rd₀ St).h (lookPubZ tl en mk next rd₀ St).L R0
        ((lookPubZ tl en mk next rd₀ St).msg rd) =
      ⟨fun x y w => R0.rel x y w ∧ DigIn tl en (rd₀ (rd w.1)),
        fun a w => R0.relR a w ∧ DigIn tl en (rd₀ (rd w.1)), R0.on, R0.core⟩ :=
  forIn_dig5 h en mk next R0 fun m => rd₀ (rd m)

end Fo.Pub2
