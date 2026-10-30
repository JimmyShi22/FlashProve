-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/Att/K05PinDec.lean: THE PIN, ONCE MORE: (1) in its barest form, at any reduction;
(2) a family of fillers of `PinItem` (Att/K05Seam.lean) that is not silly: "the oracles' words
decode,
with what the record holds, to the world's part".

Main names:
  `mOfHolds`, `pin_of_item`: AT ANY REDUCTION: an item in front HA and an item behind HB; HA fixes
    the part (two worlds with HA at one statement have one part); HB rides back (where the
    reduction puts out b from a, HB at (b, w) gives HA at (a, w)); the relation behind gives HB:
    then the pin: part w = mOfHolds … a.
  `PinItem.ofDec`: from a reading `words` of the frame's oracles that reads the stored table and
    trees below the base alone, a decoder `dec` with what is read of the record, a side condition
    `side`, and a reading rc of the record that the seat's lay keeps: the item
    "side ∧ dec (rc s) (words y) = some (part w)" IS a PinItem: it fixes the part because a decoder
    has one value.
  `mOfItem_ofDec`: there the part that the item fixes at a statement is the decoder's own value,
    wherever a world has the item: no choice is left in it.
  `ofDec_bites`: such an item is neither of the two silly fillings (False; True): where the side
    condition holds and the decoder returns m, a world whose part is m has the item, and a world
    whose part is another has it not.

Why. The filling that is meant (the table of joints' item on the segment's first moment: each
sampled tenant's committed word decodes, with its sample as the record holds it, to the witness's
message) has this shape: words := the members' words off the strings; dec := the library's decoder
with a sample, member by member; side := "the seats fit and every leaf is shown". THAT FILLING IS
NOT TYPED HERE.
Limits. words, dec, side, rc, part are letters. That a decoder of the release's codes has these
laws, that the members' trees are numbered below the base, and that the first chain's seat keeps the
samples, are not shown.
Nothing is claimed on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Att.K05Seam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.Att.P
open Iop OnBytes OnBytes.Model
open VerifiableInference.Desc.Sound (Frame)

/-! ## At any reduction -/

section
variable {A B W Mg : Type}

open Classical in
/-- The part that an item fixes at a statement; m0 where no world has the item there. -/
noncomputable def mOfHolds (HA : A → W → Prop) (part : W → Mg) (m0 : Mg) (a : A) : Mg :=
  if h : ∃ w, HA a w then part h.choose else m0

/-- **The pin in its barest form.** -/
theorem pin_of_item (K : Reduction A B) (on : A → Prop) (HA : A → W → Prop) (HB : B → W → Prop)
    (part : W → Mg) (fixes : ∀ a w w', HA a w → HA a w' → part w = part w')
    (rides : ∀ a τ b w, on a → K.out a τ = some b → HB b w → HA a w) (R' : B → W → Prop)
    (hR' : ∀ b w, R' b w → HB b w) (m0 : Mg) :
    ∀ a τ b w, on a → K.out a τ = some b → R' b w → part w = mOfHolds HA part m0 a := by
  intro a τ b w ha hb hw
  have k : HA a w := rides a τ b w ha hb (hR' b w hw)
  have ex : ∃ w, HA a w := ⟨w, k⟩
  unfold mOfHolds
  rw [dif_pos ex]
  exact fixes a _ _ k ex.choose_spec

end

/-! ## Fillers of the shape "decodes to" -/

section
variable {S W Mg : Type} {F : Frame}

/-- **"The words decode to the world's part" is a PinItem.** -/
def PinItem.ofDec (seat : Seat S) (base : ℕ) {Rc Wd : Type} (rc : S → Rc)
    (hlay : ∀ s h G s', seat.lay s h G = some s' → rc s' = rc s) (words : F.E.Str → Wd)
    (hwords : ∀ y y', SameBelow F base y y' → words y' = words y) (dec : Rc → Wd → Option Mg)
    (side : Rc → Wd → Prop) (part : W → Mg) : PinItem F seat base W Mg where
  Rc := Rc
  rc := rc
  holds := fun r y w => side r (words y) ∧ dec r (words y) = some (part w)
  part := part
  fixes := fun _ _ _ _ h h' => Option.some.inj (h.2.symm.trans h'.2)
  lay := hlay
  fenced := fun _ _ _ _ hs h => by
    rw [hwords _ _ hs] at h
    exact h

/-- There the part that the item fixes is the decoder's own value. -/
theorem mOfItem_ofDec (seat : Seat S) (base : ℕ) {Rc Wd : Type} (rc : S → Rc)
    (hlay : ∀ s h G s', seat.lay s h G = some s' → rc s' = rc s) (words : F.E.Str → Wd)
    (hwords : ∀ y y', SameBelow F base y y' → words y' = words y) (dec : Rc → Wd → Option Mg)
    (side : Rc → Wd → Prop) (part : W → Mg) (m0 : Mg) (a : S × F.E.Str) (w : W)
    (h : (PinItem.ofDec seat base rc hlay words hwords dec side part).holds (rc a.1) a.2 w) :
    dec (rc a.1) (words a.2) =
      some (mOfItem (PinItem.ofDec seat base rc hlay words hwords dec side part) m0 a) := by
  have ex : ∃ w, (PinItem.ofDec seat base rc hlay words hwords dec side part).holds
      ((PinItem.ofDec seat base rc hlay words hwords dec side part).rc a.1) a.2 w := ⟨w, h⟩
  unfold mOfItem
  rw [dif_pos ex]
  exact ex.choose_spec.2

/-- **Such an item is neither silly filling**: where the side condition holds and the decoder
returns m, a world whose part is m has the item and a world whose part is another has it not. -/
theorem ofDec_bites (seat : Seat S) (base : ℕ) {Rc Wd : Type} (rc : S → Rc)
    (hlay : ∀ s h G s', seat.lay s h G = some s' → rc s' = rc s) (words : F.E.Str → Wd)
    (hwords : ∀ y y', SameBelow F base y y' → words y' = words y) (dec : Rc → Wd → Option Mg)
    (side : Rc → Wd → Prop) (part : W → Mg) (r : Rc) (y : F.E.Str) (m : Mg)
    (hs : side r (words y)) (hd : dec r (words y) = some m) (w w' : W) (hw : part w = m)
    (hw' : part w' ≠ m) :
    (PinItem.ofDec seat base rc hlay words hwords dec side part).holds r y w ∧
      ¬ (PinItem.ofDec seat base rc hlay words hwords dec side part).holds r y w' :=
  ⟨⟨hs, by rw [hd, hw]⟩, fun h => hw' (Option.some.inj (h.2.symm.trans hd))⟩

end

end VerifiableInference.Desc.First.Att.P

#print axioms VerifiableInference.Desc.First.Att.P.pin_of_item
#print axioms VerifiableInference.Desc.First.Att.P.mOfItem_ofDec
#print axioms VerifiableInference.Desc.First.Att.P.ofDec_bites
