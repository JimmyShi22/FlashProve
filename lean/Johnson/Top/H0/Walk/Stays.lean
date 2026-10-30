-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/Walk/Stays.lean: WHAT A BLOCK's YES LEAVES OF THE ORACLES' STRINGS, AS ONE RELATION.
A definition and three small lemmas, over Johnson/Desc/Msg.lean alone: so that whoever states "my
sentence reads of the strings no more than this" need import no table and no kind.

  Stays base y y'   the stored table's cells, and every column of a tree whose number is below base,
                    are in y' what they are in y. OF A TREE AT OR ABOVE base NOTHING IS SAID: "the
                    strings are the same" is false as an equation at a piece's yes
  Stays.refl, Stays.trans, stays_mono (a smaller base)

That every piece's yes gives it, at the piece's own base: StaysBehind.lean. No soundness statement.

-/
import Johnson.Desc.Msg

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.Desc.First.Walk.Tied
open VerifiableInference.Desc (Strs)

/-- The stored table's cells, and every column of a tree whose number is below base, are in y' what
they are in y. (What every piece leaves of the strings: Johnson/Desc/Sound/StringsStay.lean. Of a
tree that is not yet sent nothing is said: the whole strings are unturned only where these are empty
in front: Johnson/Desc/Sound/PieceYes.lean, left_all.) -/
def Stays (base : Nat) (y y' : Strs) : Prop :=
  (∀ x, y'.cell x = y.cell x) ∧ ∀ j x, j < base → y'.col j x = y.col j x

theorem Stays.refl (base : Nat) (y : Strs) : Stays base y y := ⟨fun _ => rfl, fun _ _ _ => rfl⟩

theorem Stays.trans {base : Nat} {y y' y'' : Strs} (h : Stays base y y') (h' : Stays base y' y'') :
    Stays base y y'' :=
  ⟨fun x => (h'.1 x).trans (h.1 x), fun j x hj => (h'.2 j x hj).trans (h.2 j x hj)⟩

theorem stays_mono {base base' : Nat} {y y' : Strs} (hb : base' ≤ base) (h : Stays base y y') :
    Stays base' y y' := ⟨h.1, fun j x hj => h.2 j x (Nat.lt_of_lt_of_le hj hb)⟩

end Johnson.Desc.First.Walk.Tied
