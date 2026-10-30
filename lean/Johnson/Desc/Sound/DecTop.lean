-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/DecTop.lean: ONE DECODER OF THE STORED TABLE FOR THE TABLE OF JOINTS AND FOR THE
TOP STATEMENTS. Two definitions and two lemmas. No protocol's soundness is said.

Why. The table of joints reads the stored table through plain functions (`Strs.cell`,
Johnson/Desc/Msg.lean) and a letter decT (`decodesOf`, `pinWOf`, MeaningSig.lean); the top
statements have a decoder D of their own, of the stored table's string and the key file's record.
TWO LETTERS FOR ONE DECODER CAN PART IN SILENCE. Here decT is MADE of D.
  `tabBack a cell`: the stored table's string, of the plain reader: at a place at which the reader
    shows nothing: the symbol (0, []).
  `tabBack_cellAt` (proved): at the reader that `strsOf` makes of a statement's oracles it is the
    statement's own stored table: no place falls to the filler.
  `decTop D recOf a`: decT := D at that string and at the record that recOf reads off the public
    part.
  `decTop_at` (proved): at a statement's oracles it is D at the statement's own stored table.
D IS A LETTER HERE: WHICH DECODER IS MEANT (the top statements' guarded one: "none" at a collision)
is said where it is laid in.

Limits. recOf is a letter. Nothing on hiding.

Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.MsgAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Sound
open OnBytes.Maker
open _root_.Run.PQ (CK SgX)
open _root_.Iop (oneExternalString)

/-- The stored table's string, of the plain reader. -/
def tabBack (a : ℕ) (cell : ℕ → Option (ℕ × List UInt64)) : (oneExternalString (2 ^ a) SgX).Str :=
  fun i => (cell i.val).getD (0, [])

/-- At the reader that `strsOf` makes it is the statement's own stored table. -/
theorem tabBack_cellAt (Fr : Frame) (y : Fr.E.Str) : tabBack Fr.a (strsOf Fr y).cell = y.1 := by
  funext i
  show ((cellAt Fr y i.val).getD (0, [])) = y.1 i
  unfold cellAt
  rw [dif_pos i.isLt]
  rfl

/-- **The table's letter decT, made of the top statements' decoder.** -/
def decTop {P S Rec M : Type} (a : ℕ) (D : (oneExternalString (2 ^ a) SgX).Str → Rec → Option M)
    (recOf : P → Rec) : (ℕ → Option (ℕ × List UInt64)) → P × S → Option M :=
  fun cell p => D (tabBack a cell) (recOf p.1)

/-- At a statement's oracles it is D at the statement's own stored table. -/
theorem decTop_at {P S Rec M : Type} (Fr : Frame)
    (D : (oneExternalString (2 ^ Fr.a) SgX).Str → Rec → Option M) (recOf : P → Rec) (y : Fr.E.Str) (p : P × S) :
    decTop Fr.a D recOf (strsOf Fr y).cell p = D y.1 (recOf p.1) := by
  unfold decTop
  rw [tabBack_cellAt]

end VerifiableInference.Desc.Sound

#print axioms VerifiableInference.Desc.Sound.tabBack_cellAt
#print axioms VerifiableInference.Desc.Sound.decTop_at
