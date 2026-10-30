-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortWit.lean: the dictionary between names of late entries and entries of the
vector of tables, and the premises on names, can be met together, in every world and for every
record of what the verifier's claims read.

The theorems of Johnson/Road/Rows/AttPortLate.lean, AttPortFirst.lean and AttPortLin.lean stand
under premises of two kinds. Some speak of the verifier's run: the shape, the lengths of points,
that a routine has returned, that the library's challenges are the verifier's. The others speak of
the letters that tie the two sides: the record Y of the late entries' names, where the tables begin,
the values u of the late entries (LateAt, LateTabs, FirstTabs, and the ten premises on names). This
file shows that the second kind puts no condition on the first: for every world W, every record h
and every number K3 of columns there are Y and u at which all of them hold together.

Main definitions: uOf: the late entry of a name holds the entry of the vector at the name's place.
Main theorems.
 - lateAt_wit: LateAt holds of Cb.Pv.Att.End.lateW B and uOf, for all beginnings and places.
 - letters_met: LateAt, LateTabs, FirstTabs and the ten premises on names, together.

What is not claimed. The record lateW has one late entry for each name with bounded indices, under
every table. It is not the programs' message, and it is the record of no lay: two of its good names,
one cell's name at two positions, have one place, so the premise U3Lay of
Johnson/Road/Rows/AttPortWorld.lean, which gives a late entry the address of its place, fails at
lateW. So the premises on names and LateAt in the world of a lay are shown together nowhere. On the
listed names (Cb/Pv/Att/End/Names.lean) the places are one-to-one within a table
(Johnson/Road/Rows/AttLayInj.lean); that the tables do not overlap is tried at the small
configuration (Johnson/Road/Rows/TestAttPlaces.lean). The values uOf are the world's own entries,
read back: they are not the values that a sub-proof's tables are meant to have. letters_met does not
state where the six tables of AttPortLin.lean begin (they hold of tabOfAtt by definition), nor
SlotAt. Of the premises of the first kind, Johnson/Road/Rows/TestAttEnds58.lean evaluates the
lengths of six points, one point's agreement with the library's, and that the readers of the last
four sumchecks' end values return; no test evaluates the others (the limbs of the tensors, the
lengths of the tables' points, the regions' numbers of bits).


-/
import Johnson.Road.Rows.AttPlaces
import Cb.Pv.Att.End.Wit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (World)
open OnBytes.Attention (Heard)
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (AttTab RawC lateW dec enc dec_enc bd LinGood Good6b Good6d Good8 Good11 Good12
  GoodM Good16 Good18 GoodH)

variable {K : Type}

/-- The late entry of a name holds the entry of the vector of tables at the name's place. -/
def uOf (W : World K) (h : Heard) (K3 : ℕ) (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) (B : ℕ)
    (j : AttTab × RawC B) : K :=
  rdW W h.iU3 K3 (tabOf j.1 + place j.1 (dec B j.2))

/-- The dictionary can be met, in every world. -/
theorem lateAt_wit (W : World K) (h : Heard) (K3 : ℕ) (tabOf : AttTab → ℕ)
    (place : AttTab → Raw → ℕ) (B : ℕ) :
    LateAt W h K3 (lateW B) tabOf place (uOf W h K3 tabOf place B) := by
  intro T r hr
  show rdW W h.iU3 K3 (tabOf T + place T (dec B (enc B r))) = _
  rw [dec_enc B r hr]

/-- All premises on the letters that tie the two sides can be met together, in every world and for
every record of what the claims read. -/
theorem letters_met (W : World K) (h : Heard) (K3 : ℕ) :
    LateAt W h K3 (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) (tabOfAtt h) (placeAtt h.S)
        (uOf W h K3 (tabOfAtt h) (placeAtt h.S) (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      LateTabs h (tabOfAtt h) ∧
      FirstTabs h (h.t.score.getD 0 default) (h.t.score.getD 1 default) (tabOfAtt h) ∧
      LinGood (L5.dimOf h.S) h.S.ls h.S.cf.lmS (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good6b (L5.dimOf h.S) h.S.ls (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good6d (L5.dimOf h.S) h.S.ls (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good8 (L5.dimOf h.S) h.S.ls (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good11 (L5.dimOf h.S) h.S.ls h.S.cf.lmS (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good12 (L5.dimOf h.S) h.S.ls h.S.cf.lmS (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      GoodM (L5.dimOf h.S) (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good16 (L5.dimOf h.S) h.S.ls (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      Good18 (L5.dimOf h.S) h.S.ls (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) ∧
      GoodH (L5.dimOf h.S) (lateW (bd (L5.dimOf h.S) h.S.ls h.S.cf.lmS)) :=
  ⟨lateAt_wit W h K3 _ _ _, lateTabs_att h, firstTabs_att h,
    Cb.Pv.Att.End.wit_lin _ _ _ (Nat.le_refl _), Cb.Pv.Att.End.wit6b _ _ h.S.cf.lmS (Nat.le_refl _),
    Cb.Pv.Att.End.wit6d _ _ h.S.cf.lmS (Nat.le_refl _),
    Cb.Pv.Att.End.wit8 _ _ h.S.cf.lmS (Nat.le_refl _),
    Cb.Pv.Att.End.wit11 _ _ _ (Nat.le_refl _), Cb.Pv.Att.End.wit12 _ _ _ (Nat.le_refl _),
    Cb.Pv.Att.End.witM _ h.S.ls h.S.cf.lmS (Nat.le_refl _),
    Cb.Pv.Att.End.wit16 _ _ h.S.cf.lmS (Nat.le_refl _),
    Cb.Pv.Att.End.wit18 _ _ h.S.cf.lmS (Nat.le_refl _),
    Cb.Pv.Att.End.witH _ h.S.ls h.S.cf.lmS (Nat.le_refl _)⟩

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.lateAt_wit
#print axioms OnBytes.Road.Rows.letters_met
