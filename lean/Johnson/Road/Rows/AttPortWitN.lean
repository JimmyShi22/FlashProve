-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/Rows/AttPortWitN.lean: the dictionary between names of late entries and entries of the
vector of tables can be met at every record of names; with the premises on names it is met at the
record of the listed names.

Johnson/Road/Rows/AttPortWit.lean meets the premises on the letters at the record lateW, in which
two good names can have one place: that record is the record of no lay. This file meets them at
lateN (Cb/Pv/Att/End/Names.lean), whose late entries are the listed names themselves. There the
places are one-to-one within a table (Johnson/Road/Rows/AttLayInj.lean).

Main definitions: uAt: the late entry j holds the entry of the vector at the place of j's name.
Main theorems.
 - lateAt_any: LateAt holds of every record of names Y and uAt, for all beginnings and places.
 - letters_names: at lateN: LateAt, LateTabs, FirstTabs and the ten premises on names, together, in
   every world, for every record of what the claims read and every late entry j0 to start from.

What is not claimed. The values uAt are the world's own entries, read back: they are not the values
that a sub-proof's tables are meant to have. No lay is given: that there is a lay of early and late
entries in whose world the dictionary holds at lateN (U3Lay in Johnson/Road/Rows/AttPortWorld.lean)
is not shown; it asks also that the tables do not overlap. SlotAt and the premises on the verifier's
run are not met here.


-/
import Johnson.Road.Rows.AttPlaces
import Cb.Pv.Att.End.Names

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.Rows

open OnBytes.Model (World)
open OnBytes.Attention (Heard)
open OnBytes.Road.Hd (rdW)
open Inst.Model.AttSeg (Raw)
open Cb.Pv.Att.End (AttTab LateLay NameJ lateN LinGood Good6b Good6d Good8 Good11 Good12 GoodM
  Good16 Good18 GoodH)

variable {K : Type}

/-- The late entry j holds the entry of the vector of tables at the place of j's name. -/
def uAt {J₂ : Type} (W : World K) (h : Heard) (K3 : ℕ) (Y : LateLay AttTab J₂) (tabOf : AttTab → ℕ)
    (place : AttTab → Raw → ℕ) (j : J₂) : K :=
  rdW W h.iU3 K3 (tabOf (Y.nm j).1 + place (Y.nm j).1 (Y.nm j).2)

/-- The dictionary can be met at every record of names, in every world. -/
theorem lateAt_any {J₂ : Type} (W : World K) (h : Heard) (K3 : ℕ) (Y : LateLay AttTab J₂)
    (tabOf : AttTab → ℕ) (place : AttTab → Raw → ℕ) :
    LateAt W h K3 Y tabOf place (uAt W h K3 Y tabOf place) := by
  intro T r hr
  unfold uAt
  rw [Y.ok (T, r) hr]

/-- All premises on the letters that tie the two sides, at the record of the listed names. -/
theorem letters_names (W : World K) (h : Heard) (K3 : ℕ)
    (j0 : NameJ (L5.dimOf h.S) h.S.ls h.S.cf.lmS) :
    LateAt W h K3 (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) (tabOfAtt h) (placeAtt h.S)
        (uAt W h K3 (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) (tabOfAtt h) (placeAtt h.S)) ∧
      LateTabs h (tabOfAtt h) ∧
      FirstTabs h (h.t.score.getD 0 default) (h.t.score.getD 1 default) (tabOfAtt h) ∧
      LinGood (L5.dimOf h.S) h.S.ls h.S.cf.lmS (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good6b (L5.dimOf h.S) h.S.ls (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good6d (L5.dimOf h.S) h.S.ls (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good8 (L5.dimOf h.S) h.S.ls (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good11 (L5.dimOf h.S) h.S.ls h.S.cf.lmS (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good12 (L5.dimOf h.S) h.S.ls h.S.cf.lmS (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      GoodM (L5.dimOf h.S) (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good16 (L5.dimOf h.S) h.S.ls (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      Good18 (L5.dimOf h.S) h.S.ls (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) ∧
      GoodH (L5.dimOf h.S) (lateN (L5.dimOf h.S) h.S.ls h.S.cf.lmS j0) :=
  ⟨lateAt_any W h K3 _ _ _, lateTabs_att h, firstTabs_att h,
    Cb.Pv.Att.End.names_lin _ _ _ j0, Cb.Pv.Att.End.names6b _ _ _ j0,
    Cb.Pv.Att.End.names6d _ _ _ j0, Cb.Pv.Att.End.names8 _ _ _ j0,
    Cb.Pv.Att.End.names11 _ _ _ j0, Cb.Pv.Att.End.names12 _ _ _ j0,
    Cb.Pv.Att.End.namesM _ _ _ j0, Cb.Pv.Att.End.names16 _ _ _ j0,
    Cb.Pv.Att.End.names18 _ _ _ j0, Cb.Pv.Att.End.namesH _ _ _ j0⟩

end OnBytes.Road.Rows

#print axioms OnBytes.Road.Rows.lateAt_any
#print axioms OnBytes.Road.Rows.letters_names
