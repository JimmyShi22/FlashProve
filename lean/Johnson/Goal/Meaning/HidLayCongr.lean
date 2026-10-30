-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/HidLayCongr.lean: the library's record on a group of layers reads the entries
within the matrices' shapes alone.

LayerOrd (Johnson/Road/FormsKeysLinkL.lean) speaks of a list Mz of integer matrices on all numbers.
By layerOrd_iff it says: the entries within the shapes are small, and link 2 g is in order at libMZ
y g Mz; and libMZ (Johnson/Road/FormsKeysDictZ.lean) is cut to the shapes: it reads Mz at number
portNo y σ, row r and column c with InZ y σ r c alone. So two lists that agree there meet LayerOrd
together.

Main names:
  AgreeZ y Mz Mz'   the two lists agree at (portNo y σ, r, c) wherever InZ y σ r c.
  libMZ_congr, smallM_congr   the two steps.
  layerOrd_congr_core   with layerOrd_iff: the statement above, in scope.

What is not claimed. Anything on a run. The program does not import this file.
-/
import Johnson.Goal.Meaning.HidLaws
import Johnson.Road.FormsKeysLinkL

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace Meaning

open OnBytes OnBytes.Road OnBytes.Road.L5
open OnBytes.Model.Verify (publicOf layerShape)
open OnBytes.Model.Layer (Lay)

/-- The two lists agree within the shapes of the matrices that hold cells. -/
def AgreeZ (y : Lay) (Mz Mz' : Mats ℤ) : Prop :=
  ∀ σ r c, InZ y σ r c → Mz (portNo y σ) r c = Mz' (portNo y σ) r c

theorem AgreeZ.symm {y : Lay} {Mz Mz' : Mats ℤ} (H : AgreeZ y Mz Mz') : AgreeZ y Mz' Mz :=
  fun σ r c h => (H σ r c h).symm

theorem libMZ_congr {y : Lay} {Mz Mz' : Mats ℤ} (H : AgreeZ y Mz Mz') (g : ℕ) :
    libMZ y g Mz = libMZ y g Mz' := by
  funext s r c
  unfold libMZ
  by_cases hC : CutM y g s r c
  · rw [if_pos hC, if_pos hC]
    unfold libM
    rcases hC with ⟨e, hz, -⟩ | ⟨e, h7, hz⟩
    · rw [if_pos e, if_pos e]
      exact H _ _ _ hz
    · rw [if_neg (by omega), if_pos ⟨e, h7⟩, if_neg (by omega), if_pos ⟨e, h7⟩]
      exact H 6 _ _ hz
  · rw [if_neg hC, if_neg hC]

theorem smallM_congr {y : Lay} {Mz Mz' : Mats ℤ} (H : AgreeZ y Mz Mz') (S : SmallM y Mz) :
    SmallM y Mz' := fun σ r c h => by
  rw [← H σ r c h]
  exact S σ r c h

section Core
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- **In scope the record on a group of layers reads the entries within the shapes alone.** -/
theorem layerOrd_congr_core (h : publicOf pol KL lay = .ok X) (C : Hd.PublicCore X.P) {g : ℕ}
    (hg : g < 12) {Mz Mz' : Mats ℤ} (H : AgreeZ X.y Mz Mz') {Wi : Inst.Model.Mat}
    {x : Cm.Seg.XI} (O : LayerOrd (layerShape X.P) X.layers.sc X.y g Mz Wi x) :
    LayerOrd (layerShape X.P) X.layers.sc X.y g Mz' Wi x := by
  have B := (Hd.eleven_of_core h C (Hd.npOf X.hS)).1
  have I := layerOrd_iff B.lay B.switches B.sized B.sized2 B.p4 Cm.Seg.Hd.main
  obtain ⟨a, b⟩ := (I Mz Wi hg X.layers.sc (Hd.npOf X.hS) x).1 O
  refine (I Mz' Wi hg X.layers.sc (Hd.npOf X.hS) x).2 ⟨smallM_congr H a, ?_⟩
  rw [← libMZ_congr H g]
  exact b

end Core

end Meaning

#print axioms Meaning.AgreeZ.symm
#print axioms Meaning.libMZ_congr
#print axioms Meaning.smallM_congr
#print axioms Meaning.layerOrd_congr_core
