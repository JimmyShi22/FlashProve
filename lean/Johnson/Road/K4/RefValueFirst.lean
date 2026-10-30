-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefValueFirst.lean: THE FIRST GROUP's VALUE AT THE REFERENCE SIZES, AT WHICH
`Plan4F.MeetsF` (Johnson/Road/K4/PlanMapsFirst.lean) HOLDS WHERE THE TEST `recordB X 0` SAYS TRUE,
K4's TEXT COVERS THE RECORD, THE SHAPE's NUMBER la IS 16 AND THE PLACE HOLDS THE RECORD's LAYERS AND
THE FIRST GROUP's PLAN (that the first three hold anywhere is a run, no theorem). The twin, for the
first group, of `refL` and `ref_meets` (Johnson/Road/K4/RefValue.lean), whose head says what is a
theorem, what a run and what a premise. A definition and five statements.

  `ref_hd`: 5120 = 80 · 2^6, by the kernel.

  `refLF R tok nT nI`: `refL R 0 _ nT nI`, its ns one more (in the first group the merge's own slots
    begin one slot later), with the first group's letters: ls := 6, nb := 80, gB := 7 (a feature has
    6 bits in its block; 80 blocks; 7 bits of blocks: 5120 = 80 · 2^6, 80 ≤ 2^7), and the request's
    tokens, a free letter.
  `refF_sizes`: at a layout for a shape with la = 16 that agrees with `Dim.ref`: ls = 6 and
    lPd - ls = 7.
  `refF_meets`: `MeetsF` holds of `(refLF R tok nT nI).planF` at `publicOf`'s own record.
  `refF_room`: the embedding's slot and the merge's own slots lie within ns.
  `refF_mask`: `MaskLetters` (Johnson/Road/K4/MaskTiesH.lean) holds of it, at every message, with
    the mask the value's own.

WHAT IS MORE THAN IN A LATER GROUP: the library's reference sizes do not hold the shape's number la
(the logarithm of the rows of a block in a long read): hla is a premise. A run evaluates it at
linesKF: Johnson/Road/K4/GuardMemberFirst.lean [not in this library].

Limits. Those of RefValue.lean: the public half alone. The conditions C and hk need no first twin:
`ref_chOK` (Johnson/Road/K4/RefConds.lean) and `ref_hk` (RefValue.lean) bar no group.
-/
import Johnson.Road.K4.RefValue
import Johnson.Road.K4.ValueSlotsFirst
import Johnson.Road.K4.PlanPublicFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (layout)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Road.Alg (recordB bridgeB_parts returns_of_record)
open Inst.Model (Scl)
open Inst.Model.FFSeg (Dim)
open OnBytes.Desc.First.K4 (covers Par)

variable {M Xs : Type}

/-- 5120 = 80 · 2^6. -/
theorem ref_hd : Dim.ref.d = 80 * 2 ^ 6 := by decide +kernel

/-- **The first group's value at the reference sizes.** -/
noncomputable def refLF [scl : Scl] (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ) :
    Plan4LF GE M Xs where
  toPlan4L :=
    { refL R 0 (by norm_num) nT nI with ns := (refL R 0 (by norm_num) nT nI).ns + 1 }
  ls := 6
  nb := 80
  gB := 7
  hnb := by norm_num
  hd := ref_hd
  tok := tok

/-- The two numbers of the blocks, at a layout for a shape with la = 16 that agrees with `Dim.ref`.
-/
theorem refF_sizes {hS : Layer.Shape} {pc : List (List String)} {y : Layer.Lay}
    (hy : layout hS pc = .ok y) (Z : Sized hS Dim.ref) (hla : hS.la = 16) :
    y.ls = 6 ∧ y.lPd - y.ls = 7 := by
  have C := Model.Fit.layout_caps hy
  have e1 : hS.lt = 10 := Z.lT.symm
  have e2 : y.ls = 6 := by
    rw [C.ls, hla, e1]
  have e3 : y.lPd = 13 := by
    rw [(laySizes_of_layout hy).lPd, ← Z.d]
    decide +kernel
  exact ⟨e2, by rw [e3, e2]⟩

variable [scl : Scl] {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {p : Par}
  {tk : Array Nat}

/-- **`MeetsF` holds of it**, at `publicOf`'s own record, where `recordB` says true, K4's text
covers the record, the group is the first and la is 16. -/
theorem refF_meets (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = true) (hc : covers X.layers = true)
    (hla : (layerShape X.P).la = 16) :
    (refLF R tok nT nI).planF.MeetsF p (layerShape X.P) X.P.polCalls := by
  obtain ⟨hy, _, _, _, _, hW, tb⟩ := returns_of_record h t
  obtain ⟨_, Z, _⟩ := bridgeB_parts tb
  obtain ⟨s1, s2⟩ := refF_sizes hy Z hla
  exact (refLF R tok nT nI).planF.meetsF_public h hP hG hc Z (wsLayOf_units hW).1.symm hg0
    s1.symm s2.symm

/-- The embedding's slot, and the merge's own slots behind it, lie within ns. -/
theorem refF_room (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ) :
    (refLF R tok nT nI).toPlan4L.slots.f7 ≤ (refLF R tok nT nI).ns ∧
      (refLF R tok nT nI).toPlan4L.slots.f7 + 1 + 1 + (2 * (refLF R tok nT nI).planF.kW + 1) ≤
        (refLF R tok nT nI).ns := by
  have h := (ref_room R 0 (by norm_num) nT nI).2
  constructor
  · show (refL R 0 (by norm_num) nT nI).slots.f7 ≤ (refL R 0 (by norm_num) nT nI).ns + 1
    omega
  · show (refL R 0 (by norm_num) nT nI).slots.f7 + 1 + 1 +
        (2 * (refL R 0 (by norm_num) nT nI).plan.kW + 1) ≤
      (refL R 0 (by norm_num) nT nI).ns + 1
    omega

/-- **`MaskLetters` holds of it**, at every message, with the mask the value's own. -/
theorem refF_mask (R : RefLetters M Xs) (tok : Xs → ℕ → ℕ) (nT nI : ℕ) (mm : M) :
    MaskLetters (refLF R tok nT nI).toPlan4L mm (R.maskAt mm) R.n0 nT nI where
  n0 := rfl
  nT := rfl
  nI := rfl
  numI := rfl
  isM := fun _ _ => rfl
  room := (refF_room R tok nT nI).1

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ref_hd
#print axioms OnBytes.Road.K4.refF_sizes
#print axioms OnBytes.Road.K4.refF_meets
#print axioms OnBytes.Road.K4.refF_room
#print axioms OnBytes.Road.K4.refF_mask
