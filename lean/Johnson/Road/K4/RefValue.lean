-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/RefValue.lean: A VALUE AT THE REFERENCE SIZES AT WHICH THESE PUBLIC PREMISES HOLD
TOGETHER WHEREVER THE TEST `recordB` SAYS TRUE (that it does anywhere is a run, no theorem):
`Plan4.Meets`; nine equations and bounds on the value's letters; the condition on the shifts of
queries and keys; `MaskLetters` and room7; the value's own eight conditions on sizes. The value: a
family, `refL R g hg nT nI`: the value with its slots and orders laid (`Plan4L`,
Johnson/Road/K4/ValueSlots.lean) at the library's reference sizes. The place: the record that the
verifier's own `publicOf` returns, in a group that is not the first. A definition and statements
with their proofs. Nothing new is argued: other lemmas and those of this folder are gathered at one
term. NOT GATHERED HERE, though theorems on K4's block ask them too: whatever speaks of a hearing, a
ledger or a witness (see the limits); which calls the second token sumcheck covers; the fits of the
signatures; that the chain's data are as asked at this value.

  `RefLetters M X`: the letters that stay free: the names of the cells; how the four kinds of
    messages are read off a witness; three functions of the statement; n0, the first free slot in
    front of K4's own rounds; a lower bound for ns; nx; v7.
  `refL R g hg nT nI`: the value: D := `Dim.ref`, tb := `tbRef`, kW := `kRef`, hW := `hRef`, L0 := g
    * 4, the weight claims numbered by `numK` (Johnson/Road/K4/NumPieces.lean), the batched
    sumcheck's end values by `num4`, the terms' by `numA`; ns so large that the merge's own slots
    lie within it. Its eight conditions on sizes: Johnson/Road/K4/RefConds.lean.
  `ref_meets`: `Plan4.Meets`. `ref_nine`: nine equations and bounds on the value's letters (nT, nI,
    numT, the terms' end values' number, room, the two numbers of the sides' own end values, the
    table of scales, the first layer). `ref_hk`: at every number l of a layer the shifts of queries
    and keys are equal or both at least 16. `ref_mask`: `MaskLetters` and room7. `Dim.ChOK` is
    `ref_chOK`; the nineteen public lines and the rotary tables' fit: `pubLines_of_record`,
    `rope_of_record` (Johnson/Road/K4/PubLinesRec.lean), which speak of the same D, tb, kW.

THE TABLE OF SCALES is a letter of the section in the library. The one that is meant is named:
`sclX X g` := `sclOf (layerShape X.P) X.layers.sc g X.layers.y.Lam`: what `sclOf`
(Johnson/Road/FormsKeysFits.lean) makes of the record's own scales. `ref_nine` and `ref_hk` take the
equation "the section's table is that one" as a premise hscl: at scl := `sclX X g` it is rfl.

WHAT IS A THEOREM, WHAT A RUN, WHAT A PREMISE.
  THEOREMS, from `publicOf`'s return and "the test `recordB X g` says true": all of the above.
    `ref_hk` takes of the test only that the shape has routed experts and that g is a group: the
    verifier's own test on the file of scales refuses unequal shifts below 16 (theorem
    `hk_of_scalesHeld`, Johnson/Road/FormsKeysRef.lean).
  A RUN, no theorem: that `recordB` (and `tablesB`, for the lines) says true: see the head of
    PubLinesRec.lean: Johnson/Road/Ends/GuardRec.lean's run at linesKF and scalesKF, 12 groups.
  PREMISES that stay: the place holds the record's layers and the group's plan; g is not 0 and below
    12; K4's text covers the record (it follows from a return of K4's hearing: `covers_of_hear`).
  NO CLASH WAS FOUND: the number of weight claims of `numK` is the plan's NCL (a theorem under
    `Meets`: `nW_eq`); the first layer g * 4 is g * Lam; room is had by the choice of ns.

Limits. THE PUBLIC HALF ALONE. Nothing is said of a hearing, of a ledger's sizes, of the lookup's
leavings, or of any premise that speaks of a witness. n0 is a free letter: that it is the ledger's
next slot in front of K4 at a run is not shown. No soundness is concluded.
-/
import Johnson.Road.K4.RefConds
import Johnson.Road.K4.MeetsRec
import Johnson.Road.K4.MeetsCovers
import Johnson.Road.K4.MaskTiesH
import Johnson.Road.K4.NumPieces
import Johnson.Road.K4.PubLinesRec
import Johnson.Road.FormsKeysRef
import Policy.Seg.HeadAsm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open OnBytes OnBytes.K.Kc OnBytes.Model OnBytes.Slice
open OnBytes.Model.Layer (nEndT)
open OnBytes.Model.Verify (Public publicOf layerShape)
open OnBytes.Road.Alg (recordB bridgeB_parts returns_of_record)
open Cb Cb.Pv.Lay Cb.Pv.Lay.At
open Inst.Model (Scl tbRef)
open Inst.Model.Layout (kRef hRef)
open Inst.Model.FFSeg (Dim Cell)
open OnBytes.Desc.First.K4 (covers Par)

/-- The letters that stay free. -/
structure RefLetters (M X : Type) where
  Jc : Type
  [finJc : Fintype Jc]
  [decJc : DecidableEq Jc]
  nameOf : Cell → Option Jc
  nx : ℕ
  cellAt : M → Jc → GE
  maskAt : M → ℕ → GE
  matAt : M → ℕ → ℕ → GE
  idxAt : M → ℕ → GE
  zOf : X → ℕ → GE
  kTg : X → GE
  kIncS : X → ℕ → GE
  n0 : ℕ
  ns : ℕ
  v7 : ℕ

attribute [instance] RefLetters.finJc RefLetters.decJc

variable {M Xs : Type}

/-- **The value at the reference sizes.** -/
noncomputable def refL [scl : Scl] (R : RefLetters M Xs) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    Plan4L GE M Xs where
  D := Dim.ref
  tb := tbRef
  L0 := g * 4
  Jc := R.Jc
  nameOf := R.nameOf
  ns := max R.ns ((slotsAt Dim.ref R.n0 nT nI).f7 + 1 + (2 * kRef + 1))
  kW := kRef
  hW := hRef
  nx := R.nx
  cellAt := R.cellAt
  maskAt := R.maskAt
  matAt := R.matAt
  idxAt := R.idxAt
  two := Policy.two_ne_GlE
  zOf := R.zOf
  kTg := R.kTg
  kIncS := R.kIncS
  n0 := R.n0
  nT := nT
  nI := nI
  v7 := R.v7
  numT := Cb.Pv.Lay.End.numA Dim.ref
  numI := num4 Dim.ref (numK Dim.ref)
  nW := nWK Dim.ref
  num := numK Dim.ref
  h5 := ref_h5
  h6 := ref_h6
  hfe := ref_hfe
  h0 := ref_h0 g
  hf := ref_hf
  hh := ref_hh
  hLay := ref_hLay hg
  hH := ref_hH

/-- Its slots in front of the merge's, and the merge's own, lie within ns. -/
theorem ref_room [scl : Scl] (R : RefLetters M Xs) (g : ℕ) (hg : g < 12) (nT nI : ℕ) :
    (refL R g hg nT nI).slots.f7 ≤ (refL R g hg nT nI).ns ∧
      (refL R g hg nT nI).slots.f7 + 1 + (2 * (refL R g hg nT nI).plan.kW + 1) ≤
        (refL R g hg nT nI).ns :=
  ⟨Nat.le_trans (by omega : (slotsAt Dim.ref R.n0 nT nI).f7 ≤
    (slotsAt Dim.ref R.n0 nT nI).f7 + 1 + (2 * kRef + 1)) (Nat.le_max_right _ _),
    Nat.le_max_right _ _⟩

/-- The table of scales that `sclOf` makes of the record's own scales, in group g. -/
@[reducible] def sclX (X : Public) (g : ℕ) : Scl :=
  sclOf (layerShape X.P) X.layers.sc g X.layers.y.Lam

variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Public} {p : Par} {tk : Array Nat}

/-- **`Meets` holds of it**, at `publicOf`'s own record, whatever the table of scales. -/
theorem ref_meets [scl : Scl] (R : RefLetters M Xs) (hg : p.g < 12)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hc : covers X.layers = true) (nT nI : ℕ) :
    (refL R p.g hg nT nI).plan.Meets p (layerShape X.P) X.P.polCalls :=
  (refL R p.g hg nT nI).plan.meets_of_record rfl rfl h t hP hG hg0 hc

/-- **Nine equations and bounds on its letters**, where the section's table of scales is the one
laid here. -/
theorem ref_nine [scl : Scl] (hscl : scl = sclX X p.g) (R : RefLetters M Xs) (hg : p.g < 12)
    (h : publicOf pol KL lay = .ok X) (t : recordB X p.g = true)
    (hP : p.P = { X.layers with tokv := tk }) (hG : X.G[p.g]? = some p.hp)
    (hg0 : (p.g == 0) = false) (hc : covers X.layers = true) {QL : Plan4L GE M Xs}
    (hQ : QL = refL R p.g hg (nEndT X.layers.y)
      (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))) :
    QL.nT = nEndT p.P.y ∧
      QL.nI = 2 + (1 + p.P.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)) ∧
      (∀ q, QL.numT q = Cb.Pv.Lay.End.numA QL.D q) ∧
      QL.D.nNu + QL.D.ne + QL.D.ne * QL.D.nx ≤ QL.nT ∧ QL.slots.f7 ≤ QL.ns ∧
      QL.numI (Sum.inl (Sum.inl ())) = 0 ∧ QL.numI (Sum.inr (Sum.inl ())) = 2 + QL.D.ne ∧
      scl = sclOf (layerShape X.P) p.P.sc p.g p.P.y.Lam ∧ p.g * p.P.y.Lam = QL.L0 := by
  subst hQ
  have A := ref_meets R hg h t hP hG hg0 hc (nEndT X.layers.y)
    (2 + (1 + X.layers.y.LamM) + (p.hp.NCL - (if (p.g == 0) = true then 1 else 0)))
  have S7 := sevenSizes_of_meets A tk
  have L := laySizes_of_layout A.hy
  have eLam : p.P.y.Lam = 4 := by
    rw [L.Lam, ← A.Z.lL]
    rfl
  refine ⟨by rw [hP]; rfl, by rw [hP]; rfl, fun _ => rfl, ?_, (ref_room R p.g hg _ _).1, rfl, rfl,
    by rw [hscl, hP], by rw [eLam]; rfl⟩
  have e := S7.hEnd
  rw [hP] at e
  exact e

/-- **The shifts of queries and keys**, in every layer, under the table of scales laid here. -/
theorem ref_hk [scl : Scl] {g : ℕ} (hscl : scl = sclX X g) (h : publicOf pol KL lay = .ok X)
    (t : recordB X g = true) :
    ∀ l, (Dim.ref.Pl l).kq = (Dim.ref.Pl l).kk ∨
      (16 ≤ (Dim.ref.Pl l).kq ∧ 16 ≤ (Dim.ref.Pl l).kk) := by
  subst hscl
  obtain ⟨hy, _, _, _, _, _, tb⟩ := returns_of_record h t
  obtain ⟨S, _⟩ := bridgeB_parts tb
  have hsc := Hd.scalesHeld_of_public h
  rw [shape_of_public h] at hsc
  exact hk_of_scalesHeld (admitted_of_layout hy S.p3) hsc (bridgeB_more tb).1 Dim.ref

/-- **`MaskLetters` and room7 hold of it**, at every message, with the mask the value's own. -/
theorem ref_mask [scl : Scl] (R : RefLetters M Xs) (g : ℕ) (hg : g < 12) (nT nI : ℕ) (mm : M) :
    MaskLetters (refL R g hg nT nI) mm (R.maskAt mm) R.n0 nT nI ∧
      (refL R g hg nT nI).slots.f7 + 1 + (2 * (refL R g hg nT nI).plan.kW + 1) ≤
        (refL R g hg nT nI).ns :=
  ⟨{ n0 := rfl
     nT := rfl
     nI := rfl
     numI := rfl
     isM := fun _ _ => rfl
     room := (ref_room R g hg nT nI).1 },
    (ref_room R g hg nT nI).2⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ref_meets
#print axioms OnBytes.Road.K4.ref_nine
#print axioms OnBytes.Road.K4.ref_hk
#print axioms OnBytes.Road.K4.ref_mask
