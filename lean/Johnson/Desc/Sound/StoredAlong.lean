-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/StoredAlong.lean: "WHAT THE STORED TABLE DECODES TO": THE LIBRARY's DECODER WITH A RECORD (DecR, OnBytes/Slice/DecoderRec.lean), MADE OFF THE TYPED SHAPE, READ THROUGH THE CELLS, IS THE SHARED CHAIN's BLOCK 1's DECODER AT THE CORRESPONDING RECORD; AND SO ITS COLLISION. Two definitions, six theorems.
General in the shape: no size is written.

  decROfS S eM: the library's data of a decoder with a record, off the shape: the code, the number of row variables, the radius eM, the library's sample recZ at the shape's numbers, the cut before the pads.
  decROf_ix: its index IS ixLib (Johnson/Desc/Sound/SampleAlong.lean) at the library's own rank: rfl.
  numOf_rowNoS: the two numbers of a row (numOf, Johnson/Desc/K14/Law/Typed.lean; Sz.rowNo, OnBytes/Slice/LinkAt.lean) are one · tab_cells: THE TWO READINGS OF THE STORED STRING GIVE ONE TABLE OVER THE EXTENSION FIELD: the library's (a symbol's words; the position is not read; a missing word is 0) through the string made of the cells (tabBack: at a cell that shows nothing: the symbol (0, [])) and the
  typed side's (the cells' columns; at a cell that shows nothing: the empty column): AT EVERY FAMILY OF CELLS, SHOWN OR NOT: the two defaults are one.
  dcdR_cells | collR_cells: (decROfS …).dcd | coll through the cells at (ρ, y) are dcdAt | collAt at (trS ρ, y).
  dec_at_shape: SO THE BODY OF THE TOP STATEMENTS' DECODER (ConfigurationWithOutOfDomainSample.D, Hiop/RecConf.lean: "nothing at a collision at the record's seed; else dcd, through held") AT decROfS's coll | dcd, through the cells, IS decGuard collAt dcdAt held at (trS of the seed, the answers): THE CONDITION (DEC) of
  Johnson/Desc/Sound/ClaimCarried.lean for every configuration whose two fields are decROfS's.
WHAT STAYS OF (DEC): that the RELEASE's configuration is such a K: its decoder's data (at written sizes) are decROfS of the plan's shape at the plan's radius: an equation of closed terms AT THE FULL SIZE, under "the plan's shape is that one".

Limits. rank is the library's here (Fintype.equivFin's): the typed data's letter takes it. Nothing at a record whose factor is 0.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.Sound.SampleAlong
import Johnson.Desc.Sound.DecFields
import OnBytes.Slice.DecoderRec

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K14.Law
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain
open Cb Cb.Ood
open VerifiableInference.Desc.Sound (tabBack decGuard CellsOf dec_of_fields)

/-- The library's data of a decoder with a record, off the typed shape. -/
@[reducible] def decROfS (S : FoldeqShape) (eM : Nat) : DecR :=
  { T := codeOf S.index.code, v := S.index.v, eM := eM
    Z := recZ S.index.code.ell S.index.cubeBits S.index.answers, cut := S.index.plain }

/-- The library's rank. -/
noncomputable def rankLib (S : FoldeqShape) :
    ((Fin S.index.v → Bool) → Fin (S.index.code.r + S.index.code.ell) → GE) → Nat :=
  fun M => (Fintype.equivFin _ M).val

/-- Its index is the typed data with the library's sample, at the library's rank. -/
theorem decROf_ix (S : FoldeqShape) (eM : Nat) : (decROfS S eM).ix = ixLib S eM (rankLib S) := rfl

/-- The two numbers of a row (`numOf`, `Sz.rowNo`) are one. -/
theorem numOf_rowNoS : ∀ (k : Nat) (r : Fin k → Bool), numOf k r = Sz.rowNo r
  | 0, _ => by simp [numOf, Sz.rowNo]
  | k + 1, r => by
    have ih := numOf_rowNoS k (Fin.tail r)
    show (if r 0 then 1 else 0) + 2 * numOf k (Fin.tail r) =
      ∑ t : Fin (k + 1), if r t then 2 ^ t.val else 0
    rw [Fin.sum_univ_succ, ih]
    have e0 : (if r 0 = true then 2 ^ ((0 : Fin (k + 1)).val) else 0) = if r 0 = true then 1 else 0 := by
      simp
    rw [e0]
    refine congrArg (fun z => (if r 0 = true then 1 else 0) + z) ?_
    show 2 * (∑ t : Fin k, if Fin.tail r t then 2 ^ t.val else 0) =
      ∑ t : Fin k, if r t.succ then 2 ^ t.succ.val else 0
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    show 2 * (if r t.succ then 2 ^ t.val else 0) = if r t.succ then 2 ^ (t.val + 1) else 0
    by_cases h : r t.succ = true
    · rw [if_pos h, if_pos h, pow_succ, Nat.mul_comm]
    · rw [if_neg h, if_neg h, Nat.mul_zero]

/-- **The two readings of the stored string give one table over the extension field.** -/
theorem tab_cells (S : FoldeqShape) (eM : Nat) (c : CellsOf) :
    (decROfS S eM).tab (tabBack S.index.code.logN c) =
      tabF OnBytes.Model.Reading.gl S.index (colsOf c) := by
  funext r x
  show algebraMap GF GE (toF (((c x.val).getD (0, [])).2.getD (Sz.rowNo r) 0)) =
    OnBytes.Model.Reading.gl.val (ofF ((colsOf c x.val).toArray.getD (numOf S.index.v r) 0))
  rw [gl_ofF, numOf_rowNoS]
  have e : ((c x.val).getD (0, [])).2 = colsOf c x.val := by
    unfold colsOf
    cases c x.val <;> rfl
  rw [e]
  congr 2
  simp

/-- **The library's decoder with a record, through the cells, is block 1's at the corresponding record.** -/
theorem dcdR_cells (p : Par) (err eM : Nat) (c : CellsOf) (r : (decROfS p.S.fold eM).Rec) :
    (decROfS p.S.fold eM).dcd (tabBack p.S.fold.index.code.logN c) r =
      dcdAt p err eM (rankLib p.S.fold) c (trS p.S.fold.index err r.1, r.2) := by
  unfold DecR.dcd
  rw [tab_cells]
  exact (dcd_lib p err eM (rankLib p.S.fold) c r.1 r.2).symm

/-- **And its collision.** -/
theorem collR_cells (p : Par) (err eM : Nat) (c : CellsOf) (r : (decROfS p.S.fold eM).Rec) :
    (decROfS p.S.fold eM).coll (tabBack p.S.fold.index.code.logN c) r.1 ↔
      collAt p err eM (rankLib p.S.fold) c (trS p.S.fold.index err r.1, r.2) := by
  unfold DecR.coll
  rw [tab_cells]
  exact (coll_lib p err eM (rankLib p.S.fold) c r.1 r.2).symm

open Classical in
/-- **The body of the top statements' decoder, at decROfS's fields, through the cells, is the guarded decoder at the corresponding record.** -/
theorem dec_at_shape {Cells : Type} (p : Par) (err eM : Nat)
    (held : ((ixOf2 p.S.fold err eM (rankLib p.S.fold)).Row × Fin p.S.fold.index.code.ell → GE) → Option Cells)
    (c : CellsOf) (r : (decROfS p.S.fold eM).Rec) :
    (if (decROfS p.S.fold eM).coll (tabBack p.S.fold.index.code.logN c) r.1 then none
      else ((decROfS p.S.fold eM).dcd (tabBack p.S.fold.index.code.logN c) r).bind held) =
      decGuard (collAt p err eM (rankLib p.S.fold)) (dcdAt p err eM (rankLib p.S.fold)) held c
        (trS p.S.fold.index err r.1, r.2) := by
  unfold decGuard
  by_cases h : collAt p err eM (rankLib p.S.fold) c (trS p.S.fold.index err r.1, r.2)
  · rw [if_pos h, if_pos ((collR_cells p err eM c r).2 h)]
  · rw [if_neg h, if_neg fun h' => h ((collR_cells p err eM c r).1 h'), dcdR_cells p err eM c r]
    rfl

end Desc.K14.Law

#print axioms Desc.K14.Law.dec_at_shape
#print axioms Desc.K14.Law.decROf_ix
#print axioms Desc.K14.Law.numOf_rowNoS
#print axioms Desc.K14.Law.tab_cells
#print axioms Desc.K14.Law.dcdR_cells
#print axioms Desc.K14.Law.collR_cells
