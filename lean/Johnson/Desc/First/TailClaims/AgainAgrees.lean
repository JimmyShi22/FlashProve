-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/First/TailClaims/AgainAgrees.lean: THEOREMS: each definition of
Johnson/Desc/First/TailClaims/Again.lean IS `verify-on-bytes`'s function of which it is a copy: an
equation of functions, so at all arguments. No block imports this file. With these equations a law
that is proved of the program's functions carries over to the copies by rewriting.
Nothing on soundness.

-/
import Johnson.Desc.First.TailClaims.Again

set_option autoImplicit false
set_option relaxedAutoImplicit false
-- the lists of simp lemmas are made by program, each with all the equations in front of it
set_option linter.unusedSimpArgs false

namespace VerifiableInference.Desc.First.TailClaims
open OnBytes OnBytes.Model OnBytes.Model.HTailF2

theorem allFrom_eq : allFrom = OnBytes.Model.allFrom := by
  funext p c i
  induction c generalizing i with
  | zero => rfl
  | succ n ih => simp only [allFrom, OnBytes.Model.allFrom, ih]

theorem allBelow_eq : allBelow = OnBytes.Model.allBelow := by
  funext n p
  simp only [allBelow, OnBytes.Model.allBelow, allFrom_eq]

theorem EqRun.allLoop_eq : EqRun.allLoop = OnBytes.Model.EqRun.allLoop := by
  funext test c i r
  induction c generalizing i r with
  | zero => rfl
  | succ n ih => simp only [EqRun.allLoop, OnBytes.Model.EqRun.allLoop, ih]

theorem EqRun.all_eq : EqRun.all = OnBytes.Model.EqRun.all := by
  funext z first count test
  simp only [EqRun.all, OnBytes.Model.EqRun.all, EqRun.allLoop_eq]

theorem meets_eq : meets = HTailF2.Want.meets := rfl

theorem noneMeet_eq : noneMeet = HTailF2.noneMeet := by
  funext l
  induction l with
  | nil => rfl
  | cons w t ih => simp only [noneMeet, HTailF2.noneMeet, ih, meets_eq]

theorem neighboursDiffer_eq : neighboursDiffer = HTailF2.neighboursDiffer := by
  funext l
  induction l with
  | nil => rfl
  | cons a t ih =>
    cases t with
    | nil => rfl
    | cons b t' => simp only [neighboursDiffer, HTailF2.neighboursDiffer, ih]

theorem noneZero_eq : noneZero = OnBytes.Model.noneZero := by
  funext x0 x1 x2
  simp only [noneZero, OnBytes.Model.noneZero, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq]

theorem isPow2_eq : isPow2 = HTailF2.isPow2 := by
  funext x0
  simp only [isPow2, HTailF2.isPow2, allFrom_eq, allBelow_eq, EqRun.allLoop_eq, EqRun.all_eq,
    meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq]

theorem wants_eq : wants = HTailF2.wants := by
  funext x0
  simp only [wants, HTailF2.wants, allFrom_eq, allBelow_eq, EqRun.allLoop_eq, EqRun.all_eq,
    meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq]

theorem forestHeld_eq : forestHeld = HTailF2.forestHeld := by
  funext x0 x1
  simp only [forestHeld, HTailF2.forestHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq]

theorem pieceHeld_eq : pieceHeld = HTailF2.pieceHeld := by
  funext x0 x1
  simp only [pieceHeld, HTailF2.pieceHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq]

theorem callHeld_eq : callHeld = HTailF2.callHeld := by
  funext x0 x1 x2 x3
  simp only [callHeld, HTailF2.callHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq, EqRun.all_eq,
    meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq, forestHeld_eq,
    pieceHeld_eq]

theorem piecesTile_eq : piecesTile = HTailF2.piecesTile := by
  funext x0 x1 x2
  simp only [piecesTile, HTailF2.piecesTile, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq]

theorem pointsHeld_eq : pointsHeld = HTailF2.pointsHeld := by
  funext x0 x1
  simp only [pointsHeld, HTailF2.pointsHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq]

theorem pieceWeightsHeld_eq : pieceWeightsHeld = HTailF2.pieceWeightsHeld := by
  funext x0 x1 x2 x3 x4
  simp only [pieceWeightsHeld, HTailF2.pieceWeightsHeld, allFrom_eq, allBelow_eq,
    EqRun.allLoop_eq, EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq,
    isPow2_eq, wants_eq, forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq]

theorem leE_eq : leE = HTailF2.leE := by
  funext x0 x1
  simp only [leE, HTailF2.leE, allFrom_eq, allBelow_eq, EqRun.allLoop_eq, EqRun.all_eq, meets_eq,
    noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq, forestHeld_eq,
    pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq, pieceWeightsHeld_eq]

theorem tieShapeHeld_eq : tieShapeHeld = HTailF2.tieShapeHeld := by
  funext x0 x1 x2
  simp only [tieShapeHeld, HTailF2.tieShapeHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq, pieceWeightsHeld_eq,
    leE_eq]

theorem tieWeightsHeld_eq : tieWeightsHeld = HTailF2.tieWeightsHeld := by
  funext x0 x1 x2 x3
  simp only [tieWeightsHeld, HTailF2.tieWeightsHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq, pieceWeightsHeld_eq,
    leE_eq, tieShapeHeld_eq]

theorem planesShapeHeld_eq : planesShapeHeld = HTailF2.planesShapeHeld := by
  funext x0 x1 x2
  simp only [planesShapeHeld, HTailF2.planesShapeHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq, pieceWeightsHeld_eq,
    leE_eq, tieShapeHeld_eq, tieWeightsHeld_eq]

theorem planesWeightsHeld_eq : planesWeightsHeld = HTailF2.planesWeightsHeld := by
  funext x0 x1 x2 x3
  simp only [planesWeightsHeld, HTailF2.planesWeightsHeld, allFrom_eq, allBelow_eq,
    EqRun.allLoop_eq, EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq,
    isPow2_eq, wants_eq, forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq,
    pieceWeightsHeld_eq, leE_eq, tieShapeHeld_eq, tieWeightsHeld_eq, planesShapeHeld_eq]

theorem readShapeHeld_eq : readShapeHeld = HTailF2.readShapeHeld := by
  funext x0 x1
  simp only [readShapeHeld, HTailF2.readShapeHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq, pieceWeightsHeld_eq,
    leE_eq, tieShapeHeld_eq, tieWeightsHeld_eq, planesShapeHeld_eq, planesWeightsHeld_eq]

theorem readWeightsHeld_eq : readWeightsHeld = HTailF2.readWeightsHeld := by
  funext x0 x1 x2
  simp only [readWeightsHeld, HTailF2.readWeightsHeld, allFrom_eq, allBelow_eq, EqRun.allLoop_eq,
    EqRun.all_eq, meets_eq, noneMeet_eq, neighboursDiffer_eq, noneZero_eq, isPow2_eq, wants_eq,
    forestHeld_eq, pieceHeld_eq, callHeld_eq, piecesTile_eq, pointsHeld_eq, pieceWeightsHeld_eq,
    leE_eq, tieShapeHeld_eq, tieWeightsHeld_eq, planesShapeHeld_eq, planesWeightsHeld_eq,
    readShapeHeld_eq]

end VerifiableInference.Desc.First.TailClaims

#print axioms VerifiableInference.Desc.First.TailClaims.allFrom_eq
#print axioms VerifiableInference.Desc.First.TailClaims.allBelow_eq
#print axioms VerifiableInference.Desc.First.TailClaims.EqRun.allLoop_eq
#print axioms VerifiableInference.Desc.First.TailClaims.EqRun.all_eq
#print axioms VerifiableInference.Desc.First.TailClaims.meets_eq
#print axioms VerifiableInference.Desc.First.TailClaims.noneMeet_eq
#print axioms VerifiableInference.Desc.First.TailClaims.neighboursDiffer_eq
#print axioms VerifiableInference.Desc.First.TailClaims.noneZero_eq
#print axioms VerifiableInference.Desc.First.TailClaims.isPow2_eq
#print axioms VerifiableInference.Desc.First.TailClaims.wants_eq
#print axioms VerifiableInference.Desc.First.TailClaims.forestHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.pieceHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.callHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.piecesTile_eq
#print axioms VerifiableInference.Desc.First.TailClaims.pointsHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.pieceWeightsHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.leE_eq
#print axioms VerifiableInference.Desc.First.TailClaims.tieShapeHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.tieWeightsHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.planesShapeHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.planesWeightsHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.readShapeHeld_eq
#print axioms VerifiableInference.Desc.First.TailClaims.readWeightsHeld_eq
