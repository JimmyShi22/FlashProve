-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/PadsDoorLaw.lean: acceptance by the light test padsDoor
(Johnson/Desc/Kinds/PadsDoor.lean, no Mathlib), at plain arguments read off the large ones, implies
the public condition PadsFree (Johnson/P5J/WordsAtQ.lean) at the positions that the request's layout
gives. Theorems.

What is proved.
  copies_eq       the cheap test's part copiesMiss (Law/PadFreeByBlocks.lean) equals the light
          test's.
  padFree_imp     acceptance by the light test at a pair implies the cheap test's there. (The light
          test checks more: that an oracle message has the number in both segments.)
  padsFreeC_door  acceptance by padsDoor at cs, layout, Meaning.labAt X, num, arr, N.group, plainOf
          ms, (matIx X.y).iXI, the attention segments' NAs and X.hS.NHf implies padsFreeC cs arr ms
          N X layout num = true, for all arguments.
  padsFree_of_door   under Meaning.laidThere X s layout = true: acceptance by padsDoor there implies
          PadsFree cs arr ms N s (seatBy (fLay layout num) X s) X.

No existential quantifier in these statements.
Not proved here. Meaning.laidThere. The converse. The full size only. Nothing on soundness.

-/
import Johnson.Desc.Kinds.Law.PadFreeByBlocks
import Johnson.Desc.Kinds.Law.PlanK6View
import Johnson.Desc.Kinds.PadsDoor

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.Kinds.Head.Law.OffPad

open OnBytes OnBytes.Road
open OnBytes.Model.Layer (matIx)
open OnBytes.Params (ReqArray ReqLayout)
open Cb.Pv.Tail (Size)
open VerifiableInference.Desc renaming arrayOf → arrayOfD
open VerifiableInference.Desc.First (Numbers)
open VerifiableInference.Desc.Sound (Mem seatOf numOf)
open P5J (PadsFree)

variable (cs : OnBytes.Codes) (arr : ℕ → ℕ → ℕ) (ms : List Mem) (N : Numbers)

theorem copies_eq (k n : ℕ) (A : ReqArray) :
    copiesMiss cs arr ms N k n A = copiesMissP cs arr N.group (plainOf ms) k n A := by
  unfold copiesMiss copiesMissP plainOf
  rw [List.all_map]
  refine congrArg (fun f => ms.all f) (funext fun y => ?_)
  have e : Decidable.decide (seatOf y ∈ N.group k) = (N.group k).contains (seatOf y) :=
    (List.contains_eq_mem _ _).symm
  show (!(Decidable.decide (seatOf y ∈ N.group k) && Decidable.decide (numOf arr y = n)) || _) = _
  rw [e]
  rfl

variable (X : Model.Verify.Public) (layout : ReqLayout) (num : ℕ → ℕ → ℕ)

theorem padFree_imp {k k' a : ℕ}
    (h : padFreeP cs layout (Meaning.labAt X) num arr N.group (plainOf ms) k k' a = true) :
    padFreeC cs arr ms N X layout num k k' a = true := by
  unfold padFreeP at h
  unfold padFreeC
  rw [owner_eq] at h
  dsimp only at h
  cases hA : arrayOfD layout (Meaning.ownerK (Meaning.labAt X k a))
      (Meaning.nameOf (Meaning.ownerA (Meaning.labAt X k a))) with
  | none =>
    rw [hA] at h
    cases h
  | some A =>
    rw [hA] at h
    dsimp only at h ⊢
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    rw [copies_eq, copies_eq, Bool.and_eq_true]
    exact ⟨h.1.2, h.2⟩

/-- **Acceptance by the light test at plain arguments implies the cheap test's.** -/
theorem padsFreeC_door
    (h : padsDoor cs layout (Meaning.labAt X) num arr N.group (plainOf ms) (matIx X.y).iXI
      (fun g => (Hd.shapeA X g).cf.NAs) X.hS.NHf = true) :
    padsFreeC cs arr ms N X layout num = true := by
  unfold padsDoor at h
  unfold padsFreeC
  rw [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨fun g hg => ?_, padFree_imp cs arr ms N X layout num h.2⟩
  have k := h.1 g hg
  rw [Bool.and_eq_true, Bool.or_eq_true] at k ⊢
  exact ⟨k.1.imp id (padFree_imp cs arr ms N X layout num),
    padFree_imp cs arr ms N X layout num k.2⟩

/-- **Acceptance by the light test implies PadsFree.** -/
theorem padsFree_of_door (s : ℕ → Size) (T : Meaning.laidThere X s layout = true)
    (h : padsDoor cs layout (Meaning.labAt X) num arr N.group (plainOf ms) (matIx X.y).iXI
      (fun g => (Hd.shapeA X g).cf.NAs) X.hS.NHf = true) :
    PadsFree cs arr ms N s (Meaning.seatBy (Meaning.fLay layout num) X s) X :=
  padsFree_of_C cs arr ms N X s layout num T (padsFreeC_door cs arr ms N X layout num h)

end VerifiableInference.Desc.Kinds.Head.Law.OffPad

#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFreeC_door
#print axioms VerifiableInference.Desc.Kinds.Head.Law.OffPad.padsFree_of_door
