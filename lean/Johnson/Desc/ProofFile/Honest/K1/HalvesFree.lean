-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/ProofFile/Honest/K1/HalvesFree.lean: THE SHARED "SENDING" (the kind K1): THE LOT's
HALVES, AND ITS HONEST SIDE, ARE ONE VALUE WHATEVER NUMBERS ARE LAID INTO THE LETTER no (the number
that a place's first new oracle message gets). Nine theorems; no definition. A file of laws alone.
It goes on from Honest/K1/FirstFree.lean.

Main names (namespace ProofFile.Honest.K1).
  placeHalf_any_first, placeHalf_job   the half at a place, of a job with another number laid into
      "first", is the job's own; so placeJob at two numbers gives one half.
  lotHalves_any_no   lotHalves wit no D Z G = lotHalves wit no' D Z G.
  lotSide_any_no, dataSide_any_no, dataSideBy_any_no, dataSideOn_any   THE WHOLE SIDE: at two
      families of numbers it is one value; the side over a list of blocks is the side at any
      numbers.
  wHalves_any_no, wSide_any_no   the like at W's place (Honest/K1/PlaceW.lean).

Limits. No law here has a premise. WHAT THESE LAWS GIVE: THE HALVES AND THE SIDES ARE ONE VALUE AT
ALL NUMBERS. The texts still name the letter; the public tests on the numbers (firstNoFits,
noFitsOn, lotTestOn) and the laws of Honest/K1/FirstNoLaw.lean speak of the numbers themselves.
Whether another text than these reads a job's "first" is not followed here. No answer is named. OF
THE FOLDER Johnson/Goal/ IT CALLS NOTHING AND IMPORTS NOTHING. Nothing on any property.

Terms: lean/GLOSSARY.md.
-/
import Johnson.Desc.ProofFile.Honest.K1.FirstFree
import Johnson.Desc.ProofFile.Honest.K1.LotNo
import Johnson.Desc.ProofFile.Honest.K1.PlaceW

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ProofFile.Honest.K1
open OnBytes VerifiableInference.Desc

variable {V W X Xi St Cl : Type}

/-- The half at a place, of a job with another number laid into "first", is the job's own. -/
theorem placeHalf_any_first (wit : W → PlaceIn Xi) (J : SendJob (PlaceIn Xi) X) (f : ℕ) :
    placeHalf (V := V) wit { J with first := f } = placeHalf wit J := by
  unfold placeHalf
  rw [sendPart_any_first]

/-- placeJob at two numbers gives one half. -/
theorem placeHalf_job (wit : W → PlaceIn Xi) (P : K1.Par) (f f' : ℕ)
    (fold : Option (ℕ × FoldShape)) (D : RowDataOf Xi) (part : ℕ) :
    placeHalf (V := V) (X := X) wit (placeJob P f fold D part) =
      placeHalf wit (placeJob P f' fold D part) :=
  placeHalf_any_first wit (placeJob P f' fold D part) f

/-- **THE LOT's HALVES ARE ONE VALUE WHATEVER NUMBERS ARE LAID IN.** -/
theorem lotHalves_any_no (wit : W → PlaceIn Xi) (no no' : Place → ℕ)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    lotHalves (V := V) (X := X) wit no D Z G = lotHalves wit no' D Z G := by
  unfold lotHalves
  rw [placeHalf_job wit _ (no _) (no' ⟨1, some 0, 1, .K1⟩)]
  refine congrArg (List.cons _) (List.flatMap_congr ?_)
  rintro ⟨Y, l⟩ _
  cases h : K1.linkNumbers G Y with
  | none => simp only [h]
  | some t =>
    obtain ⟨pr, pd, a, b⟩ := t
    simp only [h, laterJobAt]
    rw [placeHalf_job wit _ (no _) (no' ⟨1, some l, pr, .K1⟩),
      placeHalf_job wit _ (no _) (no' ⟨1, some l, pd, .K1⟩)]

/-- **The whole side.** -/
theorem lotSide_any_no (wit : W → PlaceIn Xi) (no no' : Place → ℕ)
    (D : Pub → Ground → RowDataOf Xi) :
    lotSide (V := V) (X := X) wit no D = lotSide wit no' D := by
  have e : lotHalves (V := V) (X := X) wit no D = lotHalves wit no' D :=
    funext fun Z => funext fun G => lotHalves_any_no wit no no' D Z G
  unfold lotSide
  rw [e]

theorem dataSide_any_no (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (no no' : Place → ℕ) : dataSide (V := V) (X := X) S wit no = dataSide S wit no' :=
  lotSide_any_no wit no no' (lotData S)

theorem dataSideBy_any_no (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (no no' : Pub → Ground → Place → ℕ) :
    dataSideBy (V := V) (X := X) S wit no = dataSideBy S wit no' := by
  have e : (fun Z G => lotHalves (V := V) (X := X) wit (no Z G) (lotData S) Z G) =
      fun Z G => lotHalves wit (no' Z G) (lotData S) Z G :=
    funext fun Z => funext fun G => lotHalves_any_no wit (no Z G) (no' Z G) (lotData S) Z G
  unfold dataSideBy
  rw [e]

/-- The side over a list of blocks is the side at any numbers. -/
theorem dataSideOn_any (S : OnBytes.HonestTrace.Sz) (wit : W → PlaceIn ProofFile.Inst)
    (bs : Pub → Ground → List (Block St Cl)) (no : Pub → Ground → Place → ℕ) :
    dataSideOn (V := V) (X := X) S wit bs = dataSideBy S wit no :=
  dataSideBy_any_no S wit _ no

/-- The like at W's place. -/
theorem wHalves_any_no (wit : W → PlaceIn Xi) (no no' : Place → ℕ)
    (D : Pub → Ground → RowDataOf Xi) (Z : Pub) (G : Ground) :
    wHalves (V := V) (X := X) wit no D Z G = wHalves wit no' D Z G := by
  unfold wHalves wJobAt
  exact congrArg (fun f => ((linMessageW Z.first.lin).map f).toList)
    (funext fun _ => placeHalf_job wit _ _ _ _ _ _)

theorem wSide_any_no (wit : W → PlaceIn Xi) (no no' : Place → ℕ)
    (D : Pub → Ground → RowDataOf Xi) :
    wSide (V := V) (X := X) wit no D = wSide wit no' D := by
  have e : wHalves (V := V) (X := X) wit no D = wHalves wit no' D :=
    funext fun Z => funext fun G => wHalves_any_no wit no no' D Z G
  unfold wSide
  rw [e]

end ProofFile.Honest.K1

#print axioms ProofFile.Honest.K1.placeHalf_any_first
#print axioms ProofFile.Honest.K1.placeHalf_job
#print axioms ProofFile.Honest.K1.lotHalves_any_no
#print axioms ProofFile.Honest.K1.lotSide_any_no
#print axioms ProofFile.Honest.K1.dataSide_any_no
#print axioms ProofFile.Honest.K1.dataSideBy_any_no
#print axioms ProofFile.Honest.K1.dataSideOn_any
#print axioms ProofFile.Honest.K1.wHalves_any_no
#print axioms ProofFile.Honest.K1.wSide_any_no
