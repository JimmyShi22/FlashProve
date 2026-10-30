-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
import Johnson.Desc.ProofFile.PlanPlain
import OnBytes.Tie.Pv.Lookup.Ends.FoPlannedCut
import OnBytes.Tie.Pv.Lookup.Ends.BatRows
/-
Johnson/Loose/H2K12/PlainPartsCut.lean: A RUN OF THE PLAIN ROAD's shapesOf AS ONE CHAIN OF FIVE
EQUATIONS: Fo.shapesOf_cut's statement and proof (OnBytes/Tie/Pv/Lookup/Ends/FoPlannedCut.lean)
at the twin's name (Johnson/Desc/ProofFile/PlanPlain.lean:
ProofFile.Plain.shapesOf), with ProofFile.Plain.linksPlain X in «linksOf X default»'s place. For whoever needs,
beside PlainParts.lean's plain_parts, that the file of reqFrame IS the layout file as read,
and shapesWith's own yes. ON THE PLAN ALONE. NO SOUNDNESS
IS CLAIMED. NOTHING ON HIDING. A TWIN OF A THEOREM FOR A TWIN OF A FUNCTION: it falls when the
library's six functions (PlanPlain.lean's head) take the links' maker as a parameter.
-/
set_option autoImplicit false
namespace H2K.Made
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params
open Fo.BatRows (bindE_ok)

/-- The steps of a run of the plain shapesOf: Fo.ShapesCut with the plain links. -/
def PlainShapesCut (X : Public) (lf : Option ByteArray) (links : Array LinkH) (x : Shapes)
    (reqLinks : List ReqLink) (lay : ReqLayout) : Prop :=
  ∃ links0 declared file, ProofFile.Plain.linksPlain X = .ok links0 ∧
    declareLinks links0 X.NGr X.p4 = .ok (links, declared) ∧
    lf.bind Plan.layoutRead = some file ∧
    Plan.reqFrame declared file X.P.frame.answers = some (reqLinks, lay) ∧
    shapesWith X reqLinks lay (links.toList.map (·.gid)) = .ok x

theorem plain_shapesOf_cut {X : Public} {lf : Option ByteArray} {links : Array LinkH} {x : Shapes}
    (h : ProofFile.Plain.shapesOf X lf = .ok (links, x)) :
    ∃ reqLinks lay, PlainShapesCut X lf links x reqLinks lay := by
  unfold ProofFile.Plain.shapesOf at h
  obtain ⟨links0, h0, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨⟨links1, declared⟩, h1, h⟩ := bindE_ok h
  dsimp only at h
  cases hf : lf.bind Plan.layoutRead with
  | none =>
    rw [hf] at h
    cases h
  | some file =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨file', e1, h⟩ := bindE_ok h
    obtain rfl : file = file' := Except.ok.inj e1
    cases hr : Plan.reqFrame declared file X.P.frame.answers with
    | none =>
      rw [hr] at h
      cases h
    | some y =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨y', e2, h⟩ := bindE_ok h
      obtain rfl : y = y' := Except.ok.inj e2
      obtain ⟨x', h4, h⟩ := bindE_ok h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact ⟨y.1, y.2, links0, declared, file, h0, h1, hf, hr, h4⟩

end H2K.Made

#print axioms H2K.Made.plain_shapesOf_cut
