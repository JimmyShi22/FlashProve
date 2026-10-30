-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/PlanValues/ProofShapeAtPlain.lean: Johnson/Goal/PlanValues/ProofShapeAtScope.lean's
statement AT THE PROOF FILE's OWN PLANNER (ProofFile.Plain.planned, Johnson/Desc/ProofFile/PlanPlain.lean)
AND AT ITS PUBLIC PART (ProofFile.pubPlain), AT EVERY o: at public files in the goals' scope the shape of
a proof file's test on the committed table passes fullShapeB. STATED AND PROVED.
  shapesWith_subP · plainShapesOf_sub · plainChainsOf_parts: the planner's text taken apart, step by
      step, as OnBytes/Model/Fit/PlannedParts.lean does for the library's (whose first lemma is
      private, so it is typed again).
  fullShape_plain: from ProofFile.Plain.planned o's yes. fullShape_pub: from ProofFile.pubPlain o's yes, at
      Zp.p.
On what it rests. The sizing reads no hash: batch_of_public (StageSizesAtScope.lean) asks of the
public parameters four facts (PubFull), which pubFull_of_layout gives from two steps of their text;
publicSteps_of_O (PublicAtSteps.lean) hands these two steps at every o.
Limits. One direction: from a planner that returns: at no o is ProofFile.Plain.planned shown to return at
files in scope (runs say it of the stored full-size set at the second hash function). Nothing on
soundness.

-/
import Johnson.Goal.PlanValues.ProofShapeAtScope
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lk6.AtPlan
open OnBytes OnBytes.Model OnBytes.Model.Verify
open Fo.BatRows (bindE_ok)
open Fo.Pub (ite_unit_ok)
open H2K.Sizes
open Desc.K14.Law (fullShapeB)
open VerifiableInference.PlanWritten (publicSteps_of_O)

/-- The sub-proofs' structure in the shapes. -/
theorem shapesWith_subP {X : Public} {links : List Params.ReqLink} {layout : Params.ReqLayout}
    {ids : List Nat} {s : Params.Shapes} (h : shapesWith X links layout ids = .ok s) :
    s.sub = subproofsWith X links := by
  unfold shapesWith at h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  rfl

/-- The same from the plain planner's shapesOf. -/
theorem plainShapesOf_sub {X : Public} {lay : Option ByteArray} {links : Array Stages.LinkH}
    {shapes : Params.Shapes} (h : ProofFile.Plain.shapesOf X lay = .ok (links, shapes)) :
    ∃ rl, shapes.sub = subproofsWith X rl := by
  unfold ProofFile.Plain.shapesOf at h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨⟨links', declared⟩, _, h⟩ := bindE_ok h
  dsimp only at h
  split at h
  · obtain ⟨file, _, h⟩ := bindE_ok h
    split at h
    · obtain ⟨⟨reqLinks, layout⟩, _, h⟩ := bindE_ok h
      dsimp only at h
      obtain ⟨s, hs, h⟩ := bindE_ok h
      have e : (links', s) = (links, shapes) := Except.ok.inj h
      rw [← (Prod.mk.inj e).2]
      exact ⟨reqLinks, shapesWith_subP hs⟩
    · obtain ⟨_, e, _⟩ := bindE_ok h
      cases e
  · obtain ⟨_, e, _⟩ := bindE_ok h
    cases e

/-- From the plain planner's chainsOf's yes. -/
theorem plainChainsOf_parts {X : Public} {lay : Option ByteArray} {c : ByteArray} {ch : Chains}
    (h : ProofFile.Plain.chainsOf X lay c = .ok ch) :
    ∃ links shapes, ProofFile.Plain.shapesOf X lay = .ok (links, shapes) ∧
      Params.configure X.P.frame shapes c 0 = .ok ch.made := by
  unfold ProofFile.Plain.chainsOf at h
  obtain ⟨⟨links, shapes⟩, hs, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨z, _, h⟩ := bindE_ok h
  obtain ⟨u, _, h⟩ := bindE_ok h
  obtain ⟨made, hm, h⟩ := bindE_ok h
  split at h
  · cases h
    exact ⟨links, shapes, hs, hm⟩
  · cases h

/-- **fullShapeB at the proof file's own planner, in the goals' scope, at every o.** -/
theorem fullShape_plain {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true)
    {o : Nat → ByteArray → ByteArray} {p : Planned}
    (hp : ProofFile.Plain.planned o Z.pol Z.KL (some Z.lay) = .ok p) :
    fullShapeB p.chains.made.sized.proof.batch.shape = true := by
  unfold ProofFile.Plain.planned at hp
  obtain ⟨X, hX, hp⟩ := bindE_ok hp
  dsimp only at hp
  obtain ⟨ch, hc, hp⟩ := bindE_ok hp
  obtain ⟨b, _, hp⟩ := bindE_ok hp
  cases hp
  obtain ⟨links, shapes, hs, hm⟩ := plainChainsOf_parts hc
  obtain ⟨rl, he⟩ := plainShapesOf_sub hs
  have S := publicSteps_of_O hX
  obtain ⟨codes1, h⟩ := batch_of_public (pubFull_of_layout hZ S.layout S.wsLay) hm he
  exact shape_full h

/-- **The same at the proof file's public part.** -/
theorem fullShape_pub {Z : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Z = true) {o : ProofFile.SecondHashFunctionArgument}
    {Zp : ProofFile.Pub} (h : ProofFile.pubPlain o Z.pol Z.lay Z.KL = .ok Zp) :
    fullShapeB Zp.p.chains.made.sized.proof.batch.shape = true :=
  fullShape_plain hZ (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
          (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts Z.pol Z.lay Z.KL = .ok Zp from h)))

end Lk6.AtPlan

#print axioms Lk6.AtPlan.fullShape_plain
#print axioms Lk6.AtPlan.fullShape_pub
