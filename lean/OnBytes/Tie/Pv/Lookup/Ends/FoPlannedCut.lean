-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoPlannedCut.lean.
What follows from the three configuration files, cut into its steps: the shapes, the planner's yes,
and the plan of a proof's first chain.

The verifier computes all that follows from the three configuration files by the routine planned
(OnBytes/Model/Verify.lean): the public part X, the digest of the files, and the seven chains
(chainsOf, OnBytes/Model/VerifyChains.lean). chainsOf takes what the sub-proofs' plans hand to the
planner from shapesOf, which ends in a call of shapesWith, and then calls the planner's configure on
the parameter file's lines X.P.frame, these shapes, the digest and 0 bits. This file cuts a run of
each routine that returns into these steps, and keeps each step's equation.

* planned_cut: a run of planned: publicOf's equation, the digest, chainsOf's equation.
* ShapesCut X lf links x reqLinks lay: the steps of a run of shapesOf, as one chain of five
  equations from X and the layout file, which ends in shapesWith's. ShapesCut.shapes: that last
  equation.
* shapesOf_cut: a run of shapesOf that returns has such a chain.
* chainsOf_cut: a run of chainsOf: shapesOf's equation, configure's, and the equation of the reader
  of the proof's three chains. (chainsOf_made, OnBytes/Model/VerifyDerives.lean, keeps configure's
  alone, at some shapes.)
* planned_plan: from a run of planned: shapesOf's equation, its chain ShapesCut, and configure's
  equation at the run's own X, lines, shapes and digest; the three plans of a proof; that the first
  is the list of OnBytes/Plan/PlanListsReq.lean with the model's sub-proofs' lists between
  (configure_proof_model, OnBytes/Model/LinkRoundsList.lean); and the reader's equation. Dropped:
  the yes of the tests between the steps (headLast, linksCount, sized, linksFit), the readers of the
  key's chains and of the entry's chain, builtOf, and the equation of linSizeOf and the lists of the
  second and the third plan, which configure_proof_model has.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Model.Verify
import OnBytes.Model.LinkRoundsList

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.Model.Verify OnBytes.Model.Stages OnBytes.Params

/-- A run of planned. -/
theorem planned_cut {pol KL : ByteArray} {layout : Option ByteArray} {p : Verify.Planned}
    (h : planned pol KL layout = .ok p) :
    publicOf pol KL layout = .ok p.X ∧ p.cfg = configuration pol (layout.getD .empty) KL ∧
      chainsOf p.X layout p.cfg = .ok p.chains := by
  unfold planned at h
  obtain ⟨X, hX, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨chains, hc, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  cases h
  exact ⟨hX, rfl, hc⟩

/-- The steps of a run of shapesOf, as one chain of five equations from X and the layout file: the
links; the links with their declared arrays; the layout file as read; the frame's links and layout;
the shapes. -/
def ShapesCut (X : Public) (lf : Option ByteArray) (links : Array LinkH) (x : Shapes)
    (reqLinks : List ReqLink) (lay : ReqLayout) : Prop :=
  ∃ links0 declared file, linksOf X default = .ok links0 ∧
    declareLinks links0 X.NGr X.p4 = .ok (links, declared) ∧
    lf.bind Plan.layoutRead = some file ∧
    Plan.reqFrame declared file X.P.frame.answers = some (reqLinks, lay) ∧
    shapesWith X reqLinks lay (links.toList.map (·.gid)) = .ok x

/-- The chain's last equation. -/
theorem ShapesCut.shapes {X : Public} {lf : Option ByteArray} {links : Array LinkH} {x : Shapes}
    {reqLinks : List ReqLink} {lay : ReqLayout} (h : ShapesCut X lf links x reqLinks lay) :
    shapesWith X reqLinks lay (links.toList.map (·.gid)) = .ok x := by
  obtain ⟨_, _, _, _, _, _, _, h5⟩ := h
  exact h5

/-- A run of shapesOf, as one chain of equations. -/
theorem shapesOf_cut {X : Public} {lf : Option ByteArray} {links : Array LinkH} {x : Shapes}
    (h : shapesOf X lf = .ok (links, x)) : ∃ reqLinks lay, ShapesCut X lf links x reqLinks lay := by
  unfold shapesOf at h
  obtain ⟨links0, h0, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨⟨links1, declared⟩, h1, h⟩ := exc_bind h
  dsimp only at h
  cases hf : lf.bind Plan.layoutRead with
  | none =>
    rw [hf] at h
    cases h
  | some file =>
    rw [hf] at h
    dsimp only at h
    obtain ⟨file', e1, h⟩ := exc_bind h
    obtain rfl : file = file' := Except.ok.inj e1
    cases hr : Plan.reqFrame declared file X.P.frame.answers with
    | none =>
      rw [hr] at h
      cases h
    | some y =>
      rw [hr] at h
      dsimp only at h
      obtain ⟨y', e2, h⟩ := exc_bind h
      obtain rfl : y = y' := Except.ok.inj e2
      obtain ⟨x', h4, h⟩ := exc_bind h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
      exact ⟨y.1, y.2, links0, declared, file, h0, h1, hf, hr, h4⟩

/-- A run of chainsOf. It keeps the shapes' own equation. -/
theorem chainsOf_cut {X : Public} {lf : Option ByteArray} {cfg : ByteArray} {c : Chains}
    (h : chainsOf X lf cfg = .ok c) :
    ∃ links x, shapesOf X lf = .ok (links, x) ∧ configure X.P.frame x cfg 0 = .ok c.made ∧
      ProofChains.read c.made.first c.made.shared c.made.second = some c.proof := by
  unfold chainsOf at h
  obtain ⟨⟨links, x⟩, hs, h⟩ := exc_bind h
  dsimp only at h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨_, _, h⟩ := exc_bind h
  obtain ⟨made, hm, h⟩ := exc_bind h
  split at h
  · rename_i key link proof _ _ hp
    cases h
    exact ⟨links, x, hs, hm, hp⟩
  · cases h

/-- From a run of planned: the planner's yes at the run's own shapes, and the first chain's plan. -/
theorem planned_plan {pol KL : ByteArray} {layout : Option ByteArray} {p : Verify.Planned}
    (h : planned pol KL layout = .ok p) :
    ∃ links x reqLinks lay F S2 S3, shapesOf p.X layout = .ok (links, x) ∧
      ShapesCut p.X layout links x reqLinks lay ∧
      configure p.X.P.frame x p.cfg 0 = .ok p.chains.made ∧
      p.chains.made.proof = [F, S2, S3] ∧
      PlanIs F (settingOf p.X.P.frame) .request
        (Plan.firstChainList p.chains.made.sized.proof x.sub
          (linkList (settingOf p.X.P.frame) .request p.X) []) ∧
      ProofChains.read p.chains.made.first p.chains.made.shared p.chains.made.second =
        some p.chains.proof := by
  obtain ⟨_, _, hc⟩ := planned_cut h
  obtain ⟨links, x, hs, hm, hr⟩ := chainsOf_cut hc
  obtain ⟨reqLinks, lay, hx⟩ := shapesOf_cut hs
  obtain ⟨F, S2, S3, _, hp, _, p1, _, _⟩ := configure_proof_model hx.shapes hm
  exact ⟨links, x, reqLinks, lay, F, S2, S3, hs, hx, hm, hp, p1, hr⟩

end Fo
