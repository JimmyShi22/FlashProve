-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Kinds/Law/HeadPlanMs.lean: In the record of the smallness test of the output head's
plan, as Head.planH2 (OnBytes/Model/HeadPlan.lean) returns it and as Verify.publicOf hands it on
(X.H.tl), each matrix's shape has a third of its rows of cells, rounded up, as its rows of symbols.
Wanted by other files, for their list of conditions in front of the batching. Statements and proofs;
nothing is evaluated.

Main names (namespace VerifiableInference.Desc.Kinds.Head.Law.InScope).
  ownerHeld_shp: the comparison with the plan of the last group of layers keeps the number of
      matrices, the shapes and the matrices.
  planH2_mS: the equation in every record that planH2 returns.
  public_H_mS: the statement: the same at X.H.tl, where Verify.publicOf pol KL layout = .ok X. No
      scope.

By calls of addTrees_mS (Johnson/Road/K4/Plan/ShapeRows.lean: the equation behind
the routine that lays a sub-proof's arrays), SameShp, borderMeans_shp and mS_of_same
(Johnson/Road/K4/Plan/ShapeRowsG.lean), K6's files' one opening of the planner, planH2_parts
(Law/HeadPlanWritten.lean), and the library's Fo.Pub.public_H
(OnBytes/Tie/Pv/Lookup/Ends/FoPublic.lean). The walk of ownerHeld's text is that of
OnBytes.Road.Hd.ownerHeld_keeps (Johnson/Road/HeadReads.lean).
What it does not say. That the planner or publicOf returns anywhere. Under the library's publicOf
alone: at publicOfO o nothing is said here. Where a matrix's array bears no shape the equation holds
idly (Johnson/Road/K4/Plan/ShapeRows.lean's own limit). Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Road.K4.Plan.ShapeRowsG

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.Kinds.Head.Law.InScope

open OnBytes.Model (HTailF2 Settings Fork Tail2)
open OnBytes.Model.Head (Shape HL Border Owner HPlanH2 planH2 ownerHeld)
open OnBytes.Road (ok_of_bind)
open OnBytes.Road.K4.Plan (SameShp borderMeans_shp mS_of_same addTrees_mS)

/-- The comparison with the plan of the last group of layers turns the record of the foreign
array's place alone. -/
theorem ownerHeld_shp {O : Owner} {NGr : ℕ} {tl tl' : HTailF2} {Fp : Fork} {Tp : Tail2}
    (h : ownerHeld O NGr tl Fp Tp = .ok tl') : SameShp tl tl' := by
  unfold OnBytes.Model.Head.ownerHeld at h
  cases hb : O.tl.ix.TX.back? with
  | none =>
    simp only [hb] at h
    have h' : (Except.error "internal-h-owner-TX" : Except String HTailF2) = .ok tl' := h
    cases h'
  | some t =>
    simp only [hb] at h
    obtain ⟨last, -, h⟩ := ok_of_bind (x := (pure t : Except String ℕ)) h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    obtain ⟨t3, h3, h⟩ := ok_of_bind h
    obtain ⟨pe, -, h⟩ := ok_of_bind h
    obtain ⟨-, -, h⟩ := ok_of_bind h
    have e := (Except.ok.inj h).symm
    subst e
    exact borderMeans_shp h3

/-- **The shape equation in every record that planH2 returns.** -/
theorem planH2_mS {g : Settings} {h : Shape} {L : HL} {b : Border} {O : Owner} {NGr lkW : ℕ}
    {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∀ mu, mu < hp.tl.NM → (hp.tl.shp.getD mu {}).mS = ((hp.tl.mats.getD mu {}).m + 2) / 3 := by
  obtain ⟨stream, t1, r, Tp2, -, hr, h3, -, -⟩ := planH2_parts hpl
  obtain ⟨t2, Fp, Tp⟩ := r
  exact mS_of_same (ownerHeld_shp h3) (addTrees_mS hr)

/-- **THE STATEMENT**: at the head's plan in what publicOf returns. -/
theorem public_H_mS {pol KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (h : OnBytes.Model.Verify.publicOf pol KL layout = .ok X) :
    ∀ mu, mu < X.H.tl.NM → (X.H.tl.shp.getD mu {}).mS = ((X.H.tl.mats.getD mu {}).m + 2) / 3 := by
  obtain ⟨H0, h1, h2⟩ := Fo.Pub.public_H h
  rw [h2]
  exact planH2_mS (hp := H0) h1

end VerifiableInference.Desc.Kinds.Head.Law.InScope

#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.ownerHeld_shp
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.planH2_mS
#print axioms VerifiableInference.Desc.Kinds.Head.Law.InScope.public_H_mS
