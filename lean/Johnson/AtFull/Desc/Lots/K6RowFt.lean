-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Desc/Lots/K6RowFt.lean: ONE FIELD OF K6Reads (K6Row.lean) IS SHOWN: THE OUTPUT
HEAD'S PLAN HAS JUST ONE FOREIGN ARRAY: wherever Head.planH2 (OnBytes/Model/HeadPlan.lean) returns,
and so in what Verify.publicOf hands on, the map's list FT has one entry. General: no scope, no
size. Statements and proofs; nothing is evaluated.

Main names (namespace Johnson.AtFull.Lots).
  planH2_ft: ∃ t, hp.tl.ix.FT.toList = [t]. public_H_ft: the same at X.H.tl.

Why it holds. planH2 calls the shapes' routine with a written list of ONE foreign array ("PXf0");
that routine lays one number of the map for each; the two routines behind it keep the map.
By planH2_parts (Johnson/Desc/Kinds/Law/HeadPlanWritten.lean) and shapeF_ftSize
(Johnson/Road/K4/Names/ShapeTrees.lean), and the library's
addTreesF_record
(OnBytes/Tie/Pv/Tail/EndRuns.lean), ownerHeld_record (EndPlans.lean) and Fo.Pub.public_H.
What it does not say. That the planner returns anywhere. THAT THE LAST BUILT SEGMENT'S RECORD BEARS
THE PLAN'S tl (X.tl = G.W.H.tl): the field of K6Reads speaks of the built segment: that join is not
made here. Under the library's publicOf alone. Nothing on soundness.
-/
import Johnson.Desc.Kinds.Law.HeadPlanWritten
import Johnson.Road.K4.Names.ShapeTrees
import OnBytes.Tie.Pv.Tail.EndPlans

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.AtFull.Lots

open OnBytes.Model (Settings)
open OnBytes.Model.Head (Shape HL Border Owner HPlanH2 planH2)
open VerifiableInference.Desc.Kinds.Head.Law.InScope (planH2_parts)

/-- **The head's plan has just one foreign array.** -/
theorem planH2_ft {g : Settings} {h : Shape} {L : HL} {b : Border} {O : Owner} {NGr lkW : ℕ}
    {hp : HPlanH2} (hpl : planH2 g h L b O NGr lkW = .ok hp) :
    ∃ t, hp.tl.ix.FT.toList = [t] := by
  obtain ⟨stream, t1, r, Tp2, h1, hr, h3, -, -⟩ := planH2_parts hpl
  obtain ⟨t2, Fp, Tp⟩ := r
  have s1 : t1.ix.FT.size = 1 := OnBytes.Road.K4.Names.shapeF_ftSize h1
  have s2 : t2.ix = t1.ix :=
    (OnBytes.Tie.Pv.Tail.addTreesF_record t1 t2 _ Fp _ Tp _ _ _ _ hr).2.1
  have s3 : hp.tl.ix = t2.ix := (OnBytes.Tie.Pv.Tail.ownerHeld_record O NGr t2 hp.tl Fp Tp2 h3).ix
  have s4 : hp.tl.ix.FT.toList.length = 1 := by
    rw [s3, s2, Array.length_toList]
    exact s1
  exact List.length_eq_one_iff.1 s4

/-- The same at the head's plan in what publicOf returns. -/
theorem public_H_ft {pol KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} (h : OnBytes.Model.Verify.publicOf pol KL layout = .ok X) :
    ∃ t, X.H.tl.ix.FT.toList = [t] := by
  obtain ⟨H0, h1, h2⟩ := Fo.Pub.public_H h
  rw [h2]
  exact planH2_ft (hp := H0) h1

end Johnson.AtFull.Lots

#print axioms Johnson.AtFull.Lots.planH2_ft
#print axioms Johnson.AtFull.Lots.public_H_ft
