-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5ShpOfPlan.lean: WHERE THE ATTENTION SUB-PROOF's PLANNER RETURNS, EACH MATRIX's SHAPE HAS A THIRD OF ITS ROWS OF CELLS, ROUNDED UP, AS ITS ROWS OF SYMBOLS.
General: no head, no scope, no premise but the routine's return (in the third: and the membership in X.A). Nothing of K5 stands in it.

The fact itself is OnBytes.Road.K4.Plan.addTrees_mS (Johnson/Road/K4/Plan/ShapeRows.lean): where addTrees returns, the smallness test that it returns has it. Here it is carried to the three places at which the attention plan is spoken of:
  `seamPlan_mS`: where Attention.Seam.plan returns r: at r.tl.
  `planA_mS`: where Attention.plan returns P: at P.seam.tl.
  `public_A_mS`: at every member a of X.A, where Verify.publicOf returns X: at a.seam.tl.
The conclusion is the premise hS of Fo.topOf_eq (OnBytes/Tie/Pv/Lookup/Ends/FoTopOf.lean).
How. Seam.plan's returned tl is what addTrees returned (the walk of Fo.PlaneMat.seamPlan_mats); Attention.plan's seam is what Seam.plan returned (Fo.BatRows.planA_rows0); a member of X.A has such a seam but for the field plFor (Fo.PubA.public_A_seam_at), which the sentence does not read.
Limits. That a planner returns anywhere is not said. One direction: from a routine that returns. Nothing on soundness, completeness or hiding.

-/
import Johnson.Road.K4.Plan.ShapeRows
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicASeam

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace H2K5.Door
open OnBytes OnBytes.Model Fo.BatRows

/-- **(b) Where Attention.Seam.plan returns**, each matrix's shape in the returned seam's smallness test (r.tl) has a third of its rows of cells, rounded up, as its rows of symbols. -/
theorem seamPlan_mS {s r : Attention.Seam} {nU3 hb hbLine : ℕ} (e : s.plan nU3 hb hbLine = .ok r) :
    ∀ mu, mu < r.tl.NM → (r.tl.shp.getD mu {}).mS = ((r.tl.mats.getD mu {}).m + 2) / 3 := by
  unfold Attention.Seam.plan at e
  dsimp only at e
  obtain ⟨⟨tl, Fp, T⟩, h0, e⟩ := bindE_ok e
  dsimp only at e
  split at e
  · obtain ⟨_, e1, _⟩ := bindE_ok e
    cases e1
  obtain ⟨_, _, e⟩ := bindE_ok e
  obtain ⟨Tp, _, e⟩ := bindE_ok e
  cases e
  exact OnBytes.Road.K4.Plan.addTrees_mS h0

/-- **(c) Where Attention.plan returns**: the same at the plan's seam. -/
theorem planA_mS (settings : Settings) (i : Attention.In) (cf : Attention.Cfg) (P : Attention.Plan)
    (e : Attention.plan settings i cf = .ok P) :
    ∀ mu, mu < P.seam.tl.NM → (P.seam.tl.shp.getD mu {}).mS = ((P.seam.tl.mats.getD mu {}).m + 2) / 3 := by
  obtain ⟨_, _, h1, _⟩ := planA_rows0 settings i cf P e
  exact seamPlan_mS h1

/-- **(d) At every attention plan in what Verify.publicOf derives from the configuration files.** -/
theorem public_A_mS {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : Verify.publicOf pol KL layout = .ok X) (g : ℕ) (a : Attention.Plan) (hg : X.A[g]? = some a) :
    ∀ mu, mu < a.seam.tl.NM → (a.seam.tl.shp.getD mu {}).mS = ((a.seam.tl.mats.getD mu {}).m + 2) / 3 := by
  obtain ⟨_, s1, _, h1, ea⟩ := Fo.PubA.public_A_seam_at h g a hg
  have eN : a.seam.tl.NM = s1.tl.NM := by rw [ea]
  have eS : a.seam.tl.shp = s1.tl.shp := by rw [ea]
  have eM : a.seam.tl.mats = s1.tl.mats := by rw [ea]
  intro mu hmu
  rw [eS, eM]
  exact seamPlan_mS h1 mu (eN ▸ hmu)

end H2K5.Door

#print axioms H2K5.Door.seamPlan_mS
#print axioms H2K5.Door.planA_mS
#print axioms H2K5.Door.public_A_mS
