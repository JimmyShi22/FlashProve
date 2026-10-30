-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Att/Door/Law/K5U3Cols.lean: THE KIND K8 (the smallness test's draw), "OWN SIZES", AT THE TWELVE ATTENTION SEGMENTS (k = 2 g + 1, g < 12): in the goals' scope, where the public part returns: the request's layout has an array (2 g + 1, "U3"); it has a row; and THE TABLES' END (P5J.K8N.tabsEnd, Johnson/P5J/K8ThreeBoxes.lean: the first entry behind the last table of K8.tabs) at the segment's own numbers is at most its number of columns. BY THE MAKE: no pin, no written value, no numeral of the scope but "twelve groups" and "profile 4". A join of theorems.

  `u3_array_att`: the layout's array (2 g + 1, "U3") has one row and a.nW columns.
  **`u3_cols_att`**: see its statement: the form of P5J.K8N.tabsEnd (a row of a list not named here; P5J.K8N.ColsAt, Johnson/P5J/K8EndsJoin.lean, has the same form) at k := 2 g + 1.
THE STONES. K5's files': att_tabsEnd_le (K5TabsEnd.lean: the end is at most the shape's tableElems: general in the shape) · K5Law.public_ofPlan · ofPlan_U · ofPlan_u3_tree (Johnson/Desc/First/Att/Claims/OfPlan.lean: the plan's array of the third vector is number 0: one row, nW columns). Other files': reads_room_of_built (Johnson/Desc/K1/Law/ReadsRoomAtAny.lean: behind an accept of buildLinksH the layout has every segment's "U3" with the plan's array's rows and columns) · plan_nW (Johnson/Desc/First/Link/Law/AttTabEntries.lean: nW is the shape's tableElems). Other files': IM.ground_tails (Johnson/IMR/K8Seat.lean) · IM.ground_named · ground_publicK · planned_built · plain_built (Johnson/IMR/PureJoin.lean) (the ground's segment 2 g + 1 has the attention plan's tl, kind 1 and group g). Other files': listLinksH_with (OnBytes/Tie/Pv/Keeps/LinksOrder.lean) · planA_mats (OnBytes/Tie/Pv/Lookup/Ends/FoPlaneMatPub.lean) · scope_plans (Johnson/Goal/Meaning/PlanShapes.lean). Other files': ProofFile.Law.blankBy_W (Johnson/Desc/ProofFile/Law/MakerPublic.lean).
HOW IT IS WRITTEN: after the two sister laws, which Lean has accepted: u3_cols_head (Johnson/P2LawR/U3ColsHead.lean: the accept of buildLinksH on the plain road: its lines, at any SecondHashFunctionArgument o) and u3_cols_lay (Johnson/Road/K4/Plan/U3ColsLay.lean: the two mapped arrays; the segment's own numbers).
Limits. u3_cols_att: AT OnBytes.secondHashFunction ALONE. That the public part returns at any files in scope, and that there is a ground, are premises. g < 12 is a premise. AN INEQUALITY: that it is met with nothing to spare is an evaluation, not shown here. Nothing on soundness.

-/
import Johnson.Desc.First.Att.Door.Law.K5TabsEnd
import Johnson.Desc.K1.Law.ReadsRoomAtAny
import Johnson.Desc.First.Att.Claims.OfPlan
import Johnson.IMR.K8Seat
import Johnson.IMR.PureJoin
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Goal.Meaning.PlanShapes

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace H2K5.Door
open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open VerifiableInference.Desc.First (K8.Asks.attention)

/-- **The layout's array of the reads at an attention segment**: one row, a.nW columns. -/
theorem u3_array_att {o : ProofFile.SecondHashFunctionArgument} {pol lay KL pol' KL' : ByteArray} {layout : Option ByteArray} {Z : ProofFile.Pub}
    (h : Verify.publicOf pol' KL' layout = .ok Z.p.X) (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (h4 : Z.p.X.p4 = true) {g : ℕ} {hp : Layer.HPlan2} {a : Attention.Plan}
    (hgp : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) :
    ∃ A, reqArray Z.first.layout (2 * g + 1) "U3" = some A ∧ A.sizeI = 1 ∧ A.sizeC = a.nW := by
  have hB : ProofFile.Plain.builtOf Z.p.X Z.p.chains = .ok Z.p.built :=
    IM.planned_built (ProofFile.Law.madeOf_planned (ProofFile.Law.pubBy_made
            (show ProofFile.pubBy (ProofFile.PlainG.madeOf o) ProofFile.plainStarts pol lay KL = .ok Z
              from hZ)))
  obtain ⟨l₀, h₀, hB⟩ := IM.plain_built hB
  unfold ProofFile.Plain.linksPlain at h₀
  rw [h4] at h₀
  obtain ⟨_, _, _, p0, _⟩ := OnBytes.L5.LinksOrder.listLinksH_with _ _ _ _ _ h₀
  have s0 : (Z.p.X.G.map fun hp : Layer.HPlan2 =>
      ({ tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := hp.tl, Fp := hp.Fp, Tp := hp.Tp, ns := hp.ns, NCL := hp.NCL,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, hgp]
    rfl
  have t0 : (Z.p.X.A.map fun A : Attention.Plan =>
      ({ tl := A.seam.tl, Fp := A.seam.Fp, Tp := A.seam.Tp, ns := A.ns,
         run := ProofFile.Plain.notToBeRun } : SubPlanH))[g]? =
      some { tl := a.seam.tl, Fp := a.seam.Fp, Tp := a.seam.Tp, ns := a.ns,
             run := ProofFile.Plain.notToBeRun } := by
    rw [Array.getElem?_map, ha]
    rfl
  obtain ⟨_, q1⟩ := p0 g _ _ s0 t0
  have OP := K5Law.public_ofPlan h g a ha
  have hU : a.seam.tl.ix.U.getD 2 none = some 0 := by
    rw [K5Law.ofPlan_U OP]
    rfl
  obtain ⟨e0, T, hT, hR, hK, -⟩ := K5Law.ofPlan_u3_tree OP
  rw [e0] at hT
  obtain ⟨tr, A, c2, c3, c4, c5⟩ :=
    VerifiableInference.Desc.K1.Only.reads_room_of_built hB q1 (t := 0) hU
  have c2' : a.seam.Fp.trees[0]? = some tr := c2
  obtain rfl : T = tr := Option.some.inj (hT.symm.trans c2')
  exact ⟨A, c3, c4.trans hR, c5.trans hK⟩

/-- **K8's "OWN SIZES" AT AN ATTENTION SEGMENT: THE VECTOR OF READS HAS ROOM FOR ALL TABLES.** (a row of a list not named here, at k = 2 g + 1, in its letters; P5J.K8N.ColsAt, Johnson/P5J/K8EndsJoin.lean, has the same form; g < 12 a premise, as in the layers' law.) -/
theorem u3_cols_att {Pb : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {ly : ByteArray} {Z : ProofFile.Pub} {G : ProofFile.Ground} {Xl : LinkH} {g : ℕ}
    (hS : VerifierAndGoals.InScope Pb = true) (hR : VerifierAndGoals.readFiles Pb = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction Pb.pol ly Pb.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hg : g < 12) (e3 : G.built[2 * g + 1]? = some Xl) :
    ∃ A, OnBytes.reqArray Z.first.layout (2 * g + 1) "U3" = some A ∧ 1 ≤ A.sizeI ∧
      P5J.K8N.tabsEnd (ProofFile.k8Par Z G Xl (2 * g + 1)) ≤ A.sizeC := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have hX : Verify.publicOf Pb.pol Pb.KL (some ly) = .ok Z.p.X := by
    rw [← eW]
    exact IM.ground_publicK hZ hG
  obtain ⟨k4, -, -, -⟩ := Meaning.scope_plans hS hR hX
  -- the segment's own numbers
  obtain ⟨hp, a, l, l', hgp, ha, -, -, -, -, -, -, f', t1, -⟩ := (IM.ground_tails hS hR hZ hG).1 g hg
  obtain rfl : l' = Xl := Option.some.inj (f'.symm.trans e3)
  obtain ⟨l2, l2', -, -, -, -, f2, kd, kg, -⟩ := (IM.ground_named hS hR hZ hG).1 g hg
  obtain rfl : l2' = l' := Option.some.inj (f2.symm.trans e3)
  rw [eW] at hgp ha
  -- the layout's array
  obtain ⟨A, a1, a2, a3⟩ := u3_array_att hX hZ k4 hgp ha
  -- the plan
  obtain ⟨settings, j, cf, a0, pf, h0, ea⟩ := K5Law.public_ofPlan hX g a ha
  have hnW : a.nW = a.S.tableElems := by
    have e := VerifiableInference.Desc.K9Asks.plan_nW h0
    rw [ea]
    exact e
  have hmats : a.seam.tl.mats = (Attention.matrices a.S j).map Fo.PlaneMat.markQ := by
    rw [ea]
    exact Fo.PlaneMat.planA_mats settings j cf a0 h0
  have hk : (ProofFile.k8Par Z G l2' (2 * g + 1)).ks =
      ((Attention.matrices a.S j).map Fo.PlaneMat.markQ).toList.map (·.k) := by
    show l2'.tl.mats.toList.map (·.k) = _
    rw [t1, hmats]
  have hm : (ProofFile.k8Par Z G l2' (2 * g + 1)).ms =
      ((Attention.matrices a.S j).map Fo.PlaneMat.markQ).toList.map (·.m) := by
    show l2'.tl.mats.toList.map (·.m) = _
    rw [t1, hmats]
  have hA : (ProofFile.k8Par Z G l2' (2 * g + 1)).asks = K8.Asks.attention a.S := by
    show ProofFile.k8Asks G l2' = _
    unfold ProofFile.k8Asks
    rw [kd, kg, eW, ha]
    rfl
  refine ⟨A, a1, Nat.le_of_eq a2.symm, ?_⟩
  rw [a3, hnW]
  exact att_tabsEnd_le a.S j _ hk hm hA

end H2K5.Door

#print axioms H2K5.Door.u3_array_att
#print axioms H2K5.Door.u3_cols_att
