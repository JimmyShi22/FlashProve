-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/Plan/U3ColsLay.lean: THE KIND K8 (the smallness test's draw), "OWN SIZES", AT THE
TWELVE LAYERS' SEGMENTS (k = 2 g, g < 12): in the goals' scope, where the public part returns: the
request's layout has an array (2 g, "U3"); it has a row; and THE FIRST ENTRY BEHIND THE LAST TABLE
of K8.tabs at the segment's own numbers is at most its number of columns. BY THE MAKE: no pin, no
written value, no numeral of the scope but "twelve groups" and "profile 4". "THE TABLES' END" STANDS
HERE AS THE SECOND COMPONENT OF K8.tabs' OWN FOLD (Johnson/Desc/First/K8/Hear.lean), WRITTEN OUT:
P5J.K8N.tabsEnd (Johnson/P5J/K8ThreeBoxes.lean) is that term.

  `nameU3_eq`: the name as the maker spells it is "U3".
  `u3_array`: the layout's array (2 g, "U3") has one row and hp.nU[2] columns. The first half of the
    proof of `readsP_public` (Johnson/Road/K4/Rec/ReadsByMake.lean), line for line, ended earlier.
  **`u3_cols_lay`**: see its statement.
THE STONES. Ours: planG_u3 · declared_u3 · held_u3 · plain_cut (Road/K4/Rec/) · end_lay · planG_nU2
(TabsEndLay.lean). Johnson/IMR/'s ground_tails · ground_named · ground_publicK (the
ground's segment 2 g has the layers' plan's tl, kind 0 and group g). The library's pub34_public ·
tails_of_public · more_of_public · scope_plans · laid2_of_layout · tails_pair. ProofFile's blankBy_W.
Limits. AT OnBytes.secondHashFunction ALONE. That the public part returns at any files in scope, and that there
is a ground, are premises. g < 12 is a premise. AN INEQUALITY: that it is met with nothing to spare
is an evaluation, not shown here. Nothing on soundness.

-/
import Johnson.Road.K4.Plan.TabsEndLay
import Johnson.Road.K4.Rec.ReadsByMake
import Johnson.IMR.K8Seat
import Johnson.IMR.PureJoin
import Johnson.Desc.ProofFile.Lot.K8
import Johnson.Desc.ProofFile.Law.MakerPublic
import Johnson.Goal.Meaning.PlanShapes
import Johnson.Goal.Meaning.Pub34Scope

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4.Plan

open OnBytes OnBytes.Params OnBytes.Plan OnBytes.Model OnBytes.Model.Stages
open OnBytes.Model.Layer (matIx)
open OnBytes.Road.K4.Rec (planG_u3 plain_cut declared_u3 held_u3 nameU3 trimT u3Tree)
open VerifiableInference.Desc.First.K8 (layFamily)

/-- The name of the array of the reads, as the maker spells it. -/
theorem nameU3_eq : nameU3 = "U3" := by decide +kernel

/-- **The layout's array of the reads at a layers' segment**: one row, hp.nU[2] columns. -/
theorem u3_array {o : ProofFile.SecondHashFunctionArgument} {pol lay KL pol' KL' : ByteArray}
    {layout : Option ByteArray} {Z : ProofFile.Pub}
    (h : Verify.publicOf pol' KL' layout = .ok Z.p.X) (hZ : ProofFile.pubPlain o pol lay KL = .ok Z)
    (h4 : Z.p.X.p4 = true) {g : ℕ} {hp : Layer.HPlan2} {a : Attention.Plan}
    (hgp : Z.p.X.G[g]? = some hp) (ha : Z.p.X.A[g]? = some a) :
    ∃ A, reqArray Z.first.layout (2 * g) "U3" = some A ∧ A.sizeI = 1 ∧
      A.sizeC = hp.nU.getD 2 0 := by
  obtain ⟨eU, eT⟩ := planG_u3 _ _ _ _ (Fo.Pub.public_G h g hp hgp)
  obtain ⟨l₀, declared, h₀, hd, hh, _⟩ := plain_cut hZ
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
  obtain ⟨q0, _⟩ := p0 g _ _ s0 t0
  obtain ⟨ar, t, n, hn, har, ht, _, hl, h1, hm⟩ := declared_u3 hd q0 eU
  obtain rfl : trimT (u3Tree (hp.nU.getD 2 0)) = t := Option.some.inj (eT.symm.trans ht)
  have hD : declared[2 * g]? = some (declared.getD (2 * g) {}) := by
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem hl]
    rfl
  obtain ⟨A, L, m, hA, hL, hmm, s1, s2, s3⟩ := held_u3 hh hD h1 hm
  have hA' : reqArray Z.first.layout (2 * g) nameU3 = some A := hA
  have s1' : A.sizeI = 1 := s1
  have s2' : A.sizeC = hp.nU.getD 2 0 := s2
  exact ⟨A, by rw [← nameU3_eq]; exact hA', s1', s2'⟩

/-- **K8's "OWN SIZES" AT A LAYERS' SEGMENT: THE VECTOR OF READS HAS ROOM FOR ALL TABLES.** -/
theorem u3_cols_lay {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray} {Z : ProofFile.Pub}
    {G : ProofFile.Ground} {Xl : LinkH} {g : ℕ}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (hZ : ProofFile.pubPlain OnBytes.secondHashFunction P.pol lay P.KL = .ok Z)
    (hG : ProofFile.blankBy ProofFile.pureRoad.links Z = some G) (hg : g < 12)
    (e3 : G.built[2 * g]? = some Xl) :
    ∃ A, reqArray Z.first.layout (2 * g) "U3" = some A ∧ 1 ≤ A.sizeI ∧
      ((ProofFile.k8Par Z G Xl (2 * g)).asks.foldl
        (fun x a => let y := layFamily (ProofFile.k8Par Z G Xl (2 * g)) a x.2; (x.1 ++ y.1, y.2))
        ([], 0)).2 ≤ A.sizeC := by
  have eW : G.W = Z.p.X := ProofFile.Law.blankBy_W hG
  have hX : Verify.publicOf P.pol P.KL (some lay) = .ok Z.p.X := by
    rw [← eW]
    exact IM.ground_publicK hZ hG
  obtain ⟨k4, kN, -, -⟩ := Meaning.scope_plans hS hR hX
  -- the segment's own numbers
  obtain ⟨hp, a, l, l', hgp, ha, f, t1, -⟩ := (IM.ground_tails hS hR hZ hG).1 g hg
  obtain rfl : l = Xl := Option.some.inj (f.symm.trans e3)
  obtain ⟨l2, l2', f2, kd, kg, -⟩ := (IM.ground_named hS hR hZ hG).1 g hg
  obtain rfl : l2 = l := Option.some.inj (f2.symm.trans e3)
  rw [eW] at hgp ha
  -- the layout's array
  obtain ⟨A, a1, a2, a3⟩ := u3_array hX hZ k4 hgp ha
  -- the layers' layout, the reads, the plan
  obtain ⟨hy, -, -, hrd, -⟩ := Meaning.P34.pub34_public hS hR hX
  have L := OnBytes.Road.laid2_of_layout hy
  have F := filled_of_layout hy
  have hgN : g < Z.p.X.y.NGr := by
    have e : Z.p.X.y.NGr = 12 := kN
    omega
  have htm := (Meaning.P34.tails_of_public hX hgp).1
  have ely : Z.p.X.layers.y = Z.p.X.y :=
    (Meaning.P34.pub_more (Meaning.P34.more_of_public hX).2.2.2.1).1
  have hn := planG_nU2 _ _ _ _ (Fo.Pub.public_G hX g hp hgp)
  rw [ely] at hn
  have tXI := OnBytes.Road.tails_pair Z.p.X.y hgN (mat := 4) (p := 0) (by decide) Nat.zero_lt_one
  rw [← htm, pair_of] at tXI
  obtain ⟨x1, x2⟩ := Prod.mk.inj tXI
  have x1' : (hp.tl.mats.getD (matIx Z.p.X.y).iXI {}).m = Z.p.X.y.mxb := x1
  have x2' : (hp.tl.mats.getD (matIx Z.p.X.y).iXI {}).k = Z.p.X.y.kxb := x2
  rw [x1', x2'] at hn
  have hA : (ProofFile.k8Par Z G l2 (2 * g)).asks =
      VerifiableInference.Desc.First.K8.Asks.layers Z.p.X.y Z.p.X.layers.rd g := by
    show ProofFile.k8Asks G l2 = _
    unfold ProofFile.k8Asks
    rw [kd, kg, eW]
    rfl
  have hk : ∀ M, (ProofFile.k8Par Z G l2 (2 * g)).ks.getD M 0 =
      ((OnBytes.Road.matsR Z.p.X.y g).getD M (0, 0)).2 := by
    intro M
    show (l2.tl.mats.toList.map (·.k)).getD M 0 = _
    rw [t1, ks_at, ← htm, pair_of]
  have hm : ∀ M, (ProofFile.k8Par Z G l2 (2 * g)).ms.getD M 0 =
      ((OnBytes.Road.matsR Z.p.X.y g).getD M (0, 0)).1 := by
    intro M
    show (l2.tl.mats.toList.map (·.m)).getD M 0 = _
    rw [t1, ms_at, ← htm, pair_of]
  refine ⟨A, a1, Nat.le_of_eq a2.symm, ?_⟩
  rw [a3, hn]
  exact end_lay L F hrd hgN _ hA hk hm

end OnBytes.Road.K4.Plan

#print axioms OnBytes.Road.K4.Plan.nameU3_eq
#print axioms OnBytes.Road.K4.Plan.u3_array
#print axioms OnBytes.Road.K4.Plan.u3_cols_lay
