-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
ON PUBLIC DATA, IN THE GOALS' SCOPE | UNDER THE HEAD.
Johnson/Desc/ProofFile/Honest/K3/Term/PlanesSizesAreTheFillings.lean: at public files in scope, the
matrix of planes (b, bA or bH) of each of the 25 links has in the plan's record the rows and columns
that the filling's typed sizes `Sz.ref` give it. The library has this off the planes
(`shapeNo_in_scope`, Johnson/Goal/HonestTrace/ShapesAtRefInScope.lean); this file adds the planes.

Why. The lookup's premise `ScriptHoldsThePackedTraceCells` reads the cells of every matrix of a
link. The step from the filling's sentence to that premise (PackedTraceCellsFromLaysFilling.lean)
needs the plan's sizes and the filling's sizes to agree, the planes included.

Main names:
  `PlanesSizesAreTheFillings`                the premise's form, at one link and one record
  `layerPlaneMatrixSizes`                    number 5 of a group's plan is b's size in `Sz.ref`
  `attentionPlaneMatrixOfThePlan`            the planes' entry of what `Attention.plan` returns
  `attentionPlaneMatrixSizes`                number 3 of an attention plan is bA's size
  `headPlaneMatrixSizes`                     number 6 of the head's plan is bH's size
  `planeMatrixSizesInScope`                  the three together, by a link's number
  `planesSizesAreTheFillingsUnderTheHead`    the same under the head h

Limits. Rows and columns alone, on public data, at the full size. Nothing on cells, on the `Script`
or on any property. The numbers lmb, lmbA, lmbH, kT and NC come from PlaneNumbersInScope.lean.
-/
import Johnson.Desc.First.Look.K3CallerAtt
import Johnson.Desc.ProofFile.Honest.K3.Term.PlaneNumbersInScope
import Johnson.Goal.HonestTrace.ShapesAtRefInScope
import Johnson.P5J.MgAtAll
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPub
import OnBytes.Tie.Pv.Lookup.Ends.FoPlaneMatPubG

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K3.Term
open OnBytes.Model (HTailF2)
open OnBytes.Maker (WholeD)
open OnBytes.HonestTrace (Sz Seg MatName planeOf)
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.First.Look (szOf)
open P5J (AtMgA TS)
open OnBytes.Model.Verify (publicOf)

local notation "PlaceL" => VerifiableInference.Desc.First.Look.Place
local notation "tailAt" => VerifiableInference.Desc.First.Look.tlAt

/-- **ON PUBLIC DATA: at the planes' matrix of a link the plan's record has the filling's rows and
columns.** Off the planes the library has it (`shapeNo_in_scope`,
Johnson/Goal/HonestTrace/ShapesAtRefInScope.lean). A definition: a premise's form. -/
def PlanesSizesAreTheFillings (link : ℕ) (tl : HTailF2) : Prop :=
  ∀ number segment, Sz.ref.matAt link number = some (segment, planeOf segment) →
    (szOf tl).m number = (Sz.ref.shapeNo link number).1 ∧
      (szOf tl).k number = (Sz.ref.shapeNo link number).2

section
variable {Zl : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : Option ByteArray}
  {X : OnBytes.Model.Verify.Public}

/-- The planes' matrix of a layers' plan has the number 5. -/
theorem layerPlaneMatrixNumber (filesInScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp) (publicReturns : publicOf Zl.pol Zl.KL lay = .ok X) :
    (OnBytes.Model.Layer.matIx X.layers.y).iB = 5 := by
  obtain ⟨six, -, -⟩ := Meaning.ix_of_core publicReturns
    (OnBytes.Road.Hd.core_of_scope filesInScope filesRead publicReturns)
  have next : (OnBytes.Model.Layer.matIx X.layers.y).iB + 1 =
      (OnBytes.Model.Layer.matIx X.y).iQA := rfl
  omega

/-- **At a group's plan.** -/
theorem layerPlaneMatrixSizes (filesInScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp) (publicReturns : publicOf Zl.pol Zl.KL lay = .ok X)
    (g : ℕ) {plan : OnBytes.Model.Layer.HPlan2}
    (planIsTheGroups : X.G[g]? = some plan) :
    (plan.tl.mats.getD 5 {}).m = Sz.ref.rows .b ∧
      (plan.tl.mats.getD 5 {}).k = Sz.ref.k (.ff g) .b := by
  obtain ⟨r, borders, mats⟩ :=
    Fo.PlaneMatG.planG_mats X.layers g _ plan (Fo.Pub.public_G publicReturns g plan planIsTheGroups)
  obtain ⟨sameRows, sameColumns⟩ := Fo.PlaneMatG.sameMK_getD
    (Fo.PlaneMatG.bordersOf_keeps borders) (OnBytes.Model.Layer.matIx X.layers.y).iB
  rw [Fo.PlaneMatG.public_tails publicReturns] at sameRows sameColumns
  obtain ⟨rows, columns⟩ := Fo.PlaneMatG.tailsOf_b X.layers.y g
    (Fo.PlaneMatG.public_G_lt publicReturns planIsTheGroups)
  obtain ⟨lmbIs, kTIs, NCIs⟩ := layerPlaneNumbers filesInScope filesRead publicReturns g
  have five := layerPlaneMatrixNumber filesInScope filesRead publicReturns
  rw [five] at sameRows sameColumns rows columns
  refine ⟨?_, ?_⟩
  · rw [mats, sameRows, rows]
    show 2 ^ X.y.h.lmb = 2 ^ Sz.ref.lmb
    rw [lmbIs]
  · rw [mats, sameColumns, columns, Fo.PlaneMatG.public_kbm publicReturns]
    show X.y.fo.NC * 2 ^ (X.y.fo.kT + 5 - X.y.h.lmb) =
      Sz.ref.NC (.ff g) * 2 ^ (Sz.ref.kT (.ff g) + 5 - Sz.ref.lmb)
    rw [lmbIs, kTIs, NCIs]

/-- The configuration that `Attention.fill` returns has the file's line NAs. -/
theorem partsOfAttentionFill {y : OnBytes.Model.Layer.Lay} {scales : OnBytes.Model.Layer.Scales}
    {lines : List OnBytes.Attention.Line} {g : ℕ} {cf : OnBytes.Attention.Cfg}
    (filled : OnBytes.Attention.fill X.P y scales lines g = .ok cf) : cf.NAs = X.P.h.NAs := by
  unfold OnBytes.Attention.fill at filled
  obtain ⟨-, filled⟩ := OnBytes.Road.L5.refuse_ok filled
  obtain ⟨-, filled⟩ := OnBytes.Road.L5.refuse_ok filled
  obtain rfl := Except.ok.inj filled
  rfl

/-- The planes' matrix in the list of a plan that `Attention.plan` returns. -/
theorem attentionPlaneMatrixOfThePlan {settings : OnBytes.Model.Settings}
    {input : OnBytes.Attention.In} {cf : OnBytes.Attention.Cfg} {plan : OnBytes.Attention.Plan}
    (made : OnBytes.Attention.plan settings input cf = .ok plan) :
    (plan.mats.getD (plan.S.cf.NAs + 2) {}).m = 2 ^ plan.S.cf.lmb ∧
      (plan.mats.getD (plan.S.cf.NAs + 2) {}).k = plan.S.kbA := by
  rw [Fo.PlaneMat.planA_mats settings input cf plan made]
  exact Fo.PlaneMat.matrices_bA plan.S input

/-- **At an attention plan.** -/
theorem attentionPlaneMatrixSizes (filesInScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp) (publicReturns : publicOf Zl.pol Zl.KL lay = .ok X)
    {g : ℕ} (groupBelow : g < 12) {plan : OnBytes.Attention.Plan} (planIsTheGroups : X.A[g]? = some plan) :
    (plan.seam.tl.mats.getD 3 {}).m = Sz.ref.rows .bA ∧
      (plan.seam.tl.mats.getD 3 {}).k = Sz.ref.k (.att g) .bA := by
  obtain ⟨sc, lines, cf, a0, _, _, _, made, ha, sameMats, _⟩ :=
    Fo.Pub.public_A publicReturns g plan planIsTheGroups
  obtain ⟨shaped, -⟩ := Fo.Pub.planA_shapeHid _ _ cf a0 made
  have cfIs : a0.S.cf = cf := (Fo.Pub2.shapeOf_shapeHid shaped).2
  have sameShape : plan.S = a0.S := by rw [ha]
  have sameForest : plan.fs = a0.fs := by rw [ha]
  obtain ⟨rows, columns⟩ := attentionPlaneMatrixOfThePlan made
  obtain ⟨lmbIs, kTIs, NCIs⟩ :=
    attentionPlaneNumbers filesInScope filesRead publicReturns groupBelow
  obtain ⟨shapeAt, forestAt, -⟩ := attentionPlanIsAtItsNumber planIsTheGroups
  rw [shapeAt] at lmbIs
  rw [forestAt] at kTIs NCIs
  obtain ⟨sc', midQ, lines', c, -, -, filled, -⟩ :=
    OnBytes.HonestTrace.PlaneLook.attention_configuration_is_the_fills publicReturns planIsTheGroups
  have partsAreOne : plan.S.cf.NAs = 1 := by
    rw [partsOfAttentionFill filled,
      OnBytes.Road.Hd.scan_of_scope filesInScope filesRead publicReturns]
    rfl
  have three : a0.S.cf.NAs + 2 = 3 := by rw [← sameShape, partsAreOne]
  have listIs : plan.seam.tl.mats = a0.mats := sameMats
  rw [three] at rows columns
  refine ⟨?_, ?_⟩
  · rw [listIs, rows, ← sameShape]
    show 2 ^ plan.S.cf.lmb = 2 ^ Sz.ref.lmbA
    rw [lmbIs]
  · rw [listIs, columns, Fo.PlaneMat.shapeHid_kbA shaped, ← cfIs, ← sameShape, ← sameForest]
    show plan.fs.NC * 2 ^ (plan.fs.kT + 5 - plan.S.cf.lmb) =
      Sz.ref.NC (.att g) * 2 ^ (Sz.ref.kT (.att g) + 5 - Sz.ref.lmbA)
    rw [lmbIs, kTIs, NCIs]

/-- **At the head's plan.** -/
theorem headPlaneMatrixSizes (filesInScope : VerifierAndGoals.InScope Zl = true) (filesRead : VerifierAndGoals.readFiles Zl = .ok pp)
    (publicReturns : publicOf Zl.pol Zl.KL lay = .ok X) :
    (X.H.tl.mats.getD 6 {}).m = Sz.ref.rows .bH ∧
      (X.H.tl.mats.getD 6 {}).k = Sz.ref.k .head .bH := by
  obtain ⟨H0, planned, -⟩ := Fo.Pub.public_H publicReturns
  obtain ⟨stream, -, listIs, -⟩ := Fo.Pub.public_mats publicReturns
  obtain ⟨rows, columns⟩ := Fo.PlaneMat.matsH_bH X.hS X.HLy
    (OnBytes.Model.Verify.borderOf X.layers.y) (1 + X.layers.y.NGr) stream.aId
  obtain ⟨lmbIs, kTIs, NCIs⟩ := headPlaneNumbers filesInScope filesRead publicReturns
  obtain ⟨partsAreFour, -⟩ :=
    VerifiableInference.Desc.Kinds.Head.Law.InScope.sizes_five filesInScope filesRead publicReturns
  have six : X.hS.NHf + 1 + 1 = 6 := by rw [partsAreFour]
  rw [six] at rows columns
  refine ⟨?_, ?_⟩
  · rw [listIs, rows]
    show 2 ^ X.hS.lmbH = 2 ^ Sz.ref.lmbH
    rw [lmbIs]
  · rw [listIs, columns, Fo.PlaneMat.planH2_kb planned]
    show X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH) =
      Sz.ref.NC .head * 2 ^ (Sz.ref.kT .head + 5 - Sz.ref.lmbH)
    rw [lmbIs, kTIs, NCIs]

/-- **By a link's number.** Where `Sz.ref.matAt` names a segment's planes, the plan's record of the
link has the rows and columns of `Sz.ref.shapeNo`. -/
theorem planeMatrixSizesInScope (filesInScope : VerifierAndGoals.InScope Zl = true)
    (filesRead : VerifierAndGoals.readFiles Zl = .ok pp) (publicReturns : publicOf Zl.pol Zl.KL lay = .ok X) {link : ℕ}
    {tl : HTailF2} (tailIsTheLinks : tailAt X link = some tl) :
    PlanesSizesAreTheFillings link tl := by
  intro number segment named
  obtain ⟨segmentBelow, linkIs, numberIs⟩ :=
    (OnBytes.HonestTrace.matAt_eq_some_iff Sz.ref link number segment (planeOf segment)).1 named
  have segmentBelow' : segment.Below 12 := segmentBelow
  have linkIs' : segment.no 12 = link := linkIs
  have shapeIs : Sz.ref.shapeNo link number =
      (Sz.ref.rows (planeOf segment), Sz.ref.k segment (planeOf segment)) := by
    unfold Sz.shapeNo
    rw [named]
    exact OnBytes.HonestTrace.shape_of_mu numberIs rfl rfl
  have nameIs := (OnBytes.HonestTrace.mu_ref segmentBelow' (planeOf segment)).symm.trans numberIs
  obtain ⟨profileFour, groupsTwelve, -, -⟩ := Meaning.scope_plans filesInScope filesRead publicReturns
  rw [shapeIs]
  cases segment with
  | ff g =>
    have groupBelow : g < 12 := segmentBelow'
    have linkNumber : link = 2 * g := linkIs'.symm
    have numberFive : number = 5 := by
      have e : MatName.no? 3 1 1 4 (.ff g) .b = some 5 := by simp [MatName.no?]
      exact Option.some.inj (nameIs.symm.trans e)
    subst linkNumber numberFive
    have tailIs : (X.G[g]?).map (·.tl) = some tl := by
      have e := tailIsTheLinks
      unfold VerifiableInference.Desc.First.Look.tlAt at e
      simp only [profileFour, groupsTwelve, ↓reduceIte] at e
      rw [if_neg (by simp only [beq_iff_eq]; omega), if_pos (by simp only [beq_iff_eq]; omega),
        show 2 * g / 2 = g by omega] at e
      exact e
    obtain ⟨plan, planIsTheGroups, tailIsThePlans⟩ := Option.map_eq_some_iff.1 tailIs
    subst tailIsThePlans
    exact layerPlaneMatrixSizes filesInScope filesRead publicReturns g planIsTheGroups
  | att g =>
    have groupBelow : g < 12 := segmentBelow'
    have linkNumber : link = 2 * g + 1 := linkIs'.symm
    have numberThree : number = 3 := by
      have e : MatName.no? 3 1 1 4 (.att g) .bA = some 3 := by simp [MatName.no?]
      exact Option.some.inj (nameIs.symm.trans e)
    subst linkNumber numberThree
    have tailIs : (X.A[g]?).map (·.seam.tl) = some tl := by
      have e := tailIsTheLinks
      unfold VerifiableInference.Desc.First.Look.tlAt at e
      simp only [profileFour, groupsTwelve, ↓reduceIte] at e
      rw [if_neg (by simp only [beq_iff_eq]; omega), if_neg (by simp only [beq_iff_eq]; omega),
        show (2 * g + 1) / 2 = g by omega] at e
      exact e
    obtain ⟨plan, planIsTheGroups, tailIsThePlans⟩ := Option.map_eq_some_iff.1 tailIs
    subst tailIsThePlans
    exact attentionPlaneMatrixSizes filesInScope filesRead publicReturns groupBelow planIsTheGroups
  | head =>
    have linkNumber : link = 24 := linkIs'.symm
    have numberSix : number = 6 := by
      have e : MatName.no? 3 1 1 4 .head .bH = some 6 := by simp [MatName.no?]
      exact Option.some.inj (nameIs.symm.trans e)
    subst linkNumber numberSix
    have tailIs : some X.H.tl = some tl := by
      have e := tailIsTheLinks
      unfold VerifiableInference.Desc.First.Look.tlAt at e
      simp only [profileFour, groupsTwelve, ↓reduceIte] at e
      rw [if_pos (by simp)] at e
      exact e
    obtain rfl := Option.some.inj tailIs
    exact headPlaneMatrixSizes filesInScope filesRead publicReturns

end

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {x₀ : PlaceL}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)

include h in
/-- **ON PUBLIC DATA, under the head.** The filling's sizes `Sz.ref` type the planes' numbers by hand
(lmb, lmbA, lmbH, kT, NC: Johnson/HonestTrace/Places.lean); the plan's record has the public files'.
In the goals' scope the two are one, at all 25 links. -/
theorem planesSizesAreTheFillingsUnderTheHead {link : ℕ} (linkBelow : link < 25) {tl : HTailF2}
    (tailIsTheLinks : tailAt (P5J.At.X Zp) link = some tl) :
    PlanesSizesAreTheFillings link tl :=
  planeMatrixSizesInScope h.scope h.reads h.pubOne tailIsTheLinks

end ProofFile.Honest.K3.Term

#print axioms ProofFile.Honest.K3.Term.layerPlaneMatrixNumber
#print axioms ProofFile.Honest.K3.Term.layerPlaneMatrixSizes
#print axioms ProofFile.Honest.K3.Term.partsOfAttentionFill
#print axioms ProofFile.Honest.K3.Term.attentionPlaneMatrixOfThePlan
#print axioms ProofFile.Honest.K3.Term.attentionPlaneMatrixSizes
#print axioms ProofFile.Honest.K3.Term.headPlaneMatrixSizes
#print axioms ProofFile.Honest.K3.Term.planeMatrixSizesInScope
#print axioms ProofFile.Honest.K3.Term.planesSizesAreTheFillingsUnderTheHead
