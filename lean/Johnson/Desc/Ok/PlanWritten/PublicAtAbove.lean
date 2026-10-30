-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Ok/PlanWritten/PublicAtAbove.lean: laws of the library that take the premise
"`publicOf` returns X" (OnBytes/Model/VerifyPublic.lean) and hand it down, each once more at the
text that takes the second hash function as an argument o (`publicOfO o`,
Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

Why. The lemmas that open the text have their twins at o
(Johnson/Desc/Ok/PlanWritten/PublicAtBase.lean). A law above them is stated at the library's text,
so it does not apply to what `publicOfO o` returns. Its proof reads the premise only through lemmas
that have twins, so the same proof goes through.

What is here. For each such declaration a twin: the statement and the proof are the library's, line
for line, with `publicOfO o` for `publicOf` and the twin's name for each called declaration that has
one. A twin's name is the source file's name, a dot, and the declaration's name with an O behind it.
The twins were made by a program from the library's text. They stand in the order in which they call
one another.

The twins: `PublicCore.public_of_coreO`, `HeadL5Grp.scalesHeld_of_publicO`,
`HeadL5Grp.scales_of_publicO`, `FormsKeysLawP.shape_of_publicO`, `Lane5AttPub.label_publicO`,
`Lane5AttPub.att_publicO`, `PublicCore.eleven_of_coreO`, `GlueRows.row_glue_plan_AO`,
`FoPublic.publicOf_cutO`, `FoPublicA.public_AO`, `HeadShapeOfSettings.hS_of_settingsO`,
`row_glue_plan_AO_older`.

One twin is of a definition: `GlueRows.row_glue_plan_AO o` is the closed statement `row_glue_plan_A`
(OnBytes/Tie/Pv/Tail/GlueRows.lean) with `publicOfO o` inside; `row_glue_plan_AO_older`: at the
second hash function itself it says what the library's statement says. Whoever has the library's
statement as a premise does not get a premise at o from the twin: that would be a change of their
statement. `FoPublic.publicOf_cutO` has the shape of the library's `publicOf_cut`, explicit
arguments and the same conjuncts, because proofs take that lemma apart by position; `publicOfO_cut`
(Johnson/Desc/Ok/PlanWritten/PublicAtCut.lean) has one conjunct more.

The statements are tools: they hold of all public files and all arguments o, and no description of
the protocol is named. What of OnBytes/Model/ is used: what the library's declarations use.

Limits. Which declarations are wanted was found by a program that follows the names in the proofs
downward from the laws that two other authors asked for; a law that nobody asked for has no twin
here. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAtBase
import Johnson.Meaning.PublicCore
import Johnson.Road.HeadL5Grp
import Johnson.Road.FormsKeysLawP
import Johnson.Road.Lane5AttPub
import OnBytes.Tie.Pv.Tail.GlueRows
import OnBytes.Tie.Pv.Lookup.Ends.FoPublic
import OnBytes.Tie.Pv.Lookup.Ends.FoPublicA
import Johnson.Flat.HeadShapeOfSettings

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd
open Inst.Model (NormPar tbRef)
open Inst.Model.All (DF)

/-- At o: **The public hypotheses on the layers and on the head, from the verifier's own call and
the 41 numbers.** -/
theorem PublicCore.public_of_coreO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X) (A : PublicCore X.P) : LayersHeadAt X := by
  obtain ⟨P, y, hpl, eP, ey, eS, -, hl, -⟩ := HeadPub.public_partsO h
  have hy := layerLayout_of_polLayout hpl
  rw [← eP, ← ey] at hy
  rw [← ey] at hl
  have S := switches_of_core A
  have hN := (admitted_of_layout hy S.p3).NGr
  have e1 : X.P.h.L = 48 := A.num 2
  have e2 : X.P.h.ll = 2 := A.num 3
  have eS' : X.hS = Model.Verify.headShape X.P X.y := by rw [eS, eP, ey]
  exact {
    lay := hy
    switches := S
    sized := sized_of_core A
    sized2 := sized2_of_core A
    p4 := p4_of_core A
    groups := by
      rw [hN]
      show X.P.h.L / 2 ^ X.P.h.ll = 12
      rw [e1, e2]
      norm_num
    full := by
      rw [eS']
      exact fullH_of_core A X.y
    head := hl
    sh := by
      rw [eS']
      exact A.num 32
    sT := by
      rw [eS']
      exact A.num 33 }

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd

/-- At o: They have passed the verifier's tests on the scales. -/
theorem HeadL5Grp.scalesHeld_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray}
    {X : Model.Verify.Public} (h : publicOfO o pol KL lay = .ok X) :
    Model.Layer.scalesHeld X.y.h X.layers.sc = .ok () :=
  (HeadL5Grp.scalesBoth_of_publicO h).2

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd

/-- At o: **The scales in the public part are what the verifier's function reads off the scale
file.** -/
theorem HeadL5Grp.scales_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X) :
    Model.Layer.scalesOf X.y.h (Model.fileWords KL) = .ok X.layers.sc :=
  (HeadL5Grp.scalesBoth_of_publicO h).1

end

section
open _root_.OnBytes _root_.OnBytes.Road
open OnBytes.Model.Layer (Shape Scales)
open OnBytes.Model.Verify (Public publicOf layerShape)
open Inst.Model (NormPar)

/-- At o: The shape of the layout in the value of publicOf is the layers' shape of the parameter
file as read. -/
theorem FormsKeysLawP.shape_of_publicO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Public}
    (h : publicOfO o pol KL lay = .ok X) : X.y.h = layerShape X.P := by
  obtain ⟨P, y, hpl, eP, ey, -⟩ := HeadPub.public_partsO h
  rw [ey, eP]
  exact layout_shape (Hd.layerLayout_of_polLayout hpl)

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.L5
open Inst.Model
open OnBytes.Model.Layer (matIx)
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- At o: **In the list of the plan X.A[g] the copy of qa bears the label that the layers' formula
gives the matrix qa of group g.** -/
theorem Lane5AttPub.label_publicO {o : Nat → ByteArray → ByteArray}
    (h : publicOfO o pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) {g : ℕ} (hg : g < X.y.NGr) :
    ∃ Ag, X.A[g]? = some Ag ∧ Ag.S = Hd.shapeA X g ∧
      (Ag.seam.tl.mats[Ag.S.cf.NAs + 3]?).map (fun M => M.aId) =
        some (labA X.y g (matIx X.y).iQA) := by
  obtain ⟨lines, A0, seenG, seenA, hO, H⟩ := HeadL5Grp.groups_of_publicO h hp4
  obtain ⟨Xg, Ag, s, hG, h0, hs, hA, eAS, -, -, etl, eS⟩ := H g hg
  refine ⟨Ag, hA, eAS.trans eS.symm, ?_⟩
  rw [etl, owners_plan hO h0 hs, eAS]
  exact group_label_qa hG hg

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.L5
open Inst.Model
open OnBytes.Model.Layer (matIx)
variable {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}

/-- At o: **Attention's public hypotheses, at the shape of the plan X.A[g].** -/
theorem Lane5AttPub.att_publicO {o : Nat → ByteArray → ByteArray}
    (h : publicOfO o pol KL lay = Except.ok X)
    (hp4 : (Model.Verify.layerShape X.P).p4 = true) (F : FillRef X.P X.y) {g : ℕ}
    (hg : g < X.y.NGr) (hg12 : g < 12) (hL : Model.Layer.Shape) (nf : NormPar) :
    AttSized (Hd.shapeA X g) ∧
      ((scalesOf hL X.layers.sc nf).kap (4 * g)).sh = (Hd.shapeA X g).cf.sh.getD 0 0 ∧
      (∀ ι : ℕ, ι < (Hd.shapeA X g).u0 →
        (((Hd.shapeA X g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) ∧
      7200 ≤ (Hd.shapeA X g).kAs / (Hd.shapeA X g).cf.NAs * (Hd.shapeA X g).cf.NAs := by
  obtain ⟨lines, A0, seenG, seenA, -, H⟩ := HeadL5Grp.groups_of_publicO h hp4
  obtain ⟨Xg, Ag, s, hG, -, -, -, -, -, -, -, eS⟩ := H g hg
  rw [eS]
  obtain ⟨cf, hf, Sh, hLam, -⟩ := shaped_of_group hG
  obtain ⟨hc, h12, h8, hN⟩ := cfRef_of_fill hf F
  obtain ⟨hu, hE⟩ := exp_of_shaped Sh h12 h8
  have hS := sized_of_shaped Sh hc hu
  refine ⟨hS, ?_, hE, wide_of_shaped Sh hc hN⟩
  rw [Sh.cfg]
  exact hsh_of_fill hf (hLam.symm.trans hS.Lam) hg12 hL nf

end

section
open _root_.OnBytes _root_.OnBytes.Road _root_.OnBytes.Road.Hd
open Inst.Model (NormPar tbRef)
open Inst.Model.All (DF)

/-- At o: **All eleven public hypotheses, from the verifier's own call and the 41 numbers.** nf: any
numbers of the final normalisation; the table of scales is made of the scale file's words and of nf.
The last clause, on the width of attention's matrix of weights, is asked only where the bundle of
statements is shown to have a value. -/
theorem PublicCore.eleven_of_coreO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {lay : Option ByteArray} {X : Model.Verify.Public}
    (h : publicOfO o pol KL lay = .ok X) (A : PublicCore X.P) (nf : NormPar) :
    LayersHeadAt X ∧ (∀ g, g < 12 → L5.AttSized (shapeA X g)) ∧
      (∀ g, g < 12 →
        ((scalesOf (Model.Verify.layerShape X.P) X.layers.sc nf).kap (4 * g)).sh =
          (shapeA X g).cf.sh.getD 0 0) ∧
      (∀ g, g < 12 → ∀ ι : ℕ, ι < (shapeA X g).u0 →
        (((shapeA X g).Tt.getD ι 0 : ℕ) : ℤ) = tbRef.Exp ι) ∧
      ∀ g, g < 12 → 7200 ≤ (shapeA X g).kAs / (shapeA X g).cf.NAs * (shapeA X g).cf.NAs := by
  have H := PublicCore.public_of_coreO h A
  have F := fillRef_of_core A H
  have K : ∀ g, g < 12 → _ := fun g hg =>
    Lane5AttPub.att_publicO h H.p4 F (by rw [H.groups]; exact hg) hg (Model.Verify.layerShape X.P)
        nf
  exact ⟨H, fun g hg => (K g hg).1, fun g hg => (K g hg).2.1, fun g hg => (K g hg).2.2.1,
    fun g hg => (K g hg).2.2.2⟩

end

section
open _root_.OnBytes _root_.OnBytes.Tie _root_.OnBytes.Tie.Pv _root_.OnBytes.Tie.Pv.Tail
    _root_.OnBytes.Tie.Pv.Tail.GlueRows
open OnBytes OnBytes.Model

/-- At o: (U7) A member of X.A has the shape and the own rounds' numbers of a plan that
Attention.plan has made. From public_A. -/
def GlueRows.row_glue_plan_AO (o : Nat → ByteArray → ByteArray)
    : Prop :=
  ∀ (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public),
    publicOfO o pol KL layout = .ok X → ∀ (g : Nat) (a : Attention.Plan), X.A[g]? = some a →
    ∃ settings i cf P0, Attention.plan settings i cf = .ok P0 ∧ a.S = P0.S ∧ a.own = P0.own

end

section
open _root_.Fo _root_.Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

/-- At o: A run of publicOf that returns, in X's own fields. -/
theorem FoPublic.publicOf_cutO {o : Nat → ByteArray → ByteArray}
    (pol KL : ByteArray) (layout : Option ByteArray) (X : Verify.Public)
    (h : publicOfO o pol KL layout = .ok X) :
    Verify.polLayout pol = .ok (X.P, X.layers.y) ∧
    X.hS = Verify.headShape X.P X.layers.y ∧
    Layer.plansG X.layers = .ok X.G ∧
    Verify.ownerOf X.layers.y X.G = .ok X.owner ∧
    (∃ H0, Head.planH2 X.P.settings X.hS X.HLy (Verify.borderOf X.layers.y) X.owner
        X.layers.y.NGr X.P.lkW = .ok H0 ∧ X.H = { H0 with Fp := H0.Fp.trimL }) ∧
    ∃ (sc : Layer.Scales) (A0 : Array Attention.Plan) (seen : Array Verify.SubPlan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      ((X.layers.y.h.p4 = true ∧
          ∃ c, Attention.configO o X.P X.layers.y sc (midQ X.layers.y) = .ok c ∧ A0 = c.plans) ∨
        (X.layers.y.h.p4 = false ∧ A0 = #[])) ∧
      Verify.attentionOwners X.layers.y.h.p4 X.layers.y.NGr (seenG X.G) (seenA0 A0) = .ok seen ∧
      X.A = A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seen := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, k1, h⟩ := bindE_ok h
  dsimp only at h
  obtain ⟨sc, k2, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  have h := ite_unit_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨wsLay, _, h⟩ := bindE_ok h
  obtain ⟨rope, _, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain ⟨HLy, _, h⟩ := bindE_ok h
  obtain ⟨y2, k3, h⟩ := ite_pure_ok h
  obtain ⟨layers, k4, h⟩ := bindE_ok h
  obtain ⟨G, k5, h⟩ := bindE_ok h
  obtain ⟨seen, k6, h⟩ := bindE_ok h
  obtain ⟨owner, k7, h⟩ := bindE_ok h
  obtain ⟨H0, k8, h⟩ := bindE_ok h
  obtain ⟨_, _, h⟩ := bindE_ok h
  obtain rfl := Except.ok.inj h
  have hy : layers.y = y := pubOf_y k4
  dsimp only
  rw [hy]
  refine ⟨k1, rfl, k5, k7, ⟨H0, k8, rfl⟩, sc, y2.1, seen, k2, ?_, k6, rfl⟩
  rcases k3 with ⟨hp, c, k9, e⟩ | ⟨hp, e⟩
  · exact .inl ⟨hp, c, k9, by rw [e]⟩
  · exact .inr ⟨by simpa using hp, by rw [e]⟩

end

section
open _root_.Fo _root_.Fo.Pub
open OnBytes OnBytes.Model Fo.BatRows

/-- At o: A member of X.A. -/
theorem FoPublicA.public_AO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray} {X : Verify.Public}
    (h : publicOfO o pol KL layout = .ok X) (g : Nat) (a : Attention.Plan)
    (hg : X.A[g]? = some a) :
    ∃ (sc : Layer.Scales) (lines : List Attention.Line) (cf : Attention.Cfg)
      (a0 : Attention.Plan),
      Layer.scalesOf X.layers.y.h (fileWords KL) = .ok sc ∧
      Attention.readLines X.P.polCallsA = .ok lines ∧
      Attention.fill X.P X.layers.y sc lines g = .ok cf ∧
      Attention.plan X.P.settings
        (Attention.inOf X.P.settings X.layers.y (midQ X.layers.y g) g) cf = .ok a0 ∧
      a = { a0 with seam := { a0.seam with tl := a.seam.tl } } ∧
      a.seam.tl.mats = a0.seam.tl.mats ∧ a.seam.tl.tau = a0.seam.tl.tau := by
  obtain ⟨_, _, _, _, _, sc, A0, seen, k2, k3, k6, k7⟩ := FoPublic.publicOf_cutO pol KL layout X h
  rw [k7] at hg
  have hz : ∃ a0 s, A0[g]? = some a0 ∧ seen[g]? = some s ∧
      a = { a0 with seam := { a0.seam with tl := s.tl } } := by
    rw [← Array.getElem?_toList, Array.toList_zipWith] at hg
    obtain ⟨a0, s, e1, e2, e3⟩ := List.getElem?_zipWith_eq_some.1 hg
    exact ⟨a0, s, by simpa using e1, by simpa using e2, e3.symm⟩
  obtain ⟨a0, s, e1, e2, e3⟩ := hz
  obtain ⟨s0, f1, f2⟩ := owners_keeps k6 g s e2
  have f3 : s0 = ⟨a0.seam.tl, a0.seam.Fp, a0.seam.Tp⟩ := by
    unfold seenA0 at f1
    rw [Array.getElem?_map, e1] at f1
    exact (Option.some.inj f1).symm
  rcases k3 with ⟨_, c, k9, rfl⟩ | ⟨_, rfl⟩
  · obtain ⟨lines, l1, l2⟩ := configO_at k9
    obtain ⟨cf, m1, m2⟩ := group_plan (l2 g a0 e1)
    subst e3
    refine ⟨sc, lines, cf, a0, k2, l1, m1, m2, rfl, ?_, ?_⟩
    · show s.tl.mats = _
      rw [f2.1, f3]
    · show s.tl.tau = _
      rw [f2.2, f3]
  · simp at e1

end

section
open _root_.OnBytes _root_.OnBytes.Flat
open OnBytes.Model

/-- At o: **Where, at the same two files, `settingsAtRef` returns settings pp and `publicOf` returns
a public part X, the record `X.hS` has the C, theta and cap of `pp.pol`**, and digSh = 8, tabS = 4,
famF = 24. It says which numbers are handed to the head's check, not that the check enforces them.
-/
theorem HeadShapeOfSettings.hS_of_settingsO {o : Nat → ByteArray → ByteArray}
    {pol KL : ByteArray} {layout : Option ByteArray}
    {X : OnBytes.Model.Verify.Public} {pp : Inst.Model.ScalesAndPolicy}
    (hX : publicOfO o pol KL layout = .ok X)
    (h : OnBytes.Flat.settingsAtRef pol KL = .ok pp) :
    X.hS.clipC = pp.pol.C ∧ X.hS.theta = pp.pol.theta ∧ X.hS.cap = pp.pol.cap ∧
      X.hS.digSh = 8 ∧ X.hS.tabS = 4 ∧ X.hS.famF = 24 := by
  obtain ⟨S, hS, h8, h4, hF, hp⟩ := settingsAtRef_lines h
  have e : X.P = S := by
    have := (publicOfO_scan hX).symm.trans hS
    exact Except.ok.inj this
  rw [(FoPublic.publicOf_cutO pol KL layout X hX).2.1, hp]
  show X.P.h.clipC = _ ∧ X.P.h.theta = _ ∧ X.P.h.cap = _ ∧ X.P.h.digSh = 8 ∧
    X.P.h.tabS = 4 ∧ X.P.h.famF = 24
  rw [e]
  exact ⟨rfl, rfl, rfl, h8, h4, hF⟩

end

/-- At the second hash function itself the twin says what the library's statement says. -/
theorem row_glue_plan_AO_older :
    GlueRows.row_glue_plan_AO OnBytes.secondHashFunction ↔ OnBytes.Tie.Pv.Tail.GlueRows.row_glue_plan_A := by
  unfold GlueRows.row_glue_plan_AO OnBytes.Tie.Pv.Tail.GlueRows.row_glue_plan_A
  simp only [publicOfO_older]

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.PublicCore.public_of_coreO
#print axioms VerifiableInference.PlanWritten.HeadL5Grp.scalesHeld_of_publicO
#print axioms VerifiableInference.PlanWritten.HeadL5Grp.scales_of_publicO
#print axioms VerifiableInference.PlanWritten.FormsKeysLawP.shape_of_publicO
#print axioms VerifiableInference.PlanWritten.Lane5AttPub.label_publicO
#print axioms VerifiableInference.PlanWritten.Lane5AttPub.att_publicO
#print axioms VerifiableInference.PlanWritten.PublicCore.eleven_of_coreO
#print axioms VerifiableInference.PlanWritten.FoPublic.publicOf_cutO
#print axioms VerifiableInference.PlanWritten.FoPublicA.public_AO
#print axioms VerifiableInference.PlanWritten.HeadShapeOfSettings.hS_of_settingsO
#print axioms VerifiableInference.PlanWritten.row_glue_plan_AO_older
