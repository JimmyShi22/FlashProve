-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/PlanesAtAll.lean: THE END OF THE PREMISE hPl' OF THE LAW ON THE SUB-PROTOCOL K1
(PlanesLeft4 inside the fence at the output head's reads' place), AT THE CLOSED CONSTANT
(`hA.𝔇`, Johnson/P5J/MgAtAll.lean): `planesLeft4_at342` (ArmPlanesHostAt.lean, this folder) called
there, with its sentences on public data paid under the head or moved to tests with code.
Definitions (two tests with code) and statements with their proofs; nothing is evaluated.

  `hLen_of_shape`   **hLen IS A THEOREM** wherever the public parameters are what the reader of the
      public files returns and hShape holds: by the library's `public_planeMatHB`, as in
      `k6_numbers` (Johnson/Desc/Kinds/Law/HeadPlanesNumbers.lean): the planes' matrix has
      2 ^ lmbH rows and at least as many columns as the planes of the head's layout's own shape
  `hTh_atAll`   hTh from the test `readsWideB` (HeadNumbersAtAll.lean, this folder)
  `labPB`, `hLabP_atAll`   hLabP FROM ONE TEST WITH CODE on the planner's list of segments and the
      public parameters
  `shapeHB`, `hShape_of`   hShape FROM ONE TEST WITH CODE on the public parameters: the two shapes
      have one view (`forestView`, Johnson/Desc/Ok/PlanWritten/XShape.lean, which takes every field)
  `labP_rejects`, `shapeH_accepts_none`   `labPB` rejects at an empty list of segments (weak).
      `shapeHB` ACCEPTS WHERE THE LOOKUP HAS NO PLACE OR NO SHAPE, as hShape's own text does
  `planesLeft4_atAll`   **PlanesLeft4 inside the fence, at the constant**: from four tests with code
      (readsArrB · readsWideB · labPB · shapeHB) and PlanesLeft6 (three clauses on the state in
      front; none reads the witness), at num6 := `At.num Zp` · lay6 := `At.layout Zp`

What is not claimed. That the tests accept at any files. PlanesLeft6. No member of the head hA.
Nothing on soundness.

-/
import Johnson.Desc.K1.Law.ArmPlanesHostAt
import Johnson.Desc.K1.Law.HeadNumbersAtAll
import Johnson.Desc.Ok.PlanWritten.XShapeLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1

open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Maker (WholeD)
open VerifiableInference.Desc (Block Chain Strs)
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.Sound (MsgT CellsQ mgBase seatTab)
open VerifiableInference.Desc.K12.Door (K12Data)
open VerifiableInference.Desc.Kinds.Head.Law (p8K6 readsOf)
open VerifiableInference.PlanWritten (forestView forestView_inj sameForestV sameForestV_iff)
open _root_.Desc.K14.Law (seatZ secondAt)
open OnBytes.Params (Rounds)
open ProofFile (Cl)
open IM (Open)

/-- **hLen**, from hShape, at every return of the reader of the public files. -/
theorem hLen_of_shape {pol KL : ByteArray} {lay : Option ByteArray} {X : Verify.Public}
    (hX : Verify.publicOf pol KL lay = .ok X)
    (hShape : ∀ p h, First.Look.placeAt X 24 false = some p → p.shape = some h → h = X.HLy.fs) :
    ∀ p h, First.Look.placeAt X 24 false = some p → p.shape = some h →
      h.NC * 2 ^ (h.kT + 5 - (p8K6 X 24).h.lmbH) ≤
        ((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).k *
          (((p8K6 X 24).hp.tl.mats.getD ((p8K6 X 24).h.NHf + 1 + 1) {}).m /
            2 ^ (p8K6 X 24).h.lmbH) := by
  intro p h hp hs
  have hB := _root_.Fo.PlaneMat.public_planeMatHB hX
  simp only [_root_.Fo.planeMatHB, Bool.and_eq_true, decide_eq_true_eq] at hB
  have hm := hB.1.2
  have hk : X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH) ≤
      (X.H.tl.mats.getD (X.hS.NHf + 1 + 1) {}).k := hB.2
  rw [hShape p h hp hs]
  show X.HLy.fs.NC * 2 ^ (X.HLy.fs.kT + 5 - X.hS.lmbH) ≤
    (X.H.tl.mats.getD (X.hS.NHf + 1 + 1) {}).k *
      ((X.H.tl.mats.getD (X.hS.NHf + 1 + 1) {}).m / 2 ^ X.hS.lmbH)
  rw [hm, Nat.mul_one]
  exact hk

/-- A test: segment 24's list of arrays names the planes' matrix's symbol array by the matrix's
label. -/
def labPB (built : Array Stages.LinkH) (X : Verify.Public) : Bool :=
  decide (((built.map (·.arrayOf)).getD 24 #[])[X.H.tl.gtTree.getD (X.hS.NHf + 2) 0]? =
    some (_root_.Meaning.ownerK (_root_.Meaning.labAt X 24 (X.hS.NHf + 2)),
      _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt X 24 (X.hS.NHf + 2)))))

/-- The negative test, weak: at an empty list of segments. -/
theorem labP_rejects (X : Verify.Public) : labPB #[] X = false := by
  unfold labPB
  simp

/-- A test: the shape of the lookup on the calls at segment 24 has the view of the head's layout's
own. -/
def shapeHB (X : Verify.Public) : Bool :=
  ((First.Look.placeAt X 24 false).bind (·.shape)).all fun h =>
    sameForestV (forestView h) (forestView X.HLy.fs)

theorem hShape_of {X : Verify.Public} (h : shapeHB X = true) :
    ∀ p h, First.Look.placeAt X 24 false = some p → p.shape = some h → h = X.HLy.fs := by
  intro p h' hp hs
  unfold shapeHB at h
  rw [hp, Option.bind_some, hs, Option.all_some] at h
  exact forestView_inj ((sameForestV_iff _ _).1 h)

/-- Where the lookup has no place it accepts, for want of a case. -/
theorem shapeH_accepts_none {X : Verify.Public} (h : First.Look.placeAt X 24 false = none) :
    shapeHB X = true := by
  unfold shapeHB
  rw [h]
  rfl

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x₀ : First.Look.Place} {Bs : ProofFile.PureBase} {base₀ : List (Block S Cl)}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
include hA

theorem hTh_atAll (h : readsWideB Zp.made.p.built.links (P5J.At.X Zp) = true) :
    ∃ t, (hA.𝔇.pubD.dS.trees 24)[readsOf (P5J.At.X Zp)]? = some t := by
  unfold readsWideB at h
  cases e : (First.FillSent.treesAt Zp.made.p.built.links 24)[readsOf (P5J.At.X Zp)]? with
  | none =>
    rw [e] at h
    cases h
  | some t => exact ⟨t, e⟩

theorem hLabP_atAll (h : labPB Zp.made.p.built.links (P5J.At.X Zp) = true) :
    (hA.𝔇.pubD.d3.arrayOf.getD 24 #[])[(P5J.At.X Zp).H.tl.gtTree.getD
        ((P5J.At.X Zp).hS.NHf + 2) 0]? =
      some (_root_.Meaning.ownerK (_root_.Meaning.labAt (P5J.At.X Zp) 24
          ((P5J.At.X Zp).hS.NHf + 2)),
        _root_.Meaning.nameOf (_root_.Meaning.ownerA (_root_.Meaning.labAt (P5J.At.X Zp) 24
          ((P5J.At.X Zp).hS.NHf + 2)))) :=
  of_decide_eq_true h

/-- **PlanesLeft4 inside the fence, at the constant.** -/
theorem planesLeft4_atAll
    (O : Open OnBytes.secondHashFunction Zl.pol Zl.lay Zl.KL (P5J.F0T OnBytes.secondHashFunction Zp Np cF) Zp Bs base₀ cF
      (seatZ Zp Np) (secondAt Zp Np))
    (hArr : readsArrB Zp.made.p.built.links (P5J.At.X Zp) = true)
    (hWide : readsWideB Zp.made.p.built.links (P5J.At.X Zp) = true)
    (hLab : labPB Zp.made.p.built.links (P5J.At.X Zp) = true)
    (hSh : shapeHB (P5J.At.X Zp) = true) (dk : K12Data) (J : S → Prop) (aN : ℕ)
    (R₁ R₂ R₃ : Rounds) {X : Stages.LinkH} {arrs : Option (List ℕ)} {x x' : ProofFile.InstPub × S}
    {y y' : Strs}
    {w : Wit (CellsQ OnBytes.Flat.numsFull.rows (P5J.colsAt OnBytes.Flat.numsFull)) P5J.At.Tok MsgT}
    {p : ℕ × String} {A B : K9.Part}
    (Fc : ReadsFence hA.𝔇 dk mgBase J Zp Bs aN R₁ R₂ R₃ cF 24 X arrs x x' y y' w p A B)
    (L : PlanesLeft6 (P5J.At.X Zp) (hA.𝔇.N.sent 24 0) x.2 A hA.𝔇.arr hA.𝔇.N (P5J.At.num Zp)
      (P5J.At.layout Zp)) :
    PlanesLeft4 (P5J.At.X Zp) (hA.𝔇.N.sent 24 0) (hA.𝔇.N.group 24) x.2 A B
      (seatTab hA.𝔇.cs hA.𝔇.arr hA.𝔇.ms w) := by
  obtain ⟨cU, hU⟩ := hU_atAll hA hArr
  exact planesLeft4_at342 hA.𝔇 dk J O O.W aN R₁ R₂ R₃ cU (P5J.At.num Zp) (P5J.At.layout Zp)
    hA.plan.laid hU (hKw_atAll hA hWide) (hTh_atAll hA hWide) (hShape_of hSh)
    (hLabP_atAll hA hLab) (hLen_of_shape hA.pubOne (hShape_of hSh)) Fc L

end

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.hLen_of_shape
#print axioms VerifiableInference.Desc.K1.labP_rejects
#print axioms VerifiableInference.Desc.K1.hShape_of
#print axioms VerifiableInference.Desc.K1.shapeH_accepts_none
#print axioms VerifiableInference.Desc.K1.hTh_atAll
#print axioms VerifiableInference.Desc.K1.hLabP_atAll
#print axioms VerifiableInference.Desc.K1.planesLeft4_atAll
