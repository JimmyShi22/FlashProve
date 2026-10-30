-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-



Johnson/Desc/AtSeats/K13KindRowA.lean: KIND K13's ROW FOR THE JOIN, IN THE COUNTED FORM
hA.Kind 𝔏 KindName.K13 (AtMgA.Kind, Johnson/P5J/RowsAtAll.lean), WITH ITS PREMISES ASKED ALONG «REACHED AND TYPED» ALONE, AND TIGHT.
Two points are met here.
(1) A row at bare RchAt asks its facts at untyped public parts too; a bridge carries the END alone. Here the general
    law (k13_law_atThreeT: «reached» a letter) is CALLED AT THE NARROWER RELATION ITSELF:
      typedPub p := ∃ z, p = (LPFD.Full.instanceAsPlainRecord z).pub  ·  RchPub (F0T …) typedPub k a := RchAt (F0T …) k a ∧ typedPub a.1.1
    (Johnson/Top/H0/Walk/ReachPub.lean, with its hand-on handsOn_pub): so the facts are asked along
    that relation alone: the weaker premise; and the end IS the counted form by kindA_iff: no monotonicity is spent.
(2) The shared head's field asks all 25 fields of FoldFacts; the row spends nine tests on the state. Here:
      NineK13 codes shape layout d s   the nine, as one structure: in order (tidy · codes · shape · layout) · pileMasks ·
                                       pileWithin · oneRow · weightsOk · bookInOrder · seatsCarried · msgShapes · bookFits.
    The tenth field of FactsK13 (pubP's silence at the eight names) is paid at the closed base.
  **k13_kindA_tight**  THE ROW's STATEMENT: under hA · q₁ q₂ q₃ · hCapB · hi · hn · hft · hPl · hNine.
What is not claimed. That any premise can be met. No member of h.Kind. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K13KindRow3
import Johnson.Desc.Sound.KindEndA
import Johnson.Top.H0.Walk.ReachPub

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Params OnBytes.Model OnBytes.Slice OnBytes.Maker OnBytes.Flat KObj Iop Run
open OnBytes.Road OnBytes.RunA
open _root_.Run.PQ (CK SgX)
open VerifiableInference.Desc (Block Chain Link FileDescription Place KindName)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart Meaning Numbers start flatPlacesOf endAsks)
open ProofFile (Cl)
open VerifiableInference.Desc.Sound (TiedAtR HandsOn mgAll MgData CellsQ mgBase threeCap)
open Johnson.Desc.First.Walk.Tied (RchAt)

open Johnson.Desc.First.Walk.Tied (handsOn_map)
open VerifiableInference.Desc.Sound (threeCap_ofDesc)

open Johnson.Desc.First.Walk.Tied (RchPub handsOn_pub)
open VerifiableInference.Desc.Sound (threeCap_ofDesc)

/-- The public part is a typed instance's. -/
def typedPub (p : ProofFile.InstPub) : Prop := ∃ z, p = (LPFD.Full.instanceAsPlainRecord z).pub

/-- **The nine tests on the state that the row spends.** -/
structure NineK13 (codes : OnBytes.Codes) (shape : OnBytes.Params.ReqShape) (layout : OnBytes.Params.ReqLayout)
    (d : K12.Door.K12Data) (s : S) : Prop where
  order : inOrderK13 codes shape layout s = true
  masks : pileMasksC s = true
  within : pileWithinC s = true
  oneRow : oneRowC s = true
  weights : First.weightsB s = true
  book : K12.Door.atFirstBook d.ft s = true
  seats : K12.Door.atFirstSeats d.L s = true
  shapes : K12.Door.atFirstShapes d.M s = true
  fits : K12.Door.atFirstFits s = true

/-- **Kind K13's row, counted form, tight.** -/
theorem k13_kindA_tight {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
    {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
    (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
    (𝔏 : P5J.Free numsFull D (P5J.F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (d₁₂ : K12.Door.K12Data) (hCapB : capB hA.𝔇.P13 = true)
    (hi : hA.𝔇.N.index.1 ≤ 1) (hn : 1 ≤ inFront355 cF) (hft : d₁₂.ft = 0)
    (hPl : PlanM3 d₁₂.L d₁₂.M hA.𝔇.ms hA.𝔇.cs hA.𝔇.N)
    (hNine : ∀ j x, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a)) (D.at frS.P.T.a).key₁ 0).E.Str)
        (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j x → x.1.2.failed = none →
      NineK13 hA.𝔇.cs hA.𝔇.shape hA.𝔇.layout d₁₂ x.1.2) :
    hA.Kind 𝔏 KindName.K13 := by
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  have hD : (P5J.F0T OnBytes.secondHashFunction Zp Np cF).data "proof file" = .ok (D.at frS.P.T.a) := by
    rw [P5J.LaidAt.atDepth hA.scope hA.laid]; exact hA.laid.data
  refine (P5J.kindA_iff hA 𝔏 KindName.K13).2 ?_
  exact k13_law_atThreeT hA.scope hA.reads O hD hA.laid.planOk q₁ q₂ q₃ hA.𝔇 rfl d₁₂ 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW
    𝔏.wEnd 𝔏.c₀ P5J.At.tokOf hCapB (counts_atAll hA).1 (counts_atAll hA).2 (hbase_atAll hA hi hn) hft hPl
    (smpReads_atAll hA) (decBlind_atAll hA) (RchPub (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub)
    (fun j x hr hm =>
      have h9 := hNine j x hr hm
      ⟨h9.order, h9.masks, h9.within, h9.oneRow, h9.weights, h9.book, h9.seats, h9.shapes, h9.fits,
        fun q hq => (fillsK13C_base hA.𝔇).quiet q (quietC_of_cA13 q hq) x.1⟩)
    fun _ _ hq => handsOn_pub
      (threeCap_ofDesc 𝔏.e₁ 𝔏.e₂ 𝔏.e₃ 𝔏.dW 𝔏.wEnd hD hA.laid.planOk q₁ q₂ q₃) typedPub hq _

end VerifiableInference.Desc.K13.Law
