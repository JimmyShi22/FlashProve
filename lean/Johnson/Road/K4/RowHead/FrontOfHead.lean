-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/RowHead/FrontOfHead.lean: FROM A FACT AT THE TWINS WITH FREE LETTERS TO THE SAME
FACT AT WHAT publicOf RETURNS, IN SCOPE AND UNDER THE HEAD. Statements with their proofs: inversions
and calls; nothing is evaluated.

  `polLayout_inv`: Verify.polLayout pol = .ok (P, y) ⟹ Layer.layout (layerShape P) P.polCalls = .ok
    y.
  **`withPlans_public`**: X.P = Pv v · every step of publicOf's text in X's own fields
    (`PublicSteps`, Johnson/Desc/Ok/PlanWritten/PublicAtSteps.lean) · withPlans v pub sc rope f =
    true AT ALL pub sc rope ⟹ f X.layers X.G = true.
  `FrontFree`: THE ONE CLOSED FACT THAT IS ASKED: at all v pub sc rope: the listing "front" returns
  at the plan's value at the groups 0 and 1. A PROPOSITION, NOT SHOWN HERE.
  **`front_of_head`**: FrontFree · the head ⟹ the same at the head's own public record.

Limits. FrontFree IS A PREMISE. K04_law, the law of K4's sub-protocol itself, IS NOT PROVED. Nothing
on soundness.
-/
import Johnson.Road.K4.RowHead.Inversions
import Johnson.Road.K4.Total.PlanMemberDefs
import Johnson.Desc.Ok.PlanWritten.PublicAtSteps
import Johnson.Goal.Meaning.ScopeScanTies
import Johnson.P5J.MgAtAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model
open OnBytes.Road (ok_of_bind)
open OnBytes.Desc.First.K4.Total (frontB)
open VerifiableInference.PlanWritten (PublicSteps publicSteps_of)
open OnBytes.Maker (WholeD)

theorem polLayout_inv {pol : ByteArray} {P : PolScan} {y : Layer.Lay}
    (h : Verify.polLayout pol = .ok (P, y)) :
    Layer.layout (Verify.layerShape P) P.polCalls = .ok y := by
  unfold Verify.polLayout at h
  obtain ⟨P', _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨y', hy, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨_, _, h⟩ := ok_of_bind h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  exact hy

/-- **A fact at the twins with free letters is a fact at what publicOf returns.** -/
theorem withPlans_public {pol KL : ByteArray} {X : Verify.Public} {v : VerifierAndGoals.FreeLines}
    (hP : X.P = Pv v) (C : PublicSteps pol KL X) (f : Layer.Pub → Array Layer.HPlan2 → Bool)
    (h : ∀ pub sc rope, withPlans v pub sc rope f = true) : f X.layers X.G = true := by
  have hl := polLayout_inv C.layout
  rw [hP] at hl
  obtain ⟨y0, fo, pub, kbm, a, b, c, e⟩ := layout_inv (pc := VerifierAndGoals.Lines.callsRef) hl
  have H := h pub X.layers.sc X.layers.rope
  unfold withPlans at H
  have H1 := onOk_ok H a
  have H2 := onOk_ok H1 b
  have H3 := onOk_ok H2 c
  have w := C.wsLay
  rw [hP, e] at w
  have H4 := onOk_ok H3 w
  have l := C.layers
  rw [hP, e] at l
  have H5 := onOk_ok H4 l
  exact onOk_ok H5 C.plans

/-- **The one closed fact that is asked.** -/
def FrontFree : Prop :=
  ∀ (v : VerifierAndGoals.FreeLines) (pub : Array ℕ) (sc : Layer.Scales) (rope : Array ℕ),
    withPlans v pub sc rope (fun L G => (List.range 2).all fun g => (G[g]?).any fun hp =>
      frontB false L hp g L.y.fo) = true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

/-- **Under the head: the listing "front" returns at the plan's value at the groups 0 and 1.** -/
theorem front_of_head (FF : FrontFree) (hA : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀) :
    ((List.range 2).all fun g => ((P5J.At.X Zp).G[g]?).any fun hp =>
      frontB false (P5J.At.X Zp).layers hp g (P5J.At.X Zp).layers.y.fo) = true :=
  withPlans_public (OnBytes.Road.Hd.scan_of_scope hA.scope hA.reads hA.pubOne)
    (publicSteps_of hA.pubOne) _ (FF _)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.polLayout_inv
#print axioms OnBytes.Road.K4.withPlans_public
#print axioms OnBytes.Road.K4.front_of_head
