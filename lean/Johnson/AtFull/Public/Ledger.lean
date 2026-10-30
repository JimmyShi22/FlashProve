-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/AtFull/Public/Ledger.lean: THE LEDGER OF publicOfO: publicOfO_of_parts: where each of its
  steps returns, publicOfO returns, and at which value:
twenty-two named premises. IT PAYS NO PREMISE. The Lean text is that of an earlier working file of
  this project, which is not in this repository (sha256 295d154a…), from its import line on, to the
letter. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAt

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4.Trial.AttL2
open OnBytes OnBytes.Model OnBytes.Model.Verify
open VerifiableInference.PlanWritten

/-- The number that names group g's matrix qa: publicOfO's own term (PublicAt.lean:150). -/
def mqOf (y : Layer.Lay) (g : Nat) : Nat :=
  (((Layer.tailsOf y).getD g {}).mats.getD (Layer.matIx y).iQA {}).aId

/-- What attentionOwners and crossPlans read of the layers' plans (PublicAt.lean:156). -/
def seenGOf (G : Array Layer.HPlan2) : Array SubPlan := G.map fun O => (⟨O.tl, O.Fp, O.Tp⟩ :
    SubPlan)

/-- The attention's plans with the smallness tests that attentionOwners returns (PublicAt.lean:159).
  -/
def AOf (A0 : Array OnBytes.Attention.Plan) (seenA : Array SubPlan) : Array OnBytes.Attention.Plan
    :=
  A0.zipWith (fun X s => { X with seam := { X.seam with tl := s.tl } }) seenA

/-- **publicOfO returns, and what.** -/
theorem publicOfO_of_parts {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {P : PolScan} {y : Layer.Lay} {sc : Layer.Scales} {hp : ByteArray}
    {wsLay : WsLay} {rope : Array Nat} {HLy : Head.HL} {c : OnBytes.Attention.Config} {layers :
        Layer.Pub}
    {G : Array Layer.HPlan2} {seenA : Array SubPlan} {owner : Head.Owner} {H : Head.HPlanH2}
    (h3 : y.h.p3 = true) (h4 : y.h.p4 = true)
    (p1 : polLayout pol = .ok (P, y))
    (p2 : Layer.scalesOf y.h (fileWords KL) = .ok sc)
    (p3 : Layer.scalesHeld y.h sc = .ok ())
    (p4 : tableHeldO o P .silu y.silu = .ok ())
    (p5 : tableHeldO o P .sigmoid y.fs = .ok ())
    (p6 : Layer.noWrap y.h sc y.dq = .ok ())
    (p7 : hParO o pol KL layout = .ok hp)
    (p8 : Layer.weightWidthsHeld y.h y.kinds = .ok ())
    (p8' : Head.vocabulary (headShape P y) = .ok ())
    (p9 : wsLayOf (weightShape P y) y.h.p3 P.lkW = .ok wsLay)
    (p10 : Layer.ropeOf y.h = .ok rope)
    (p11 : tableHeldO o P .rope rope = .ok ())
    (p13 : Head.layout (headShape P y) y.tauFC = .ok HLy)
    (p14 : Attention.configO o P y sc (mqOf y) = .ok c)
    (p15 : Layer.Pub.of y sc rope wsLay P.h.V #[] P.settings = .ok layers)
    (p16 : Layer.plansG layers = .ok G)
    (p17 : attentionOwners y.h.p4 y.NGr (seenGOf G)
      (c.plans.map fun X => ⟨X.seam.tl, X.seam.Fp, X.seam.Tp⟩) = .ok seenA)
    (p18 : ownerOf y G = .ok owner)
    (p19 : Head.planH2 P.settings (headShape P y) HLy (borderOf y) owner y.NGr P.lkW = .ok H)
    (p20 : crossPlans (G.size - 1 + (AOf c.plans seenA).size + 1) y.NGr y.h.p4 (Layer.tailsOf y)
        (seenGOf G)
      seenA ⟨H.tl, H.Fp, H.Tp⟩ = .ok ()) :
    publicOfO o pol KL layout = .ok
      { P := P,
        digests := { hCalls := callsDigestO o "call" y.calls.toList, hCallsA := c.hCallsA,
                     hCallsH := callsDigestO o "callH" HLy.calls.toList },
        layers := layers, hS := headShape P y, HLy := HLy, G := G, A := AOf c.plans seenA,
        H := { H with Fp := H.Fp.trimL }, owner := owner } := by
  unfold mqOf at p14
  unfold seenGOf at p17 p20
  unfold AOf at p20
  rw [h3] at p9
  rw [h4] at p17 p20
  unfold publicOfO AOf
  simp only [p1, p2, p3, p4, p5, p6, p7, p8, p8', p9, p10, p11, p13, p14, p15, p16, p17, p18, p19,
      p20, h3, h4,
    bind, Except.bind, pure, Except.pure, if_true]

end OnBytes.Road.K4.Trial.AttL2

#print axioms OnBytes.Road.K4.Trial.AttL2.publicOfO_of_parts
