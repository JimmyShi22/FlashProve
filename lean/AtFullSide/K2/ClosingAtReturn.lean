-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/ClosingAtReturn.lean: the closing's test at each switch, spoken at a return of the maker:
at the public part and the ground that the return holds.

  closing_at_return   closing_at_head at A.Z and A.G, from the library's head and the return alone

Limits. The limits of closing_at_head stand. That the list of switches holds a place at each link
is not said here.
-/
import Johnson.Desc.ProofFile.Honest.K2.Law.ClosingAtHead
import Johnson.Desc.ProofFile.Honest.AtPureLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace AtFullSide.K2.Term
open ProofFile.Honest
open ProofFile.Honest.K2
open ProofFile.Honest.K2.Law

/-- **The closing's test at each switch, at the return's public part and ground.** -/
theorem closing_at_return {Z : VerifierAndGoals.PublicFiles} {D : OnBytes.Maker.WholeD} {r : LPFD.Full.RunPF}
    {Zp : ProofFile.Pub} {Np : H2U.Places4}
    {cF : VerifiableInference.Desc.Chain P5J.TS ProofFile.Cl}
    {x : VerifiableInference.Desc.First.Look.Place} {W₀ Rc Tr X₀ X : Type}
    {P : OnlineProverParts W₀ Rc Tr X₀ X} {A : OnlineProverWithDescription W₀ Rc Tr X₀ X}
    (h : P5J.AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (hA : onlineProverFromPublicFiles OnBytes.secondHashFunction Z.pol Z.lay Z.KL P = .ok A) :
    ∀ p ∈ switchPlaces A.Z A.G,
      closingOk freshTable ((segmentsOf A.Z A.G).take p.link) p = true := by
  obtain ⟨Bs, base, O⟩ := h.toAtMg.laid.opened
  obtain ⟨e₁, e₂, -⟩ := atPure_ok hA
  have hZ : A.Z = Zp := Except.ok.inj (e₁.symm.trans O.pub)
  have hG : A.G = Bs.G₀ := by
    rw [hZ] at e₂
    exact Option.some.inj (e₂.symm.trans O.blank)
  rw [hZ, hG]
  exact closing_at_head h.toAtMg O

end AtFullSide.K2.Term

#print axioms AtFullSide.K2.Term.closing_at_return
