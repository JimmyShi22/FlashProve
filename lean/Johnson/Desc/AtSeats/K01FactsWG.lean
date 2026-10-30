-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/AtSeats/K01FactsWG.lean: THE TWO TIES OF KIND K1 (at W's commitment and at the first
segment's opening): THEIR PREMISES ALONG REACHED STATES, W_hFacts AND G_hFacts, AT THE
CLOSED CONSTANT (P5J.mgAtAll), IN THE BINDERS' OWN TYPES (Johnson/Desc/AtSeats/K01KindAtThree.lean
[not in this library]), BY CALLS.
  W_hFacts_atAll   factsK13_reached_of (Johnson/Desc/AtSeats/K01FactsOf.lean) at the tie's dW; its
                   codes are the constant's by W_hcs_atAll (Johnson/Desc/K1/Law/TiesAtAll.lean)
  G_hFacts_atAll   FactsG's four fields: factsK13_reached_of at dG · liveIs_reached · front_at_rchAt
                   (Johnson/Desc/AtSeats/FrontAtRch.lean) · mgAll_pubP_said
                   (Johnson/Desc/Sound/MgBase.lean)
Laid: Dm := hA.𝔇 · dk := d12Full · Rch := "reached, with a typed public part".
What is not claimed. That hA or hP1 can be met: NO MEMBER. Nothing on soundness.

-/
import Johnson.Desc.AtSeats.K01FactsOf
import Johnson.Desc.AtSeats.FrontAtRch
import Johnson.Desc.AtSeats.TieWAt9
import Johnson.Desc.AtSeats.TieGAt9
import Johnson.Desc.K1.Law.TiesAtAll
import Johnson.Desc.K13.Law.BridgeG

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K13.Law

open OnBytes OnBytes.Slice OnBytes.Maker OnBytes.Flat
open VerifiableInference.Desc (Chain)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open ProofFile (Cl)
open Johnson.Desc.First.Walk.Tied (RchPub rchAt_raw)
open VerifiableInference.PlanWritten (madePinnedAt)
open VerifiableInference.Desc.K1 (dW dG W_hcs_atAll)

section
variable {Zl : VerifierAndGoals.PublicFiles} {D : WholeD} {r₀ : LPFD.Full.RunPF} {Zp : ProofFile.Pub}
  {Np : H2U.Places4} {cF : Chain S Cl} {x₀ : First.Look.Place}
  (hA : P5J.AtMgA OnBytes.secondHashFunction Zl D r₀ Zp Np cF x₀)
  (hP1 : madePinnedAt Zp.p.X.P Zp.p.chains.made Zp.first Zp.made = true)
include hA hP1

/-- **W_hFacts at the constant.** -/
theorem W_hFacts_atAll {nR : ℕ} (W_msg : Array OracleNotice)
    (W_rwD : ProofFile.InstPub × S →
      VerifiableInference.Desc.Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT →
      Wit GE nR (K13.whereOf Zp).lin.kCol) :
    ∀ j a, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str)
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j a → a.1.2.failed = none →
      FactsK13 (dW Zp W_msg hA.𝔇.shape hA.𝔇.layout hA.𝔇.N W_rwD) d12Full (mgAll hA.𝔇 mgBase) a.1 :=
  fun j a hr hm => factsK13_reached_of hA hP1 _ (W_hcs_atAll hA W_msg) rfl rfl j a.1
    (rchAt_raw hr.1) hm

/-- **G_hFacts at the constant.** -/
theorem G_hFacts_atAll {nR : ℕ}
    (G_rwD : ProofFile.InstPub × S →
      VerifiableInference.Desc.Wit (P5J.CellsM numsFull) P5J.At.Tok MsgT →
      Wit GE nR (K13.whereOf Zp).lin.kCol) :
    ∀ j a, RchPub (Str := (frameAt (D.at frS.P.T.a) (allOf (D.at frS.P.T.a))
        (D.at frS.P.T.a).key₁ 0).E.Str)
      (P5J.F0T OnBytes.secondHashFunction Zp Np cF) typedPub j a → j = 2 ∨ j = 2 + 1 →
      a.1.2.failed = none →
      FactsG (dG Zp hA.𝔇.pubD.cs hA.𝔇.shape hA.𝔇.layout hA.𝔇.N G_rwD) d12Full hA.𝔇.pubD.d3
        (mgAll hA.𝔇 mgBase) a.1 := by
  intro j a hr hj hm
  obtain ⟨Bs, base, O⟩ := hA.laid.opened
  exact ⟨factsK13_reached_of hA hP1 _ rfl rfl rfl j a.1 (rchAt_raw hr.1) hm,
    liveIs_reached hA _ rfl rfl j a.1 (rchAt_raw hr.1) hm,
    HashBuild.front_at_rchAt hA.scope hA.reads O j a hr.1 hj hm,
    mgAll_pubP_said hA.𝔇 _ a.1 (by decide)⟩

end

end VerifiableInference.Desc.K13.Law

#print axioms VerifiableInference.Desc.K13.Law.W_hFacts_atAll
#print axioms VerifiableInference.Desc.K13.Law.G_hFacts_atAll
