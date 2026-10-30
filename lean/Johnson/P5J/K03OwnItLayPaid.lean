-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OwnItLayPaid.lean: THE LOOKUP ARGUMENTS ON THE DIGITS AT THE TWELVE LAYERS' SEGMENTS:
THE ITEM "own" OF hForms (the premise hOwnIt of `k03_digForms`, Johnson/P5J/K03DigFormsAt.lean), IN
ITS OWN TEXT, AT THE CLOSED CONSTANT, **UNDER THE HEAD `AtMgA`, A VALUE OF `Free` AND ITS THREE
EQUATIONS.** One theorem:
`k03_ownIt_lay_paid`: `k03_ownIt_lay` (Johnson/P5J/K03OwnItLayAt.lean) with its one named premise
paid by `k03_fwd_lay_front` (Johnson/P5J/K03OwnFwdLayFront.lean).

Limits. The twelve layers' segments alone: attention's twelve and the head's are not here. The head
`AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side library
AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03OwnItLayAt
import Johnson.P5J.K03OwnFwdLayFront

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S ModelPart shift)
open VerifiableInference.Reads.Pass (Fwd)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **THE ITEM "own" AT THE TWELVE LAYERS' DIGITS, FROM THE HEAD ALONE.** -/
theorem k03_ownIt_lay_paid (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    {g : ℕ} (hg : g < 12)
    (q) (hq : (h.toAtMg.row 𝔏)[k3K (2 * g) true]? = some q)
    (b') (hb : k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b') :
    DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (2 * g) q b'
      (.formsIn (2 * g) (3 + shift .layers) "own") :=
  k03_ownIt_lay h 𝔏 q₁ q₂ q₃ hg q hq b' hb (k03_fwd_lay_front h 𝔏 q₁ q₂ q₃ g hg b' hb)

end P5J

#print axioms P5J.k03_ownIt_lay_paid
