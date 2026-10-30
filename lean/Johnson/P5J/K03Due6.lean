-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P5J/K03Due6.lean: the kind "lookup" (K3): WHAT IS STILL DUE FOR THE KIND's NAMED CONDITION
AT THE CLOSED CONSTANT, SIXTH COUNT: `k03_cond_due6` : `h.K3Cond 𝔏`
(Johnson/Goal/Skeleton/Kinds/K3Bridge.lean), by one call of `k03_cond_due5`
(Johnson/P5J/K03Due5.lean, which does not turn). FROM the head, the filling 𝔏, its three equations
q₁ q₂ q₃ and FOUR BINDERS, ALL WHERE THE DIGITS' PIECE ACCEPTS; NO CLOSED TEST IS LEFT:
    Io: the public test at the item formsIn l (3 + shift sub) "own" holds behind the accept (25);
    Ip: the like at formsIn l (2 + shift sub) "planes", off the layers' segments (13);
    Ij: the like at formsIn l (joinAt sub) "join", off the layers' segments (13);
      (each `DigItemR`: three binders of `hForms_dig_mgAll`, under the field's own fenced hands)
    Rd: rides at the 25 digits' places.
s₀ and z₀ are idle letters of the condition's own text.

PAID HERE BEYOND `k03_cond_due5`: hcalls (Johnson/P5J/K03HeadCallsAt.lean: one call of
`callsC_at_head_all`) · `DigFormsR` but for the three items (Johnson/P5J/K03DigFormsAt.lean,
over `hForms_dig_mgAll` and `forms_of_live`); that the digits' reader answers at
every l < 25: `K3PlanR.digB`.

Limits: the four are premises; no member is known; Rd is a conjunct of the kind's own conclusion.
"From the head" moves tests into the head; whether there is a head is not said here. At secondHashFunction
alone. Nothing on soundness by itself; nothing on hiding.


-/
import Johnson.P5J.K03Due5
import Johnson.P5J.K03HeadCallsAt
import Johnson.P5J.K03DigFormsAt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart shift joinAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

set_option maxHeartbeats 4000000 in
/-- **WHAT IS STILL DUE, SIXTH COUNT.** -/
theorem k03_cond_due6 (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (s₀ : VerifiableInference.Desc.First.S) (z₀ : ProofFile.InstPub)
    (Io : ∀ l < 25, ∀ sub, linksFull[l]? = some sub →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
          (.formsIn l (3 + shift sub) "own"))
    (Ip : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → sub ≠ .layers →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
          (.formsIn l (2 + shift sub) "planes"))
    (Ij : ∀ l < 25, ∀ sub, linksFull[l]? = some sub → sub ≠ .layers →
      ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch l q b'
          (.formsIn l (joinAt sub) "join"))
    (Rd : ∀ l < 25, ∀ q, (h.toAtMg.row 𝔏)[k3K l true]? = some q →
      ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l true = some b' →
        RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
          (k3K l true) q b') :
    h.K3Cond 𝔏 := by
  letI := k3SizesAt (At.X Zp)
  letI := k3PolicyAt (At.X Zp)
  have P := k03_planR_at h (k03_digRow_at h.toAtMg) (k03_headRow_at h.toAtMg)
  refine k03_cond_due5 h 𝔏 q₁ q₂ q₃ s₀ z₀ (k03_hcalls_head h) ?_ Rd
  intro l hl sub hsub q hq b' hb
  obtain ⟨y, tl, hy, -⟩ := P.digB (fun _ => 0) l hl
  exact k03_digForms h 𝔏 q₁ q₂ q₃ hl hsub hy q hq b' hb (Io l hl sub hsub q hq b' hb)
    (fun hs => Ip l hl sub hsub hs q hq b' hb) (fun hs => Ij l hl sub hsub hs q hq b' hb)

end P5J

#print axioms P5J.k03_cond_due6
