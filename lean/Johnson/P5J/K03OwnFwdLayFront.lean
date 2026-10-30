-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OwnFwdLayFront.lean: THE LOOKUP ARGUMENTS ON THE DIGITS AT THE TWELVE LAYERS'
SEGMENTS: WHAT THE SEGMENT's READERS ANSWER AT "front" AND "back" IN FRONT OF AN ACCEPT THEY ANSWER
BEHIND IT (`Fwd`), AT THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA`, A VALUE OF `Free` AND ITS THREE
EQUATIONS: **WITHOUT THE TABLE's
PROMISE BEHIND AMONG ITS HANDS.** The sister of `k03_fwd_lay` (Johnson/P5J/K03OwnFwdLayAt.lean),
whose text it is but for that hand: for a spender that has no promise behind: the item "own" of
hForms (Johnson/P5J/K03OwnItLayAt.lean). One theorem: `k03_fwd_lay_front`: ONE CALL of the lookups'
authors' `hOwn_of_below_holes` (Johnson/Desc/Sound/MgAt/K3DigitsStaysBelowFront.lean), with the
named lemmas of the sister's file: `k03_wins_at`, `k03_states_lay`; `k03_link_some`,
`k03_pieceAt_dig`, `k03_hlink`.

Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03OwnFwdLayAt
import Johnson.Desc.Sound.MgAt.K3DigitsStaysBelowFront

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

set_option maxHeartbeats 4000000 in
/-- **Fwd AT THE TWELVE LAYERS' DIGITS, WITHOUT THE PROMISE BEHIND.** -/
theorem k03_fwd_lay_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) : ∀ g < 12,
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g) true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K (2 * g) true) u →
      h.toAtMg.rch (k3K (2 * g) true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(2, "front"), (2, "back")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd (2 * g)) p.1 p.2 u.1 v.1 := by
  intro g hg b' hb'
  have hl : 2 * g < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g]? = some ModelPart.layers := by
    have h0 := List.all_eq_true.1 linksLayFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  obtain ⟨pK, hSt⟩ := k03_states_lay h hg Lk hLk
  exact hOwn_of_below_holes (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Lk K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place (2 * g) true) b' pK
    (mH := headLink (At.X Zp)) hb' (Pc.planOk (2 * g) hl true b' hb') rfl
    (k03_pieceAt_dig h.toAtMg (2 * g))
    (by
      show (if (true : Bool) = true then 6 else 1) + (if 2 * g = 24 then 1 else 0) + 1 = 7
      rw [if_pos rfl, if_neg (by omega)])
    rfl hl hsub
    (by
      rw [h24]
      simp only [beq_eq_false_iff_ne, ne_eq]
      omega)
    (k03_hlink h (2 * g) Lk hLk) (fun z u _ hr _ => k03_wins_at h hg z u hr) hSt

end P5J

#print axioms P5J.k03_fwd_lay_front
