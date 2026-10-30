-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03JoinItAttAt.lean: THE KIND "LOOKUP" (K3), AT THE DIGITS' LOOKUPS OF THE TWELVE
ATTENTION SEGMENTS, AT THE COMPOSED MEANING's OWN PARAMETERS: THE COMPOSED MEANING's PUBLIC TEST AT
THE KEPT ITEM formsIn (2 g + 1) 2 "join" ACCEPTS BEHIND AN ACCEPT OF THE SEATED SUB-PROTOCOL. One
theorem.
  `k03_joinIt_att`: ends in `DigItemR … (.formsIn (2 * g + 1) (joinAt ModelPart.attention) "join")`
    (Johnson/P5J/K03DigFormsAt.lean): the premise hJoinIt of `k03_digForms` and the binder Ij of the
    kind's counts, at attention's twelve.
AN APPLICATION: ONE CALL of `hJoinIt_dig`
(Johnson/Desc/Sound/MgAt/K3DigitsJoinIt.lean) at sub := .attention: its term hrawJ :=
`k03_joinRaw_att` (Johnson/P5J/K03JoinRawAt.lean); its premise at the output head's segment is idle
here (the sort is not the head's). WHAT STAYS A PREMISE: the head AtMgA · the filling with its three
equations.
Limits. Nothing at the output head's segment. At OnBytes.secondHashFunction. The full size alone. Nothing on
soundness.

-/
import Johnson.P5J.K03JoinRawAt
import Johnson.P5J.K03DigFormsAt
import Johnson.P5J.K03RidesDigLeft
import Johnson.Desc.Sound.MgAt.K3DigitsJoinIt

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart joinAt)
open VerifiableInference.Desc.First.Att.P (K05_join_of_open)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

set_option maxHeartbeats 4000000 in
/-- **THE ITEM "join" BEHIND THE DIGITS' ACCEPT, AT ATTENTION's TWELVE.** -/
theorem k03_joinIt_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ g < 12, ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g + 1) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
      DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (2 * g + 1) q b'
        (.formsIn (2 * g + 1) (joinAt ModelPart.attention) "join") := by
  intro g hg q hq b' hb'
  have hl : 2 * g + 1 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨y, tl, hy⟩ := k03_digAt_some h hl
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  obtain ⟨-, A, -, -, -, hA, -⟩ := hT g hg
  rw [hW] at hA
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨Lk, hLk, -⟩ := K05_join_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) (by rw [hW]; exact hA)
  exact hJoinIt_dig (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch Zp.first.codes
    Zp.first.shape rfl hl hsub hy q b' hb' (Pc.planOk (2 * g + 1) hl true b' hb')
    (Pc.back (2 * g + 1) hl true q hq) rfl Lk ((h.laid.linkAt (2 * g + 1)).trans hLk)
    (fun _ => ⟨A, k03_joinRaw_att h g hg A hA Lk hLk⟩) (fun e => nomatch e) (by decide)

end P5J

#print axioms P5J.k03_joinIt_att
