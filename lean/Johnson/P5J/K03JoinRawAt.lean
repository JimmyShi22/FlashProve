-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03JoinRawAt.lean: THE KIND "LOOKUP" (K3), AT THE TWELVE ATTENTION SEGMENTS, AT THE
COMPOSED MEANING's OWN PARAMETERS: THE TERM hrawJ OF `join_kept_dig_att`
(Johnson/Desc/Sound/MgAt/K3DigitsFormsJoinAtt.lean), AND A CALL OF THAT THEOREM AT IT. Two theorems.
  `k03_joinRaw_att`: what the link's second sub-protocol states under "join" IS ("join", the
    lookup's own run at the caller's keys): hrawJ's own shape: `K05_join_of_open`
    (Johnson/H2K5R/JoinAtOpen.lean) at the head's own opening. (Johnson/P5J/K03JoinFindAt.lean has
    the same stone in another premise's shape.)
  `k03_join_kept_att`: ONE CALL of `join_kept_dig_att` at these parameters: the composed meaning's
    public test at the kept item formsIn (2 g + 1) 2 "join" passes an accept of the whole seated
    digits' sub-protocol. That file says: "no payer has typechecked against it here": this one has.
WHAT STAYS A PREMISE OF THE SECOND: the head · the filling · on the state in front: the ledger is
there and sized; the part is an attention's; the test accepts there. It stands at the stated
sub-protocol's decision, as that theorem does.
Limits. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03RidesDigAt2
import Johnson.H2K5R.JoinAtOpen
import Johnson.Desc.Sound.MgAt.K3DigitsFormsJoinAtt

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
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.K9 (statesOfLink)
open VerifiableInference.Desc.First.Att.P (keysOfO K05_join_of_open)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

/-- **hrawJ AT THE CONSTANT.** -/
theorem k03_joinRaw_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ g < 12, ∀ A, (At.X Zp).A[g]? = some A → ∀ Lk, cF.links[2 * g + 1]? = some Lk →
    (statesOfLink Lk 2).find? (fun x => x.1 == "join") =
      some ("join", VerifiableInference.Desc.K3.joinRun
        (VerifiableInference.Desc.K3.seatCalls K3Lot.ofForm) (keysOfO A)) := by
  intro g hg A hA Lk hLk
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨Lk', e1, e2⟩ := K05_join_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) (by rw [hW]; exact hA)
  obtain rfl : Lk' = Lk := Option.some.inj (e1.symm.trans hLk)
  exact e2

set_option maxHeartbeats 4000000 in
/-- **THE KEPT "join" PASSES THE DIGITS' ACCEPT, AT ATTENTION's TWELVE.** -/
theorem k03_join_kept_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ g < 12, ∀ b',
    k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
    ∀ (z : ProofFile.InstPub) (s s₂ : VerifiableInference.Desc.First.S), StepRel b' s s₂ →
    ∀ F, s.fork? = some F → OnBytes.PscRun.Sized F →
    ∀ w, s.here = .att w →
    (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn (2 * g + 1) 2 "join") (z, s) = true →
    (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsIn (2 * g + 1) 2 "join") (z, s₂) = true := by
  intro g hg b' hb' z s s₂ hR F hF hS w hw ht
  have hl : 2 * g + 1 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  obtain ⟨-, A, -, -, -, hA, -⟩ := hT g hg
  rw [hW] at hA
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨Lk, hLk, -⟩ := K05_join_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) (by rw [hW]; exact hA)
  obtain ⟨rs, gs, hd⟩ := id hR
  exact join_kept_dig_att (h.toAtMg.𝔇 h.𝔇) mgBase Lk (K3Lot.readersAt (At.X Zp)) Zp.first.codes
    Zp.first.shape (IM.k3Place (2 * g + 1) true) b' K3Lot.ofForm hb'
    (Pc.planOk (2 * g + 1) hl true b' hb') rfl (k03_pieceAt_dig h.toAtMg (2 * g + 1)) rfl hsub
    ((h.laid.linkAt (2 * g + 1)).trans hLk) K3Lot.ofForm k03_atS2_calls z s s₂ rs gs hd hF hS
    (by rw [h24, beq_eq_false_iff_ne]; omega) A hw (k03_joinRaw_att h g hg A hA Lk hLk) ht

end P5J

#print axioms P5J.k03_joinRaw_att
#print axioms P5J.k03_join_kept_att
