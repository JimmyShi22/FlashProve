-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OwnItAttAt.lean: THE KIND "LOOKUP" (K3), AT THE DIGITS' LOOKUPS OF THE TWELVE
ATTENTION SEGMENTS, AT THE COMPOSED MEANING's OWN PARAMETERS: THE COMPOSED MEANING's PUBLIC TEST AT
THE KEPT ITEM formsIn (2 g + 1) 3 "own" ACCEPTS BEHIND AN ACCEPT OF THE SEATED SUB-PROTOCOL. One
theorem.
  `k03_ownIt_att`: ends in `DigItemR … (.formsIn (2 * g + 1) (3 + shift ModelPart.attention) "own")`
    (Johnson/P5J/K03DigFormsAt.lean): the premise hOwnIt of `k03_digForms` and the binder Io of the
    kind's counts, at attention's twelve.
THE ROAD. The accept gives StepRel (`stepRel_of_seated`) · IN FRONT the item's test accepts: it is
among the kept items (`digits_sorted`, by the kernel) and the promise in front holds them
(`onQ_front`) · the item stands for three runs: "first", "keys", "second" at the second sub-protocol
· each run's test goes forward by the lookup's files' `k3_formsIn_fwd`
(Johnson/Top/H/Keep/FormsPassK3.lean) at `k3_digits_step_pass`: hf := `k03_fwd_att_front`
(Johnson/P5J/K03OwnFwdAttAt.lean: it takes no promise behind) · hlow: these runs lay nothing
late: `own_low` (Johnson/Top/H/Keep/AttOwnSame.lean), whose premise "the run returns the state
that it was given" is `runsN_keeps` at what the link states
(`K05_states_raw_of_open`, Johnson/H2K5R/StatesRawAtOpen.lean). NO PROMISE BEHIND THE ACCEPT IS
SPENT. The field's hands SameBut and DigLeft are not spent either. WHAT STAYS A PREMISE: the head
AtMgA · the filling with its three equations.
Limits. At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03OwnFwdAttAt
import Johnson.P5J.K03DigFormsAt
import Johnson.Desc.Sound.MgAt.K3DigitsFormsPlanes

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
open VerifiableInference.Desc.First (ModelPart Pub shift runsOf)
open VerifiableInference.Desc.K9 (holesAt statesOfLink readersOfLink readerOf)
open VerifiableInference.Desc.First.Att.P (runsN runsN_keeps K05_states_raw_of_open)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **THE ITEM "own" BEHIND THE DIGITS' ACCEPT, AT ATTENTION's TWELVE.** -/
theorem k03_ownIt_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ g < 12, ∀ q, (h.toAtMg.row 𝔏)[k3K (2 * g + 1) true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape (2 * g + 1) true = some b' →
      DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch (2 * g + 1) q b'
        (.formsIn (2 * g + 1) (3 + shift ModelPart.attention) "own") := by
  intro g hg q hq b' hb' B' hB' z u τ v hv _ _ hu hr hf
  have hl : 2 * g + 1 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[2 * g + 1]? = some ModelPart.attention := by
    have h0 := List.all_eq_true.1 linksAttFull g (List.mem_range.2 hg)
    simpa using h0
  have hm : ¬ u.1.failed ≠ none := fun k => k hf
  have hR : StepRel b' u.1 v.1 :=
    stepRel_of_seated b' q (Pc.back (2 * g + 1) hl true q hq) B' hB' u τ v hv
  -- in front the item's test accepts
  have hmem : Pub.formsIn (2 * g + 1) (3 + shift ModelPart.attention) "own" ∈
      frontDig mgMore (2 * g + 1) :=
    (digits_sorted hl hsub).2 _ (by simp [keptDigits, shift])
  have hfr := onQ_front hu hf
  rw [mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl] at hfr
  have ht := hfr _ hmem
  -- what the link states
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨hT, -⟩ := IM.ground_tails h.scope h.reads O.pub O.blank
  obtain ⟨-, A, -, -, -, hA, -⟩ := hT g hg
  obtain ⟨Lk, hLk, hSt⟩ := K05_states_raw_of_open O (by rw [hW]; exact hp4)
    (by rw [hW]; exact hN ▸ hg) hA
  have hRd := k03_hlink h (2 * g + 1) Lk hLk
  have hne : (2 * g + 1 == headLink (At.X Zp)) = false := by
    rw [h24, beq_eq_false_iff_ne]
    omega
  -- the accept passes
  obtain ⟨F, hF, hSz⟩ := led_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch rfl hl hsub
    z u hu hr hm
  obtain ⟨rs, gs, hd⟩ := id hR
  obtain ⟨G, Q⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place (2 * g + 1) true) b' hb'
    (Pc.planOk (2 * g + 1) hl true b' hb') (2 * g + 1) rfl (k03_pieceAt_dig h.toAtMg (2 * g + 1))
    u.1 v.1 rs gs hd hF hSz
  have hFw := k03_fwd_att_front h 𝔏 q₁ q₂ q₃ g hg b' hb' z u v hu hr hm hR
  have he : runsOf ModelPart.attention (3 + shift ModelPart.attention) "own" =
      [(2, "first"), (2, "keys"), (2, "second")] := by decide
  refine formsIn_pass_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl hsub z u.1 v.1 (fun p hp => ?_) ht
  rw [he] at hp
  have hj : p.1 = 2 ∧ p.2 ≠ "join" ∧ (p.2 == "K8.equations") = false := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl <;> exact ⟨rfl, by decide, by decide⟩
  refine ⟨hj.2.2, fun hin => k3_formsIn_fwd Q _ _ p.1 p.2 (hFw p hp) (fun R hRf y hy => ?_) hin⟩
  -- these runs lay nothing late
  rw [hRd, hj.1] at hRf
  have e' : (if p.2 == "K8.equations" then
        (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk).small u.1
      else match readerOf (statesOfLink Lk) 2 p.2 u.1 with
        | some R => some R
        | Option.none =>
          (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk).silent 2 p.2 u.1) = some R := hRf
  rw [hj.2.2] at e'
  have hrd : readerOf (statesOfLink Lk) 2 p.2 u.1 = some R := by
    cases hq' : readerOf (statesOfLink Lk) 2 p.2 u.1 with
    | none =>
      simp only [hq'] at e'
      have e2 : (holesAt (At.X Zp) (headLink (At.X Zp)) (2 * g + 1) Lk).silent 2 p.2 u.1 =
          some R := e'
      rw [holesAt_silent_none (At.X Zp) hne Lk 2 p.2 u.1] at e2
      exact nomatch e2
    | some R0 =>
      simp only [hq'] at e'
      exact e'
  have hlate : R.late = [] := own_low (states := statesOfLink Lk) (fun nm rr hfd cl t hrun => by
    rw [hSt] at hfd
    have hmm := List.mem_of_find?_eq_some hfd
    have hnm : nm = p.2 := by simpa using List.find?_some hfd
    exact runsN_keeps A (nm, rr) hmm (hnm ▸ hj.2.1) 0 u.1 (cl, t) hrun) hrd
  rw [hlate] at hy
  exact absurd hy (List.not_mem_nil)

end P5J

#print axioms P5J.k03_ownIt_att
