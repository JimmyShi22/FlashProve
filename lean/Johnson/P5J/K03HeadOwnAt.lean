-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/- Johnson/P5J/K03HeadOwnAt.lean: AT THE OUTPUT HEAD's SEGMENT (NUMBER 24) OF THE CLOSED CONSTANT,
  ACROSS AN ACCEPT OF THE SEATED LOOKUP ON THE DIGITS: THE CALLING KIND's OWN THREE RUNS ("norm" |
  "policy" | "logits") AND THE RUN "join" GO FORWARD, AND THE KEPT ITEMS formsIn 24 4 "own" | "join"
  PASS: FROM THE HEAD (WITH 𝔏 AND ITS THREE EQUATIONS q₁ q₂ q₃),
  THE PROMISE IN FRONT, "REACHED" AND "NO MARK" ALONE.
IT IS THE LOOKUPS' FOUR ENDS (own_fwd_seat · own_formsIn_pass_seat · join_fwd_seat ·
  join_formsIn_pass_seat: Johnson/Top/H/Keep/HeadOwnAtSeat.lean),
  CALLED, WITH EVERY PREMISE PAID. The credit is the lookup's files' and the output head's files'.
  k03_head_pair: WHAT THE FOUR ENDS ASK OF THE TWO STATES OF THE ACCEPT, TOGETHER: K3Pass
    (k3_digits_step_pass) · SamePlanes (k3_digits_step_samePlanes) · Alike (alike_of_pass; "squaresP
    stays" off k3_digits_step_headStays: the part is kept but for tl, F, claim) · hReady
    (P5J.k03_heardAt_345: K6HeardAt at the front state IS K6Ready at whatever it shows, its ledger
    being the open one) · what was heard at the calls' seat stays (k3_digits_step_leaves at
    K3Lot.ofForm: Lean takes it at asClaim: the two are one by
    P4.ofForm_eq := rfl, and "heard" does not read the maker of claims) · a debt unpaid behind was
    unpaid in front (the lookups' k3_digits_step_hob, called in the proof itself;
    P5J.k03_hob_dig says the same at the constant: not imported here). NO PROMISE BEHIND IS SPENT.
  k03_fwd_own_head_front · k03_fwd_join_head_front: Fwd at the constant's own readers 𝔇.Rd 24, FROM
    THE PROMISE IN FRONT ALONE.
  k03_fwd_own_head · k03_fwd_join_head: the same in the form of the ledger's premise on rides (its
    hand "the promise behind" is not spent).
  **k03_ownIt_head · k03_joinIt_head**: the two items, in the form DigItemR
    (Johnson/P5J/K03DigFormsAt.lean).
K · hBo · hBj: P5J.k03_six_K | _hBo | _hBj (Johnson/P5J/K03HeadSixAt.lean).

Limits. Implications across an accept: that such an accept exists is not shown. The head is a
  premise; a member of it is proved at storedPublicFiles and zGap alone (at secondHashFunction; side library
  AtFullSide/Top/). Nothing on soundness by itself.
Terms: lean/GLOSSARY.md.

-/
import Johnson.P5J.K03HeadSixAt
import Johnson.P5J.K03ReadyAt345
import Johnson.P5J.K03DigFormsAt
import Johnson.P5J.K03RidesDigAt2
import Johnson.Desc.Sound.MgAt.K3DigitsPlanesHead
import Johnson.Desc.First.Look.K3DigitsCallersStay
import Johnson.Desc.K1.Law.ArmHeadJ

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
open VerifiableInference.Desc.First (S ModelPart Pub shift joinAt runsOf)
open VerifiableInference.Desc.K3 (seatCalls unpaid)
open VerifiableInference.Desc.K9 (holesAt statesOfLink readersOfLink)
open VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law
open VerifiableInference.Reads.Pass (Fwd)
open OnBytes.PscRun (Later)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **WHAT THE FOUR ENDS ASK OF THE TWO STATES OF THE ACCEPT.** -/
theorem k03_head_pair (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      StepRel b' u.1 v.1 →
      ∃ F G, K3Pass u.1 v.1 F G ∧ SamePlanes u.1 v.1 ∧ Alike u.1 v.1 ∧
        (∀ zz U, Sees u.1 zz U → K6Ready (At.X Zp).hS (readsOf (At.X Zp))
          (parOf (At.X Zp).hS (workOf (At.X Zp))) zz U) ∧
        (seatCalls asClaim).heard v.1 = (seatCalls asClaim).heard u.1 ∧
        ∀ i, unpaid G i = true → unpaid F i = true := by
  intro b' hb' z u v hu hr hm hR
  have hl : 24 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hsub : linksFull[24]? = some ModelPart.head := rfl
  obtain ⟨o, ho⟩ := VerifiableInference.Desc.K1.here_head_of_stand
    (k03_stand_dig h hl hsub z u hu (Classical.not_not.1 hm))
  obtain ⟨F, hF, hSz⟩ := led_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch rfl hl hsub
    z u hu hr hm
  obtain ⟨rs, gs, hd⟩ := id hR
  obtain ⟨G, Q⟩ := k3_digits_step_pass K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' (Pc.planOk 24 hl true b' hb') 24 rfl
    (k03_pieceAt_dig h.toAtMg 24) u.1 v.1 rs gs hd hF hSz
  have A := k3_digits_step_samePlanes K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' (Pc.planOk 24 hl true b' hb') 24 rfl
    (k03_pieceAt_dig h.toAtMg 24) u.1 v.1 rs gs hd
  have HS := k3_digits_step_headStays K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' (Pc.planOk 24 hl true b' hb') 24 rfl
    (k03_pieceAt_dig h.toAtMg 24) u.1 v.1 rs gs hd
  obtain ⟨-, -, -, -, hLk, -, -⟩ := k3_digits_step_leaves K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' (Pc.planOk 24 hl true b' hb') 24 rfl
    (k03_pieceAt_dig h.toAtMg 24) u.1 v.1 rs gs hd
  have hsq : ∀ o', v.1.here = .head o' → o'.squaresP = o.squaresP := by
    intro o' h'
    obtain ⟨a', ha', hkp⟩ := HS o ho
    obtain rfl : a' = o' := by
      have e := ha'.symm.trans h'
      simpa using e
    rw [hkp.eq]
  have hop : o.opened = true := by
    cases hc : o.opened with
    | true => rfl
    | false =>
      have hf := hF
      simp [S.fork?, ho, hc] at hf
  have eF : o.F = F := by
    have hf := hF
    simpa [S.fork?, ho, hop] using hf
  refine ⟨F, G, Q, A, alike_of_pass A Q ho hsq, ?_, hLk,
    k3_digits_step_hob K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb' (Pc.planOk 24 hl true b' hb') 24 rfl
    (k03_pieceAt_dig h.toAtMg 24) u.1 v.1 rs gs hd Q⟩
  intro zz U hs
  obtain ⟨g, H, F0, G0, rs0, hg, hH, hW, hh0, hL⟩ := k03_heardAt_345 h z u hr
  refine ⟨u.1, g, H, F0, G0, rs0, hs, hg, hH, hW, hh0, ?_⟩
  obtain ⟨o2, ho2, rfl, -⟩ := hs
  obtain rfl : o = o2 := by
    have e := ho.symm.trans ho2
    simpa using e
  have eL : (seatAt (At.X Zp).hS (readsOf (At.X Zp))).ledger u.1 = F := by
    show u.1.fork?.getD {} = F
    rw [hF]
    rfl
  rw [eF, ← eL]
  exact hL

/-- **THE HEAD's OWN THREE RUNS GO FORWARD: FROM THE PROMISE IN FRONT ALONE.** -/
theorem k03_fwd_own_head_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1 := by
  intro b' hb' z u v hu hr hm hR p hp
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hm' : (24 == headLink (At.X Zp)) = true := by rw [h24]; rfl
  obtain ⟨Lk, hLk⟩ := P4.link24_at_head h
  have hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk := (h.laid.linkAt 24).trans hLk
  obtain ⟨F, G, Q, A, a, hReady, -, -⟩ := k03_head_pair h 𝔏 q₁ q₂ q₃ b' hb' z u v hu hr hm hR
  rw [k03_hlink h 24 Lk hLk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact own_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBo h hk) (Or.inl rfl)
  · exact own_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBo h hk) (Or.inr (Or.inl rfl))
  · exact own_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
      (k03_six_hBo h hk) (Or.inr (Or.inr rfl))

/-- **THE RUN "join" GOES FORWARD: FROM THE PROMISE IN FRONT ALONE.** -/
theorem k03_fwd_join_head_front (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "join")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1 := by
  intro b' hb' z u v hu hr hm hR p hp
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hm' : (24 == headLink (At.X Zp)) = true := by rw [h24]; rfl
  obtain ⟨Lk, hLk⟩ := P4.link24_at_head h
  have hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk := (h.laid.linkAt 24).trans hLk
  obtain ⟨F, G, Q, A, a, hReady, hh, hob⟩ := k03_head_pair h 𝔏 q₁ q₂ q₃ b' hb' z u v hu hr hm hR
  rw [k03_hlink h 24 Lk hLk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl := hp
  exact join_fwd_seat (At.X Zp) _ 24 hm' Lk 3 _ _ 24 4 _ Q A a (k03_six_K h hk) hReady
    (k03_six_hBj h hk) atS2_calls_ofForm hh hob

/-- The three, in the form of rides' premise. -/
theorem k03_fwd_own_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1 :=
  fun b' hb' z u v hu hr hm _ hR =>
    k03_fwd_own_head_front h 𝔏 q₁ q₂ q₃ b' hb' z u v hu hr hm hR

/-- "join", in the form of rides' premise. -/
theorem k03_fwd_join_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "join")], Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1 :=
  fun b' hb' z u v hu hr hm _ hR =>
    k03_fwd_join_head_front h 𝔏 q₁ q₂ q₃ b' hb' z u v hu hr hm hR

set_option maxHeartbeats 4000000 in
/-- **THE ITEM "own" BEHIND THE DIGITS' ACCEPT, AT THE OUTPUT HEAD's SEGMENT.** -/
theorem k03_ownIt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
      DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch 24 q b'
        (.formsIn 24 (3 + shift ModelPart.head) "own") := by
  intro q hq b' hb' B' hB' z u τ v hv _ _ hu hr hf
  have hl : 24 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hsub : linksFull[24]? = some ModelPart.head := rfl
  have hm : ¬ u.1.failed ≠ none := fun k => k hf
  have hR : StepRel b' u.1 v.1 :=
    stepRel_of_seated b' q (Pc.back 24 hl true q hq) B' hB' u τ v hv
  have hmem : Pub.formsIn 24 (3 + shift ModelPart.head) "own" ∈ frontDig mgMore 24 :=
    (digits_sorted hl hsub).2 _ (by simp [keptDigits, shift, joinAt])
  have hfr := onQ_front hu hf
  rw [mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl] at hfr
  have ht := hfr _ hmem
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hm' : (24 == headLink (At.X Zp)) = true := by rw [h24]; rfl
  obtain ⟨Lk, hLk⟩ := P4.link24_at_head h
  have hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk := (h.laid.linkAt 24).trans hLk
  obtain ⟨F, G, Q, A, a, hReady, hh, hob⟩ := k03_head_pair h 𝔏 q₁ q₂ q₃ b' hb' z u v hu hr hm hR
  have he : runsOf ModelPart.head (3 + shift ModelPart.head) "own" =
      [(3, "norm"), (3, "policy"), (3, "logits")] := by decide
  refine formsIn_pass_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl hsub z u.1 v.1 (fun p hp => ?_) ht
  rw [he] at hp
  rw [k03_hlink h 24 Lk hLk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact ⟨by decide, fun hin => own_formsIn_pass_seat (At.X Zp) _ 24 hm' Lk 3 _ _ _ 24 4 _ Q A a
      (k03_six_K h hk) hReady (k03_six_hBo h hk) (Or.inl rfl) hin⟩
  · exact ⟨by decide, fun hin => own_formsIn_pass_seat (At.X Zp) _ 24 hm' Lk 3 _ _ _ 24 4 _ Q A a
      (k03_six_K h hk) hReady (k03_six_hBo h hk) (Or.inr (Or.inl rfl)) hin⟩
  · exact ⟨by decide, fun hin => own_formsIn_pass_seat (At.X Zp) _ 24 hm' Lk 3 _ _ _ 24 4 _ Q A a
      (k03_six_K h hk) hReady (k03_six_hBo h hk) (Or.inr (Or.inr rfl)) hin⟩

set_option maxHeartbeats 4000000 in
/-- **THE ITEM "join" BEHIND THE DIGITS' ACCEPT, AT THE OUTPUT HEAD's SEGMENT.** -/
theorem k03_joinIt_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
      DigItemR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch 24 q b'
        (.formsIn 24 (joinAt ModelPart.head) "join") := by
  intro q hq b' hb' B' hB' z u τ v hv _ _ hu hr hf
  have hl : 24 < 25 := by omega
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have hsub : linksFull[24]? = some ModelPart.head := rfl
  have hm : ¬ u.1.failed ≠ none := fun k => k hf
  have hR : StepRel b' u.1 v.1 :=
    stepRel_of_seated b' q (Pc.back 24 hl true q hq) B' hB' u τ v hv
  have hmem : Pub.formsIn 24 (joinAt ModelPart.head) "join" ∈ frontDig mgMore 24 :=
    (digits_sorted hl hsub).2 _ (by simp [keptDigits, shift, joinAt])
  have hfr := onQ_front hu hf
  rw [mgAll_more_closed (h.toAtMg.𝔇 h.𝔇) mgBase rfl] at hfr
  have ht := hfr _ hmem
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hm' : (24 == headLink (At.X Zp)) = true := by rw [h24]; rfl
  obtain ⟨Lk, hLk⟩ := P4.link24_at_head h
  have hk : (h.toAtMg.𝔇 h.𝔇).lk 24 = some Lk := (h.laid.linkAt 24).trans hLk
  obtain ⟨F, G, Q, A, a, hReady, hh, hob⟩ := k03_head_pair h 𝔏 q₁ q₂ q₃ b' hb' z u v hu hr hm hR
  have he : runsOf ModelPart.head (joinAt ModelPart.head) "join" = [(3, "join")] := by decide
  refine formsIn_pass_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl hsub z u.1 v.1 (fun p hp => ?_) ht
  rw [he] at hp
  rw [k03_hlink h 24 Lk hLk]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
  obtain rfl := hp
  exact ⟨by decide, fun hin => join_formsIn_pass_seat (At.X Zp) _ 24 hm' Lk 3 _ _ _ 24 4 _ Q A a
    (k03_six_K h hk) hReady (k03_six_hBj h hk) atS2_calls_ofForm hh hob hin⟩

end P5J

#print axioms P5J.k03_head_pair
#print axioms P5J.k03_fwd_own_head_front
#print axioms P5J.k03_fwd_join_head_front
#print axioms P5J.k03_fwd_own_head
#print axioms P5J.k03_fwd_join_head
#print axioms P5J.k03_ownIt_head
#print axioms P5J.k03_joinIt_head
