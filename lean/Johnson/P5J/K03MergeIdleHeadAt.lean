-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MergeIdleHeadAt.lean: THE LOOKUP ARGUMENT ON THE CALLS AT THE OUTPUT HEAD's SEGMENT:
THE NAMED FACT hmerge ("no heard row names the slot of the merge's end value"), IN ITS OWN TEXT, AT
THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA`: IT HOLDS THERE BECAUSE THE MERGE HAS NO SLOT YET.
  `k6Reached_340`: a state that is reached at border 340 of the first chain (in front of the head's
    calls' lookup) meets `K6Reached` (Johnson/Desc/Kinds/Law/K6Reached.lean: its field wo: the merge
    has not laid its end value). AFTER OTHER FILES' OWN PROOF: the first two thirds of `back_341`
    (Johnson/P4R/Back341N.lean: the walk back over the sub-protocols at 339 and 338), then
    `made_H1` and `kept_H2`, as in `k6Reached_341` (Johnson/P4R/K6ReachedAt341.lean).
  `k03_merge_none_head_calls`: so, at "reached" := `AtMg.rch`: mergeOf = none there.
  **`k03_mergeAt_head_calls`**: hmerge's own text at k := k3K 24 false: by `k3_calls_merge_kept`
    (Johnson/P5J/K03MergeIdleAt.lean): the accept leaves the merge's slot.
WHY AT 340 AND NOT AT 341, where `k6Reached_341` has the fact: the state behind is an accept of ANY
sub-protocol that narrows the stated one: it need not be reached.

Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03MergeIdleAt
import Johnson.P4R.Back341N
import Johnson.Desc.Kinds.Law.K6Reached

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Block Chain FileDescription Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S)
open VerifiableInference.Desc.First.K2 (between_of_link)
open VerifiableInference.Desc.First.Look (lookAt placeAt)
open VerifiableInference.Desc.K9 (mergeOf)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (K6Reached made_H1 kept_H2)
open Johnson.Desc.First.Walk.Tied (Reach reach_raw)
open P4 (reach_last step_yes head_behind_338 k7Front k7_front k7_left_seat)

/-- **A state reached at border 340 meets K6Reached.** -/
theorem k6Reached_340 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S ProofFile.Cl)}
    {c : Chain S ProofFile.Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat}
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) {XP : Type} {start : XP → S}
    {z : XP} {s340 : S} (h340 : Reach 0 c.blocksInOrder start 340 (z, s340)) : K6Reached s340 := by
  obtain ⟨s339, b2, h339, e2, y2⟩ := reach_last h340
  obtain ⟨s338, b1, h338, e1, y1⟩ := reach_last h339
  -- 338
  obtain ⟨L1, c1, l1, l2, -, -, hyes, -⟩ := k7_left_seat hS hR O
  have f1 : c.blocksInOrder[338]? = some c1 := by
    have q := IM.hear_at_flat l1 l2
    rwa [IM.flatIx_scope hS hR O (by decide) 0] at q
  obtain rfl : b1 = c1 := Option.some.inj (e1.symm.trans f1)
  obtain ⟨r1, g1, d1⟩ := step_yes y1
  obtain ⟨r1', g1', a1⟩ := hyes _ _ _ _ d1
  obtain ⟨ha, hhead⟩ := head_behind_338 Bs.G₀.W a1
  have Z1 : K6Reached s339 := made_H1 Bs.G₀.W 24 "H:1" (k7Front Bs.G₀.W) Bs.G₀.W.H.tl
    (k7_front Bs.G₀.W) s338 r1' g1' s339 a1
  -- 339
  obtain ⟨L2, c2, x, m1, m2, -, hla2, hK⟩ := IM.k2_head_of hS hR O
  have f2 : c.blocksInOrder[339]? = some c2 := by
    have q := IM.hear_at_flat m1 m2
    rwa [IM.flatIx_scope hS hR O (by decide) 1] at q
  obtain rfl : b2 = c2 := Option.some.inj (e2.symm.trans f2)
  obtain ⟨r2, g2, d2⟩ := step_yes y2
  have a2 : x.decide s339 r2 g2 = .ok s340 :=
    ((IM.yes_alone hla2 (by decide) s339 s340 r2 g2).1 d2).1
  rcases hK with ⟨-, hm⟩ | ⟨Pp, n, -, -, hd⟩
  · obtain ⟨e, he⟩ := hm s339 r2 g2
    rw [he] at a2
    cases a2
  · rcases hd with ⟨hn, -⟩ | ⟨l, HP, -, -, hx⟩ | ⟨l, -, hx⟩
    · cases hn
    · rw [hx] at a2
      exact kept_H2 a2 Z1
    · rw [hx] at a2
      have hb := between_of_link (snd := _root_.Tw.K2.sendByL8) a2 rfl
      rw [hhead] at hb
      cases hb

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- **In front of the head's calls' lookup the merge has no slot.** -/
theorem k03_merge_none_head_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ (z : ProofFile.InstPub) (u : S × (FrD).E.Str),
      h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → mergeOf u.1 = none := by
  intro z u hr
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hr' : Reach 0 cF.blocksInOrder (ProofFile.startS Zp) 340 (z, u.1) :=
    reach_raw (h.toAtMg.rch_is_reach _ _ hr)
  exact (k6Reached_340 h.scope h.reads O hr').wo

set_option maxHeartbeats 4000000 in
/-- **hmerge AT THE HEAD's CALLS, AT THE CONSTANT.** -/
theorem k03_mergeAt_head_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ y, lookAt (At.X Zp) 24 false = some y →
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) (u v : S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 false) u →
      h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, v.1.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ t ∈ f.slots.toList,
        mergeOf v.1 ≠ some t.1 := by
  intro y hy q hq b' hb' B' hB z u v _ hr _ ⟨τ, hout⟩ g _ f _ t _
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape 24 false b' hb'
  have eP : placeAt (At.X Zp) 24 false = some (VerifiableInference.Desc.First.Look.P.ofPlace
      (Params.settingOf (At.X Zp).P.frame) false y) := by
    unfold placeAt
    rw [hy]
    rfl
  obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place 24 false) b' B' hb'
    (K.planOk 24 (by omega) false b' hb') hB.1 (strictAt B' q) rfl rfl hpcX eP
    (K.back 24 (by omega) false q hq) u v τ hout
  rw [k3_calls_merge_kept _ _ _ _ _ _ _ _ _ _ hd, k03_merge_none_head_calls h z u hr]
  exact fun e => nomatch e

end P5J

#print axioms P5J.k6Reached_340
#print axioms P5J.k03_merge_none_head_calls
#print axioms P5J.k03_mergeAt_head_calls
