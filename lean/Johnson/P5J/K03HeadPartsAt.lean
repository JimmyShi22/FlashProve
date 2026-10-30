-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03HeadPartsAt.lean: THE LOOKUP ARGUMENT ON THE CALLS AT THE OUTPUT HEAD's SEGMENT: THE
FIELD parts OF `HeadShortR` (Johnson/P5J/K03HeadAt.lean) AND OF `HeadRestR`
(Johnson/Desc/Sound/MgAt/K3Mean.lean), IN ITS OWN TEXT, AT THE CLOSED CONSTANT, UNDER THE HEAD
`AtMgA`. It pays the letters of `head_parts_base` (Johnson/Desc/Sound/MgAt/K3HeadBehindAt.lean).

  `lookAt_fs_head`: lookAt's place at 24, where X.p4 = true and X.NGr = 12: its shape is the head's
    layout's: by lookAt's make.
  `k03_look_head`: in scope the head's reader's place (headAt) IS the table's own (lookAt at 24).
  **`k03_head_parts_at`**: THE FIELD.
PAID: hmH (`headLink_in_scope`) · hlook (here) · hns (`k03_slots_head`,
Johnson/P5J/K03SlotsHeadAt.lean) · hOk, hback (`k03_pieces_at`) · next
(`MgAt.next_place`) · stand (`stand_at`) · fit (`k03_book_at`) · tells (`k03_tells_at`) · hbase
(`k03_base_at`) · hsmpT (`k03_es`, `smpNamed_same`).
LEFT, NAMED: hObj (the test formsInT 24 3 "objects" at the state behind an accept) · hg (the table's
test fenceFit at the constant's numbers).

Limits. The head is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03HeadAt
import Johnson.P5J.K03SlotsHeadAt
import Johnson.P5J.K03PiecesAt
import Johnson.Desc.Sound.MgAt.K3HeadBehindAt
import Johnson.Desc.Sound.MgAt.K3CallsStand
import Johnson.Desc.Sound.MgAt.K3Pins
import Johnson.Desc.Kinds.Law.TabIsEXInScope

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open OnBytes.Model.Stages (LinkH SubPlanH)
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First.Look (Place lookAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl} {x : Place}

/-- lookAt's place at the head's segment: by lookAt's make. -/
theorem lookAt_fs_head {X : Verify.Public} (h4 : X.p4 = true) (hN : X.NGr = 12) {y : Place}
    (hy : lookAt X 24 false = some y) : y.fs = X.HLy.fs := by
  have hs : (if X.p4 = true then 2 else 1) = 2 := by rw [h4]; rfl
  unfold lookAt at hy
  dsimp only at hy
  rw [hs, hN] at hy
  split at hy
  · simp only [Bool.false_eq_true, if_false] at hy
    obtain rfl := Option.some.inj hy
    rfl
  · rename_i hc
    exact absurd rfl hc

/-- **In scope the head's reader's place is the table's own.** -/
theorem k03_look_head (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    lookAt (At.X Zp) 24 false = some x := by
  have hx := h.headAt
  have efs := VerifiableInference.Desc.Kinds.Head.Law.InScope.headAt_fs h.scope h.pubOne hx
  obtain ⟨h4, hN, -, -⟩ := Meaning.scope_plans h.scope h.reads h.pubOne
  unfold VerifiableInference.Desc.Kinds.Head.Law.headAt at hx
  rw [h4, hN] at hx
  have e24 : (if true = true then 2 else 1) * 12 = 24 := rfl
  rw [e24] at hx
  obtain ⟨y, h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨k, -, rfl⟩ := Option.map_eq_some_iff.1 hx
  have ek : k = y.fs := efs.trans (lookAt_fs_head h4 hN h1).symm
  subst ek
  exact h1

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

set_option maxHeartbeats 4000000 in
/-- **THE FIELD parts AT THE HEAD's CALLS, AT THE CONSTANT.** -/
theorem k03_head_parts_at (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
    (hg : VerifiableInference.Desc.First.fenceFit (At.N Zp cF) linksFull PS = true) :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 false = some b' →
    (∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub) u τ v, (strictAt B' q).ior.red.out u τ = some v →
      SameBut u.1 v.1 →
      onQ (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS
        (fun s => (z, s)) (k3K 24 false) u →
      h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2) → u.1.failed = none →
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT 24 3 "objects") (z, v.1) = true) →
    ∀ B', SeatOf b' B' → ∀ z : ProofFile.InstPub,
      BehindPartsR (Fr := FrD) x (Params.settingOf (At.X Zp).P.frame) (h.toAtMg.𝔇 h.𝔇).N
        (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS z (k3K 24 false) 24 3
        ((h.toAtMg.𝔇 h.𝔇).sent.arrayOf.getD 24 #[]) (IM.k3Place 24 false) (MgAt.nextOf 24 false)
        (At.told cF) (fun u v => ∃ τ, (strictAt B' q).ior.red.out u τ = some v)
        (fun u => h.toAtMg.rch (k3K 24 false) ((z, u.1), u.2)) := by
  intro q hq b' hb' hObj
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  exact head_parts_base (h.toAtMg.𝔇 h.𝔇) Zp.first.codes Zp.first.shape
    (headLink_in_scope h.scope h.reads h.pubOne) (k03_look_head h) q b' hb'
    (K.planOk 24 (by omega) false b' hb') (K.back 24 (by omega) false q hq) h.toAtMg.rch hObj
    (k03_slots_head h) (MgAt.next_place (by omega) false) (stand_at (by omega))
    (k03_book_at Zp cF) (k03_tells_at h.toAtMg 24 (by omega) false)
    (fun t ht => k03_base_at h.toAtMg 𝔏 q₁ q₂ q₃ (k03_blocks_at h.toAtMg)
      (k03_bookHeld_at Zp Np cF) hg 24 (by omega) false q hq t ht)
    (fun z s s' e => by
      rw [k03_es h]
      funext t i
      exact smpNamed_same _ _ (z, s) (z, s') e t i)

end P5J

#print axioms P5J.lookAt_fs_head
#print axioms P5J.k03_look_head
#print axioms P5J.k03_head_parts_at
