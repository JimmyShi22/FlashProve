-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03OthersPubAt.lean: THE LOOKUP ARGUMENT ON THE CALLS AT THE 24 SEGMENTS IN FRONT OF THE
OUTPUT HEAD's: THE FIELD othersPub OF `CallsLastR` (Johnson/P5J/K03Last.lean): "the other kinds'
public tests that are open behind hold behind": IN ITS OWN TEXT, AT THE CLOSED CONSTANT, UNDER THE
HEAD `AtMgA`. One call each of the lookup's files' `othersPub_att_mgAll` and
`othersPub_lay_mgAll` (Johnson/Desc/Sound/MgAt/K3CallsOthers.lean); this file pays their letters.

  `calls_number`: the lookups' name of the border, kOfCalls l, is 14 l + 3 at l < 24. (That it is
    the ledger's k3K l false: their `kOfCalls_border`, Johnson/Desc/Sound/MgAt/K3CallsTests.lean.)
  `k03_shape_lay`: at layAt's place the kind's own parameters make the place's shape: by layAt's
    make (after `attAt_shape`, Johnson/Desc/First/Look/K3AttInst.lean).
  `k03_calls_place`: the written list `IM.placesW` has the ledger's place there.
  **`k03_othersPub_att`**, **`k03_othersPub_lay`**: THE FIELD.
PAID: the stated sub-protocol, hOk, hback (`k03_pieces_at`) · the place's facts (`K3Lot.k03_place`,
`k03_sub_full`; the lookups' `calls_tests`; `links_att`, `links_lay`) · hlook (`k03_look_att`,
`k03_look_lay`) · hsP · hmore, hlinks · hhd (`headLink_in_scope`) · hfit (`hfit_mgAll`) · hns
(`k03_slots_lay`) · hh5, hown (Johnson/IMR/UnheardField.lean) and hlay (Johnson/IMR/SortField.lean),
at "reached" := `AtMg.rch`, by `AtMg.rch_is_reach`.
LEFT, NAMED: hObj: the new test formsInT l 2 "objects" at the state behind an accept.

Limits. The head is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at secondHashFunction; side
library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03Last
import Johnson.P5J.K03LeftAt
import Johnson.P5J.K03PiecesAt
import Johnson.P5J.K03SlotsAt
import Johnson.P5J.RchAtMg
import Johnson.Desc.Sound.MgAt.K3CallsOthers
import Johnson.Desc.Sound.MgAt.K3CallsTests
import Johnson.Desc.First.Look.K3AttInst
import Johnson.IMR.SortField
import Johnson.LPFK9R.SubsFull

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
open VerifiableInference.Desc.First (ModelPart pubSets pubStep pubRowM pubOfItems stepOpen openSets start)
open VerifiableInference.Desc.First.Look (attAt layAt lookAt)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- In front of the head's segment it is 14 l + 3. -/
theorem calls_number : ∀ l, l < 24 → kOfCalls l = 14 * l + 3 := by decide

/-- At layAt's place the kind's own parameters make the place's shape. -/
theorem k03_shape_lay {X : Verify.Public} {i : ℕ} {y : VerifiableInference.Desc.First.Look.Place}
    (hy : layAt X i = some y) :
    (VerifiableInference.Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false y).shape =
      some y.fs := by
  unfold layAt at hy
  split at hy
  · obtain ⟨x', -, hy⟩ := Option.bind_eq_some_iff.1 hy
    obtain ⟨h', hh, rfl⟩ := Option.map_eq_some_iff.1 hy
    exact hh
  · cases hy

/-- The written list (Johnson/IMR/WrittenList.lean) has the ledger's place at the calls' number. -/
theorem k03_calls_place : ∀ l, l < 24 → IM.placesW[14 * l + 3]? = some (IM.k3Place l false) := by
  decide +kernel

set_option maxHeartbeats 4000000 in
/-- **othersPub AT AN ATTENTION's CALLS, AT THE CONSTANT.** -/
theorem k03_othersPub_att (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ l < 25, ∀ y A tl, attAt (At.X Zp) l = some (y, A, tl) →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
    (∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT l 2 "objects") (z, v.1) = true) →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS)[k3K l false]?.getD
            []) (pubRowM (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull (IM.k3Place l false)) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k3K l false]?.getD [])
            (VerifiableInference.Desc.First.rowOf linksFull (IM.k3Place l false))),
        p ∉ paidCallsR l 2 → (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub p (z, v.1) = true := by
  intro l hl y A tl hy q hq b' hb' hObj
  have ho := attAt_odd hy
  have h24 : l < 24 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  have hsub := links_att l h24 ho
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub = ModelPart.attention := Option.some.inj (hs'.symm.trans hsub)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have en := calls_number l h24
  rw [ek] at hObj ⊢
  refine othersPub_att_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape hb'
    (K.planOk l hl false b' hb') (K.back l hl false q hq) rfl hpcX hpc hl hsub
    (calls_tests hl).1 (k03_look_att h hl hy)
    (VerifiableInference.Desc.First.Look.attAt_shape hy) rfl rfl
    (by rw [headLink_in_scope h.scope h.reads h.pubOne]; omega)
    (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) ?_ hObj
  intro z u hr hu o ho'
  rw [en] at hr
  exact Meaning.K2.heard5_none_field_at h.scope h.reads O h.toAtMg.rch (fun a => a.1)
    (fun k a ha => h.toAtMg.rch_is_reach k a ha) (14 * l + 3) ((z, u.1), u.2) (IM.k3Place l false) l
    hr hu (k03_calls_place l h24) rfl rfl hpc o ho'

set_option maxHeartbeats 4000000 in
/-- **othersPub AT A LAYERS' CALLS, AT THE CONSTANT.** -/
theorem k03_othersPub_lay (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ l < 25, ∀ y, layAt (At.X Zp) l = some y →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
    (∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub (.formsInT l 2 "objects") (z, v.1) = true) →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) → SameBut u.1 v.1 →
      ∀ p ∈ pubStep ((pubSets (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull PS)[k3K l false]?.getD
            []) (pubRowM (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).more linksFull (IM.k3Place l false)) ++
          pubOfItems (stepOpen ((openSets linksFull PS (start linksFull))[k3K l false]?.getD [])
            (VerifiableInference.Desc.First.rowOf linksFull (IM.k3Place l false))),
        p ∉ paidCallsR l 2 → (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase).pub p (z, v.1) = true := by
  intro l hl y hy q hq b' hb' hObj
  obtain ⟨hp4, hN, -, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
  obtain ⟨he, hne⟩ := layAt_even hp4 hN hy
  have h24 : l < 24 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  have hsub := links_lay l h24 he
  obtain ⟨sub, hs', hpc, -⟩ := K3Lot.k03_sub_full l hl
  obtain rfl : sub = ModelPart.layers := Option.some.inj (hs'.symm.trans hsub)
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ek : k3K l false = kOfCalls l := (kOfCalls_border l).symm
  have en := calls_number l h24
  rw [ek] at hObj ⊢
  refine othersPub_lay_mgAll (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape hb'
    (K.planOk l hl false b' hb') (K.back l hl false q hq) rfl hpcX hpc hl hsub
    (calls_tests hl).1 (k03_look_lay h hl hy) (k03_shape_lay hy) rfl rfl
    (by rw [headLink_in_scope h.scope h.reads h.pubOne]; omega)
    (hfit_mgAll (h.toAtMg.𝔇 h.𝔇) mgBase rfl) (k03_slots_lay h h24 hy) ?_ ?_ hObj
  · intro z u hr hu o ho'
    rw [en] at hr
    exact Meaning.K2.own_none_field_at h.scope h.reads O h.toAtMg.rch (fun a => a.1)
      (fun k a ha => h.toAtMg.rch_is_reach k a ha) (14 * l + 3) ((z, u.1), u.2) (IM.k3Place l false)
      l hr hu (k03_calls_place l h24) rfl rfl hpc o ho'
  · intro z u hr hu
    rw [en] at hr
    exact Meaning.K2.lay_number_at h.scope h.reads O h.toAtMg.rch (fun a => a.1)
      (fun k a ha => h.toAtMg.rch_is_reach k a ha) l ((z, u.1), u.2) h24 hr hu
      (by rw [LPFK9.linksW_full]; exact hsub)

end P5J

#print axioms P5J.calls_number
#print axioms P5J.k03_shape_lay
#print axioms P5J.k03_calls_place
#print axioms P5J.k03_othersPub_att
#print axioms P5J.k03_othersPub_lay
