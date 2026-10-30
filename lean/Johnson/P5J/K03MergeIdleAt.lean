-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03MergeIdleAt.lean: THE LOOKUP ARGUMENT ON THE CALLS AT THE 24 SEGMENTS IN FRONT OF THE
OUTPUT HEAD's: THE NAMED FACT hmerge ("no heard row names the slot of the merge's end value": the
premise of the lookups' authors' `objIn_mgAll`, Johnson/Desc/Sound/MgAt/K3CallsObjIn.lean), IN ITS
OWN TEXT, AT THE CLOSED CONSTANT, UNDER THE HEAD `AtMgA`: IT HOLDS THERE BECAUSE THE MERGE HAS NO
SLOT.
  `putCalls_merge`, `k3_calls_merge_kept`: an accept of the lookup on the calls leaves the merge's
    slot as it was: by the seat's writers' text (they write the ledger and what was heard).
  `k03_merge_none_calls`: at a reached state without a mark in front of the calls' lookup of a
    segment l < 24 the merge has no slot: at a layers' part the caller's own rounds are not yet
    heard, at an attention's part by `mergeOf`'s text: from
    `unheard_field_at` (Johnson/IMR/UnheardField.lean), at "reached" := `AtMg.rch`.
  **`k03_mergeAt_calls`**: hmerge's own text at k := k3K l false, l < 24.

NOT HERE: the output head's calls (Johnson/P5J/K03MergeIdleHeadAt.lean: there the merge's slot is
laid by the merge, behind both lookups); the lookups on the digits (at the layers' segments the
merge has a slot there, and hmerge asks something: Johnson/P5J/K03MergeAt.lean).
Limits. The head `AtMgA` is a premise; a member of it is proved at `storedPublicFiles` and `zGap` alone (at
secondHashFunction; side library AtFullSide/Top/). At OnBytes.secondHashFunction. The full size alone. Nothing on soundness.

-/
import Johnson.P5J.K03OthersPubAt
import Johnson.Desc.First.Look.K3CallsStatedYes
import Johnson.Desc.First.Batch.AtS

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
open VerifiableInference.Desc.First.Look (lookAt placeAt)
open VerifiableInference.Desc.K9 (mergeOf)

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

/-- The calls' seat's writers leave the merge's slot. -/
theorem putCalls_merge {Cl : Type} (claim : Aff → Cl) (s : VerifiableInference.Desc.First.S)
    (g : Forest.Heard) (F Gk : Fork)
    (hF : (VerifiableInference.Desc.K3.seatCalls claim).fork s = some F)
    (hn : (VerifiableInference.Desc.K3.seatCalls claim).heard s = none) :
    mergeOf ((VerifiableInference.Desc.K3.seatCalls claim).put s g Gk) = mergeOf s := by
  simp only [VerifiableInference.Desc.K3.seatCalls] at hF hn ⊢
  cases hh : s.here with
  | between => simp [VerifiableInference.Desc.First.S.fork?, hh] at hF
  | fin _ => simp [VerifiableInference.Desc.First.S.fork?, hh] at hF
  | mem _ => simp [VerifiableInference.Desc.First.S.fork?, hh] at hF
  | lay a =>
    have hn' : a.lookHeard = none := by
      simpa [VerifiableInference.Desc.First.S.lookHeard?, hh] using hn
    simp [mergeOf, VerifiableInference.Desc.First.S.putFork,
      VerifiableInference.Desc.First.S.hearLook, hh, hn']
  | att a =>
    have hn' : a.lookHeard = none := by
      simpa [VerifiableInference.Desc.First.S.lookHeard?, hh] using hn
    simp [mergeOf, VerifiableInference.Desc.First.S.putFork,
      VerifiableInference.Desc.First.S.hearLook, hh, hn']
  | head a =>
    cases ho : a.opened with
    | false => simp [VerifiableInference.Desc.First.S.fork?, hh, ho] at hF
    | true =>
      have hn' : a.lookHeard = none := by
        simpa [VerifiableInference.Desc.First.S.lookHeard?, hh, ho] using hn
      simp [mergeOf, VerifiableInference.Desc.First.S.putFork,
        VerifiableInference.Desc.First.S.hearLook, hh, ho, hn']

/-- **An accept of the lookup on the calls leaves the merge's slot.** -/
theorem k3_calls_merge_kept {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (p : VerifiableInference.Desc.First.Look.P)
    (guests : List (VerifiableInference.Desc.First.Look.Guest VerifiableInference.Desc.First.S Cl))
    (s s' : VerifiableInference.Desc.First.S) (rs : List Fmt.RoundView)
    (cols : List (List (ℕ × List UInt64)))
    (h : (VerifiableInference.Desc.K3.block (VerifiableInference.Desc.K3.seatCalls claim) piece laid
      before p guests).decide s rs cols = .ok s') : mergeOf s' = mergeOf s := by
  obtain ⟨F, y, hF, hn, -, rfl⟩ := decide_ok _ piece laid before p guests s s' rs cols h
  exact putCalls_merge claim s y.1 F y.2 hF hn

/-- In front of the head's segment the calls' place has the piece 2. A closed fact. -/
theorem calls_piece_two :
    ((List.range 24).all fun l => decide ((IM.k3Place l false).piece = 2)) = true := by decide

/-- **In front of the calls' lookup of a segment l < 24 the merge has no slot.** -/
theorem k03_merge_none_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x) :
    ∀ l < 24, ∀ (z : ProofFile.InstPub) (u : VerifiableInference.Desc.First.S × (FrD).E.Str),
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none → mergeOf u.1 = none := by
  intro l h24 z u hr hu
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have ek : k3K l false = 14 * l + 3 :=
    ((kOfCalls_border l).symm : k3K l false = kOfCalls l).trans (calls_number l h24)
  rw [ek] at hr
  have hp2 : (IM.k3Place l false).piece = 2 :=
    of_decide_eq_true (List.all_eq_true.1 calls_piece_two l (List.mem_range.2 h24))
  rcases Meaning.K2.unheard_field_at h.scope h.reads O h.toAtMg.rch (fun a => a.1)
      (fun k a ha => h.toAtMg.rch_is_reach k a ha) (14 * l + 3) ((z, u.1), u.2) (IM.k3Place l false)
      l hr hu (k03_calls_place l h24) rfl rfl hp2 with ⟨b, hb, q⟩ | ⟨b, hb, -⟩
  · have hb' : u.1.here = .lay b := hb
    unfold mergeOf
    rw [hb']
    show b.own.map (·.wo.sFv) = none
    rw [q.2.1]
    rfl
  · have hb' : u.1.here = .att b := hb
    unfold mergeOf
    rw [hb']

set_option maxHeartbeats 4000000 in
/-- **hmerge AT THE 24 CALLS, AT THE CONSTANT.** -/
theorem k03_mergeAt_calls (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃) :
    ∀ l < 24, ∀ y, lookAt (At.X Zp) l false = some y →
    ∀ q, (h.toAtMg.row 𝔏)[k3K l false]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape l false = some b' →
    ∀ B', SeatOf b' B' → ∀ (z : ProofFile.InstPub)
      (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K l false) u →
      h.toAtMg.rch (k3K l false) ((z, u.1), u.2) → u.1.failed = none →
      (∃ τ, (strictAt B' q).ior.red.out u τ = some v) →
      ∀ g, v.1.lookHeard? = some g → ∀ f ∈ g.rows.toList, ∀ t ∈ f.slots.toList,
        mergeOf v.1 ≠ some t.1 := by
  intro l h24 y hy q hq b' hb' B' hB z u v _ hr hu ⟨τ, hout⟩ g _ f _ t _
  have hl : l < 25 := by omega
  have K := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  obtain ⟨hpcX, -⟩ := K3Lot.k03_place K3Lot.ofForm (K3Lot.readersAt (At.X Zp)) (At.X Zp)
    Zp.first.codes Zp.first.shape l false b' hb'
  have eP : placeAt (At.X Zp) l false = some (VerifiableInference.Desc.First.Look.P.ofPlace
      (Params.settingOf (At.X Zp).P.frame) false y) := by
    unfold placeAt
    rw [hy]
    rfl
  obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place l false) b' B' hb'
    (K.planOk l hl false b' hb') hB.1 (strictAt B' q) rfl rfl hpcX eP (K.back l hl false q hq) u v
    τ hout
  rw [k3_calls_merge_kept _ _ _ _ _ _ _ _ _ _ hd, k03_merge_none_calls h l h24 z u hr hu]
  exact fun e => nomatch e

end P5J

#print axioms P5J.putCalls_merge
#print axioms P5J.k3_calls_merge_kept
#print axioms P5J.calls_piece_two
#print axioms P5J.k03_merge_none_calls
#print axioms P5J.k03_mergeAt_calls
