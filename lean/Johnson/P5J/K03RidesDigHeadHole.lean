-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/P5J/K03RidesDigHeadHole.lean: THE KIND "LOOKUP" (K3): THE FIELD rides AT THE OUTPUT HEAD's
DIGITS, AT THE CLOSED CONSTANT, OVER THE SECOND PAYMENT `ridesAtR_digits_head_hole`
(Johnson/Desc/Sound/MgAt/K3RidesDigFwd3.lean), WHICH DOES NOT ASK THAT THE RUN "planes" ITSELF
ANSWERS IN FRONT. FROM THREE PREMISES ON THE STATES THAT ARE NOT SHOWN AT THE CONSTANT: UNTIL
THEY HAVE PAYERS THE ROW BUYS NOTHING. (Where this
and lean/THEOREM.md differ, the page holds.) One theorem: a call.
  `k03_rides_dig_head_hole`: in the form in which the kind's condition asks the field: from hOb
    (across the accept: what the ledger behind still owes, the ledger in front owed), hJoin (the
    calling kind's run "join" goes forward), hOwn ("norm", "policy", "logits" go forward).
It takes the place of `k03_rides_dig_head_three` (Johnson/P5J/K03RidesDigLeft.lean), whose premise
hrP may be false at a state under the promise. Laid in: as there; the holes are the description's
own at the head's segment (hmH by the scope; hH := rfl).
Limits: a call. The head h and the free letters' three equations are premises. The full size
alone. No soundness is claimed.

-/
import Johnson.P5J.K03RidesDigLeft
import Johnson.Desc.Sound.MgAt.K3RidesDigFwd3

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 40000

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace P5J
open OnBytes OnBytes.Flat OnBytes.Maker OnBytes.Model
open Inst.Model
open VerifiableInference.OnPublicFiles
open VerifiableInference.Desc (Chain Wit Link)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart)
open VerifiableInference.Desc.First.Look (lookAt)
open VerifiableInference.Desc.K9 (holesAt)
open VerifiableInference.Desc.Kinds.Head (planesAt callerReaders)
open VerifiableInference.Reads.Pass (Fwd)

local notation "PS" => VerifiableInference.Desc.First.flatPlacesOf linksFull true

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF}
  {Zp : ProofFile.Pub} {Np : H2U.Places4} {cF : Chain TS ProofFile.Cl}
  {x₀ : VerifiableInference.Desc.First.Look.Place}

set_option quotPrecheck false in
local notation "FrD" => frameAt (D.at OnBytes.Slice.frS.P.T.a)
  (allOf (D.at OnBytes.Slice.frS.P.T.a)) (D.at OnBytes.Slice.frS.P.T.a).key₁ 0

section
variable (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x₀)
  (𝔏 : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) At.Tok)
  (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = 𝔏.c₁ :: 𝔏.k₁)
  (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = 𝔏.c₂ :: 𝔏.k₂)
  (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = 𝔏.c₃ :: 𝔏.k₃)
include q₁ q₂ q₃

/-- **THE OUTPUT HEAD's DIGITS, OVER THE SECOND PAYMENT.** -/
theorem k03_rides_dig_head_hole :
    ∀ q, (h.toAtMg.row 𝔏)[k3K 24 true]? = some q →
    ∀ b', k3Const (At.X Zp) Zp.first.codes Zp.first.shape 24 true = some b' →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ F G, K3Pass u.1 v.1 F G → ∀ i, VerifiableInference.Desc.K3.unpaid G i = true →
        VerifiableInference.Desc.K3.unpaid F i = true) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) 3 "join" u.1 v.1) →
    (∀ (z : ProofFile.InstPub) (u v : VerifiableInference.Desc.First.S × (FrD).E.Str),
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true) u →
      h.toAtMg.rch (k3K 24 true) ((z, u.1), u.2) → ¬ u.1.failed ≠ none →
      onQ (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) linksFull PS (fun s => (z, s))
        (k3K 24 true + 1) v →
      StepRel b' u.1 v.1 →
      ∀ p ∈ [(3, "norm"), (3, "policy"), (3, "logits")],
        Fwd ((h.toAtMg.𝔇 h.𝔇).Rd 24) p.1 p.2 u.1 v.1) →
      RidesAtR (Fr := FrD) (h.toAtMg.𝔇 h.𝔇).N (mgAll (h.toAtMg.𝔇 h.𝔇) mgBase) h.toAtMg.rch
        (k3K 24 true) q b' := by
  intro q hq b' hb' hOb hJoin hOwn
  have hl : 24 < 25 := by omega
  obtain ⟨y, tl, hdig⟩ := k03_digAt_some h hl
  obtain ⟨Lk, hLk⟩ := k03_link_some h hl
  obtain ⟨hs, hx, hsh⟩ : ∃ hs, lookAt (At.X Zp) 24 true = some y ∧
      (VerifiableInference.Desc.First.Look.P.ofPlace
        (OnBytes.Params.settingOf (At.X Zp).P.frame) true y).shape = some hs := by
    unfold VerifiableInference.Desc.First.Look.digAt at hdig
    obtain ⟨x', hx', hd1⟩ := Option.bind_eq_some_iff.1 hdig
    obtain ⟨tl', -, hd2⟩ := Option.bind_eq_some_iff.1 hd1
    obtain ⟨s, hs', hd3⟩ := Option.map_eq_some_iff.1 hd2
    obtain ⟨rfl, -⟩ := Prod.mk.inj hd3
    exact ⟨s, hx', hs'⟩
  have Pc := k03_pieces_at h.toAtMg 𝔏 q₁ q₂ q₃
  have h24 : headLink (At.X Zp) = 24 := headLink_in_scope h.scope h.reads h.pubOne
  have hsub : linksFull[24]? = some ModelPart.head := by decide +kernel
  have hU : (At.X Zp).H.tl.ix.U.getD 2 none = some 0 :=
    VerifiableInference.Desc.Kinds.Head.Law.ReadsNamed.public_third h.pubOne
  obtain ⟨Bs, base, O⟩ := h.laid.opened
  have hW : Bs.G₀.W = At.X Zp := O.W
  have hrd : K3Lot.readersAt (At.X Zp) 24 = some (callerReaders (planesAt 0)) := by
    obtain ⟨p4, ng, -⟩ := _root_.Meaning.scope_plans h.scope h.reads h.pubOne
    unfold K3Lot.readersAt VerifiableInference.Desc.K3.isHead
    rw [p4, ng, hU]
    rfl
  obtain ⟨L1, e1, hO⟩ := k03_objects_raw h.scope h.reads O 24 hl false
  obtain ⟨L2, e2, hG⟩ := k03_guests_raw h.scope h.reads O 24 hl false
  obtain ⟨L3, p, e3, -, hP⟩ := k03_planes_raw h.scope h.reads O 24 hl
    (callerReaders (planesAt 0)) (by rw [hW]; exact hrd)
  obtain rfl : Lk = L1 := Option.some.inj (hLk.symm.trans e1)
  obtain rfl : Lk = L2 := Option.some.inj (hLk.symm.trans e2)
  obtain rfl : Lk = L3 := Option.some.inj (hLk.symm.trans e3)
  exact ridesAtR_digits_head_hole (Fr := FrD) (h.toAtMg.𝔇 h.𝔇) mgBase h.toAtMg.rch
    (holesAt (At.X Zp) (headLink (At.X Zp)) 24 Lk) Lk K3Lot.ofForm
    (K3Lot.readersAt (At.X Zp)) Zp.first.codes Zp.first.shape (IM.k3Place 24 true) b' hb'
    (Pc.planOk 24 hl true b' hb') rfl (k03_pieceAt_dig h.toAtMg 24) rfl rfl hl
    hsub (k03_hlink h 24 Lk hLk) k03_atS2_calls
    (At.seats Zp) (k03_es h) (k03_hD h) (k03_hd h) q (K3Lot.k03_at_full 24 hl true) rfl
    (by decide)
    (Pc.back 24 hl true q hq) hx hsh (k03_index_low_dig h 𝔏 q₁ q₂ q₃ hl q hq)
    (fun _ _ _ _ => rfl) (k03_hHeadAll h q.base)
    (headLink (At.X Zp)) (by rw [h24]; rfl) rfl 0 p.lm
    (fun n r e => (Prod.mk.inj (Option.some.inj (hO.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hG.symm.trans e))).2.symm)
    (fun n r e => (Prod.mk.inj (Option.some.inj (hP.symm.trans e))).2.symm)
    (fun z u _ hu _ hm _ _ => k03_hrO_head h Lk hLk z u hu (Classical.not_not.1 hm))
    (fun z u _ hu _ hm _ _ => k03_hrG_head h Lk hLk z u hu (Classical.not_not.1 hm))
    hOb
    (fun z u _ hu _ hm _ _ =>
      VerifiableInference.Desc.K1.here_head_of_stand
        (k03_stand_dig h hl hsub z u hu (Classical.not_not.1 hm)))
    (k03_hWin h hl hb') hJoin hOwn (k03_hWt h 𝔏 q₁ q₂ q₃ b' hb')

end

end P5J

#print axioms P5J.k03_rides_dig_head_hole
