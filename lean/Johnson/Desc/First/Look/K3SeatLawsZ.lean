-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3SeatLawsZ.lean: the kind "lookup" (K3), the lookup on the calls at a
layers' link and at the head's: `SeatLaws`, WITH THE READER OF THE STORED TABLE's STRING A FUNCTION
OF THE PUBLIC PART.

Why. `SeatLaws` runs over every value z of the public part. In `k3_lay_seatLaws`
(Johnson/Desc/First/Look/K3CallsSeatLaws.lean) and `k3_head_seatLaws`
(Johnson/Desc/First/Look/K3HeadAtTable.lean) the letter strW stands fixed outside that "for all z".
At the meant filling the stored table's string is read through the one decoder, which reads the
key's record off z: so strW must be z's own. The rows' laws stand at one z: they are called here at
strW z, and do not turn.

Main names: `k3_lay_seatLaws_z`, `k3_head_seatLaws_z`: the two theorems named above, binder for
binder and proof line for proof line, but: strW : P → Fr.E.Str → oW.Str; hstrW and T at strW z.

Limits: as the two: rules over letters; `LayAtTable` and `HeadAtTable` are premises. Nothing on
soundness by itself; nothing on hiding.


-/
import Johnson.Desc.First.Look.K3CallsSeatLaws
import Johnson.Desc.First.Look.K3HeadAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn)
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr)

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {ql : LayPub} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : P → Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **At the calls' seat of a layers' link.** -/
theorem k3_lay_seatLaws_z (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (Bst : Desc.Block Desc.First.S Cl)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP) (hback : q.back = [])
    (H : LayOK (Params.settingOf X.P.frame) x)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs q.ds (theP).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ (z : P) y (τ : Tr (uLT (ckP .two) q.ds)),
      strW z (behind (ckP .two) Fr q.base q.ds y τ) = strW z y)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : ∀ B', SeatOf Bst B' → ∀ z : P,
      LayAtTable (Fr := Fr) G x ql tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
        smp smpW (strW z) msgW claim N Mg links ps z k m
        (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c))
    (rides : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLaws links ps k q N Mg Bst := by
  have hT : ∀ B' : Desc.Block Desc.First.S Cl, B'.Narrows Bst → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 := by
    intro B' hN u τ v hout
    obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes claim readers codes shape a Bst B' h
      hOk hN
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
      rfl hl hpc e hback u v τ hout
    exact k3_calls_sameBut claim a.piece laid sent theP [] u.1 v.1 rs cols hd
  unfold SeatLaws
  refine ⟨?_, rides, ?_, ?_⟩
  · intro B' hN z
    exact k3_lay_atTable_stated G seatT arr smp smpW (strW z) msgW claim readers codes shape a Bst
      B' h hOk hN.1 _ rfl hl hpc e hback (fun _ _ _ => rfl) H hpl hr hR hcap hsmp hsmpW (hstrW z)
      hseat σ₀ σW₀ (T B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u τ v hout).failed]
    exact hm
  · intro B' hN z u τ v hout hd
    exact (T B' hN z).decodes u v ⟨τ, hout⟩ (hT B' hN.1 u τ v hout) hd

end

section
variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy]
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {adr : HeadAdr} {x : Desc.First.Look.Place} {floor : ℕ} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : P → Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (Q : Fork → Prop)
  (gd : Desc.Wit Cells Tok MsgT → Prop)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **At the calls' seat of the head's link.** -/
theorem k3_head_seatLaws_z (rq : P → Desc.Kinds.Head.Request) (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (Bst : Desc.Block Desc.First.S Cl)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (hl : a.link = some (headLink X)) (hpc : a.piece = Desc.K3.pieceAt X (headLink X) false)
    (hback : q.back = [])
    (hB : Desc.Kinds.Head.Law.headB floor x.fs = true)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs q.ds (theP).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ (z : P) y (τ : Tr (uLT (ckP .two) q.ds)),
      strW z (behind (ckP .two) Fr q.base q.ds y τ) = strW z y)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : ∀ B', SeatOf Bst B' → ∀ z : P, letI := rq z
      HeadAtTable (Fr := Fr) G adr x tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
        smp smpW (strW z) msgW Q gd claim N Mg links ps z k m
        (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c))
    (rides : ∀ B', SeatOf Bst B' → ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLaws links ps k q N Mg Bst := by
  -- the lemma's statement reads no request; it was typed under the letter: any value serves
  have e : placeAt X (headLink X) false = some theP :=
    letI : Desc.Kinds.Head.Request := ⟨fun _ => 0, 0, 0⟩
    placeAt_headAt hx
  have hT : ∀ B' : Desc.Block Desc.First.S Cl, B'.Narrows Bst → ∀ u τ v,
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out u τ = some v →
      SameBut u.1 v.1 := by
    intro B' hN u τ v hout
    obtain ⟨laid, sent, rs, cols, -, hd⟩ := k3_calls_stated_yes claim readers codes shape a Bst B' h
      hOk hN
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
      rfl hl hpc e hback u v τ hout
    exact k3_calls_sameBut claim a.piece laid sent theP [] u.1 v.1 rs cols hd
  refine ⟨?_, rides, ?_, ?_⟩
  · intro B' hN z
    letI := rq z
    exact k3_head_atTable_stated (floor := floor) G seatT arr smp smpW (strW z) msgW Q gd claim
      readers codes shape a Bst B' h hOk hN.1 _ rfl hx hl hpc hback (fun _ _ _ => rfl) hB hpl hr hR
      hcap hsmp hsmpW (hstrW z) hseat σ₀ σW₀ (T B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u τ v hout).failed]
    exact hm
  · intro B' hN z u τ v hout hd
    letI := rq z
    exact (T B' hN z).decodes u v ⟨τ, hout⟩ (hT B' hN.1 u τ v hout) hd

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_lay_seatLaws_z
#print axioms VerifiableInference.OnPublicFiles.k3_head_seatLaws_z
