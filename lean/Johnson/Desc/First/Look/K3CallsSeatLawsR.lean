-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3CallsSeatLawsR.lean: WHAT THE KIND's FILES OWE AT THE CALLS' SEATS OF AN
ATTENTION AND OF A LAYERS' LINK, IN THE SECOND FORM OF THE CHAIN OF PROMISES: k3_att_seatLawsR,
k3_lay_seatLawsR END IN Desc.Sound.SeatLawsR (Johnson/Desc/Sound/TiedSeatR.lean), over AttAtTableR
and LayAtTableR at Rc := fun a => Rch k ((z, a.1), a.2). So the kind's law at these places spends,
of the facts along the fold, OwnIs alone: neither "frame.liveIs" nor "in order".
THE TEXT IS THE FIRST FORM's (Johnson/Desc/First/Look/K3CallsSeatLaws.lean), TURNED BY A PROGRAM,
after the pattern at the
head's calls (Johnson/Desc/First/Look/K3HeadAtTableR.lean); the law beneath is called as it lies;
the first form's file is not touched. NO SOUNDNESS IS CLAIMED.

USER: K3CallsMeanR.lean.
OBJECT, LETTERS: the first form's; and Rc (Rch): a condition on the statement that stands
  beside the table's promise in front (meant: "this verifier's state is reached from the state at
  the start by the sub-protocols in front"): A LETTER: no term is named here.

Main names: `k3_att_seatLawsR`, `k3_lay_seatLawsR`.

Limits. The first form's. Rc is a letter; ownIn is a premise, shown at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3RowsStatedR
import Johnson.Desc.Sound.TiedSeatR

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers openSets pubSets start
  sampledIn)

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {k m : ℕ} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **WHAT IS OWED AT THE CALLS' SEAT OF AN ATTENTION LINK, SECOND FORM.** -/
theorem k3_att_seatLawsR (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place) (Bst : Desc.Block Desc.First.S Cl)
    (q : Piece (ckP .two) Fr (P × Desc.First.S) Cl (Desc.Wit Cells Tok MsgT))
    (h : Desc.K3.theStated claim readers X codes shape a = some Bst) (hOk : Bst.planOk = true)
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP) (hback : q.back = [])
    (H : AttOK (Params.settingOf X.P.frame) x A tl D rad)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs q.ds (theP).rounds)
    (hcap : q.err = Err.cap 128 (uLT (ckP .two) q.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (attSg x D rad).Smp)
    (T : ∀ B', SeatOf Bst B' →
      ∀ z : P,
      AttAtTableR (Fr := Fr) G x A tl D rad (Params.settingOf X.P.frame) seatT arr smp claim N Mg
        links ps z k m (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c)
        (fun a => Rch k ((z, a.1), a.2)))
    (rides : ∀ B', SeatOf Bst B' →
      ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLawsR links ps k q N Mg Rch Bst := by
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
  unfold SeatLawsR
  refine ⟨?_, rides, ?_, ?_⟩
  · intro B' hN z
    exact k3_att_atTable_statedR G seatT arr smp (fun a => Rch k ((z, a.1), a.2)) claim readers
      codes shape a Bst B' h hOk hN.1 _ rfl hl hpc e hback (fun _ _ _ => rfl) H hr hR hcap hsmp
      hseat σ₀ (T B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u τ v hout).failed]
    exact hm
  · intro B' hN z u τ v hout hd
    exact (T B' hN z).decodes u v ⟨τ, hout⟩ (hT B' hN.1 u τ v hout) hd

end

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
  {ps : List Desc.Place} {k m : ℕ} (Rch : ℕ → (P × Desc.First.S) × Fr.E.Str → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **WHAT IS OWED AT THE CALLS' SEAT OF A LAYERS' LINK, SECOND FORM.** strW: the reader of the
committed table's string, of the public part (after k3_lay_seatLaws_z, K3SeatLawsZ.lean). -/
theorem k3_lay_seatLawsR (claim : Aff → Cl)
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
    (T : ∀ B', SeatOf Bst B' →
      ∀ z : P,
      LayAtTableR (Fr := Fr) G x ql tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
        smp smpW (strW z) msgW claim N Mg links ps z k m
        (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c)
        (fun a => Rch k ((z, a.1), a.2)))
    (rides : ∀ B', SeatOf Bst B' →
      ∀ (z : P) a τ b w i,
      onQ N Mg links ps (fun s => (z, s)) k a → Rch k ((z, a.1), a.2) → ¬ a.1.failed ≠ none →
      (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some b →
      onQ N Mg links ps (fun s => (z, s)) (k + 1) b →
      relQ N Mg links ps (fun s => (z, s)) (k + 1) b w →
      openAfter (insQ links ps) (outsQ links ps) (· ∈ start links) k i → ¬ insQ links ps k i →
      meansQ N Mg (fun s => (z, s)) i a w) :
    SeatLawsR links ps k q N Mg Rch Bst := by
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
  unfold SeatLawsR
  refine ⟨?_, rides, ?_, ?_⟩
  · intro B' hN z
    exact k3_lay_atTable_statedR G seatT arr smp smpW (strW z) msgW
      (fun a => Rch k ((z, a.1), a.2)) claim readers codes shape a Bst B' h
      hOk hN.1 _ rfl hl hpc e hback (fun _ _ _ => rfl) H hpl hr hR hcap hsmp hsmpW (hstrW z) hseat
      σ₀ σW₀ (T B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u τ v hout).failed]
    exact hm
  · intro B' hN z u τ v hout hd
    exact (T B' hN z).decodes u v ⟨τ, hout⟩ (hT B' hN.1 u τ v hout) hd

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_att_seatLawsR
#print axioms VerifiableInference.OnPublicFiles.k3_lay_seatLawsR
