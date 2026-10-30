-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsSeatLaws.lean: the lookup on a link's CALLS: THE FOUR THINGS THAT THE
KIND's AUTHORS OWE AT A SEAT, AS ONE LEMMA, at an attention and at a layers' link: the row's own law
at the table of joints; what rides, in the tie's fenced form; a mark stays; "decodes" rides: each
over every block B' that narrows K3.theStated's value Bst and whose yes bears no mark, and every
value z of the public part. After the pattern of the like at the digits. NO RESULT ON THE PROTOCOL:
EVERY PREMISE THAT IS LEFT IS NAMED; NONE IS SHOWN AT ANY DESCRIPTION.

OBJECT: Desc.K3.theStated claim readers X codes shape a = some Bst, at a.link = some i, a.piece =
  K3.pieceAt X i false; the table's words at block number k of any list of places.
USER: nobody yet. Meant: the premise of the rule that ties a block at a seat, whatever its kind
  (its four arguments), at the written description's value and at the driver's chain.
LETTERS: those of k3_att_atTable_stated, k3_lay_atTable_stated
  (Johnson/Desc/First/Look/K3RowsStated.lean); q: the description's piece over the public part with
  the carried record: of it only base, ds, back, err are read.

Main names: `k3_att_seatLaws`, `k3_lay_seatLaws`. EACH ENDS IN THE NAME SeatLaws links ps k q N Mg
Bst (Johnson/Desc/Sound/TiedSeat.lean), at C := ckP .two and W := Desc.Wit Cells Tok MsgT: BY LEAN.

WHAT IS PAID IN IT: the first conjunct by the rows at the seated constant, at the cap · the third by
k3_calls_stated_yes and k3_calls_sameBut (a yes leaves the mark as it was) · the fourth by the
structure's field decodes. THE SECOND IS A PREMISE HANDED THROUGH (rides).
WHAT IS LEFT, BY NAME: h, hOk, hl, hpc, e · H (and hpl) · hr · hback, hR, hcap, hseat · hsmp (hsmpW,
hstrW) · T: the structure AttAtTable (LayAtTable), AT EVERY B' AND EVERY z · rides.

Limits. A rule over letters.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3RowsStated
import Johnson.Desc.Sound.TiedSeat

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
  {ps : List Desc.Place} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **WHAT IS OWED AT THE CALLS' SEAT OF AN ATTENTION LINK.** -/
theorem k3_att_seatLaws (claim : Aff → Cl)
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
      AttAtTable (Fr := Fr) G x A tl D rad (Params.settingOf X.P.frame) seatT arr smp claim N Mg
        links ps z k m (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c))
    (rides : ∀ B', SeatOf Bst B' →
      ∀ (z : P) a τ b w i,
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
    exact k3_att_atTable_stated G seatT arr smp claim readers codes shape a Bst B' h hOk hN.1 _ rfl
      hl hpc e hback (fun _ _ _ => rfl) H hr hR hcap hsmp hseat σ₀ (T B' hN z)
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
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **WHAT IS OWED AT THE CALLS' SEAT OF A LAYERS' LINK.** -/
theorem k3_lay_seatLaws (claim : Aff → Cl)
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
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) q.ds)),
      strW (behind (ckP .two) Fr q.base q.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < q.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : ∀ B', SeatOf Bst B' →
      ∀ z : P,
      LayAtTable (Fr := Fr) G x ql tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
        smp smpW strW msgW claim N Mg links ps z k m
        (fun a c => ∃ τ, (⟨below B', q.base, q.ds, q.back, fun _ _ w => w, q.err⟩ :
        Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)).ior.red.out a τ = some c))
    (rides : ∀ B', SeatOf Bst B' →
      ∀ (z : P) a τ b w i,
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
    exact k3_lay_atTable_stated G seatT arr smp smpW strW msgW claim readers codes shape a Bst B' h
      hOk hN.1 _ rfl hl hpc e hback (fun _ _ _ => rfl) H hpl hr hR hcap hsmp hsmpW hstrW hseat σ₀
      σW₀ (T B' hN z)
  · intro B' hN u τ v hout hm
    rw [(hT B' hN.1 u τ v hout).failed]
    exact hm
  · intro B' hN z u τ v hout hd
    exact (T B' hN z).decodes u v ⟨τ, hout⟩ (hT B' hN.1 u τ v hout) hd

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_att_seatLaws
#print axioms VerifiableInference.OnPublicFiles.k3_lay_seatLaws
