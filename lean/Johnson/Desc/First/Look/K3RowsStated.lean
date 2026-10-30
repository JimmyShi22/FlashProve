-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3RowsStated.lean: THE LOOKUP's ROWS AT THE TABLE OF JOINTS, AT WHAT IS
SEATED: at a piece that holds "below B'", B' any block that narrows the value of K3.theStated at the
address of a link's lookup on the calls, AND BEARS THE CAP AS ITS ERRORS: Piece.Own between the
table's promises at the two borders and the items that the row closes and opens. Attention and the
layers. THE TWO ENDS JOINED: the seated constant (Johnson/Desc/First/Look/K3CallsStatedCap.lean) and
the table's door (K3AttAtTable.lean, K3LayAtTable.lean). RULES: their worth is the list of their
premises. NO SOUNDNESS IS CLAIMED.

OBJECT: the value B of K3.theStated claim readers X codes shape a
  (Johnson/Desc/First/Look/K3Stated.lean), and any block B' that narrows it.
Used by K3CallsSeatLaws.lean, K3SeatLawsZ.lean (Johnson/Desc/First/Look/).
LETTERS: those of k3_att_stated, k3_lay_stated; N, Mg, links, ps, k, m, pi: the table's, free, under
  AttAtTable, LayAtTable at the setting Params.settingOf X.P.frame.

Main names:
  `k3_att_atTable_stated`, `k3_lay_atTable_stated`: THE ENDS.

Limits. Those of K3CallsStated.lean, K3AttAtTable.lean, K3LayAtTable.lean, all: NO NAMED PREMISE OF
AttAtTable OR LayAtTable IS SHOWN ANYWHERE; NOTHING IS TRIED FOR EMPTINESS. The record of the chain
is First.S with a fixed public part beside it. What rides past the block (Frames) is not here.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsStatedCap
import Johnson.Desc.First.Look.K3CallsStatedYes
import Johnson.Desc.First.Look.K3LayAtTable

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (ModelPart Item Pub Part Meaning Numbers)

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {pi : P} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE LOOKUP's ROW AT THE TABLE, AT WHAT IS SEATED, at an attention link.** -/
theorem k3_att_atTable_stated (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (H : AttOK (Params.settingOf X.P.frame) x A tl D rad)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp)
    (T : AttAtTable (Fr := Fr) G x A tl D rad (Params.settingOf X.P.frame) seatT arr smp claim N Mg
      links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_att_atTable_of G seatT arr smp p hext H.shape
    (k3_att_stated_cap G seatT arr smp claim readers codes shape a B B' h hOk hN p hp hl hpc e
      hback hext H hr hR hcap hsmp hseat σ₀)
    (fun s τ c hc => by
      obtain ⟨laid, sent, rs, cols, hw, hd⟩ :=
        k3_calls_stated_yes claim readers codes shape a B B' h hOk hN p hp hl hpc e hback s c τ hc
      exact ⟨a.piece, laid, sent, [], rs, cols, hw, hd⟩) T

end

section
variable {P Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {q : LayPub} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)
  {N : Numbers} {Mg : Meaning P (Desc.Wit Cells Tok MsgT)} {links : List ModelPart}
  {ps : List Desc.Place} {pi : P} {k m : ℕ}

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE LOOKUP's ROW AT THE TABLE, AT WHAT IS SEATED, at a layers' link.** -/
theorem k3_lay_atTable_stated (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (H : LayOK (Params.settingOf X.P.frame) x)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp)
    (T : LayAtTable (Fr := Fr) G x q tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
      smp smpW strW msgW claim N Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c)) :
    p.Own (onQ N Mg links ps (fun s => (pi, s)) k) (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_lay_atTable_of G seatT arr smp smpW strW msgW p hext H.shape
    (k3_lay_stated_cap G seatT arr smp smpW strW msgW claim readers codes shape a B B' h hOk hN p
      hp hl hpc e hback hext H hpl hr hR hcap hsmp hsmpW hstrW hseat σ₀ σW₀)
    (fun s τ c hc => by
      obtain ⟨laid, sent, rs, cols, hw, hd⟩ :=
        k3_calls_stated_yes claim readers codes shape a B B' h hOk hN p hp hl hpc e hback s c τ hc
      exact ⟨a.piece, laid, sent, [], rs, cols, hw, hd⟩) T

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_att_atTable_stated
#print axioms VerifiableInference.OnPublicFiles.k3_lay_atTable_stated
