-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No real place of a stored set is shown at which all premises hold together.
Johnson/Desc/First/Look/K3CallsStatedCap.lean: THE CALLS' END THEOREMS AT WHAT IS SEATED, AT A PIECE
WHOSE ERRORS ARE THE CAP (Err.cap 128, Iop/ErrCap.lean): what the pieces of a description's real
rows bear. Two theorems: attention, the layers. Carriages: k3_att_stated, k3_lay_stated
(Johnson/Desc/First/Look/K3CallsStated.lean) at the piece with the law's own errors laid, then up to
the cap by goodIn_atCap (Johnson/Desc/Sound/GoodInErr.lean) with k3_rounds_at
(Johnson/Desc/First/Look/K3RoundsAt.lean: the law's errors lie under the cap round by round). NO
SOUNDNESS OF THE PROTOCOL IS CLAIMED.

OBJECT: the value B of K3.theStated claim readers X codes shape a, and any block B' that narrows it;
  the piece bears Err.cap 128.
USER: k3_att_atTable_stated, k3_lay_atTable_stated (Johnson/Desc/First/Look/K3RowsStated.lean).
LETTERS: those of k3_att_stated, k3_lay_stated.

Why. k3_att_stated and k3_lay_stated ask that the piece's errors ARE the law's own list (the premise
on bearT): at a piece that bears the cap that is false: they speak of another piece than the rule
holds.

Limits. Those of K3CallsStated.lean, but the premise on bearT, which falls: hcap stands in its
place.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsStated
import Johnson.Desc.First.Look.K3RoundsAt
import Johnson.Desc.Sound.GoodInErr

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound

/-- A piece whose errors are c is the piece with any errors laid and then c laid. -/
theorem piece_err_back {S Cl W : Type} {C : Run.PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (ε c : Err (uLT C p.ds)) (h : p.err = c) :
    ({ ({ p with err := ε } : Piece C F S Cl W) with err := c } : Piece C F S Cl W) = p := by
  cases p
  subst h
  rfl

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {A : Attention.Shape} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE END THEOREM AT WHAT IS SEATED, AT THE CAP, at an attention link.** -/
theorem k3_att_stated_cap (claim : Aff → Cl)
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
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) :
    p.GoodIn
      (AttOn G x D rad seatT smp (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (AttOn' G x D rad seatT smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (AttFront G x A tl D rad seatT arr smp)
      (AttBehind G x A tl D rad seatT arr smp (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) := by
  obtain ⟨-, ε', e', -, -, hle⟩ := k3_rounds_at (attRider x A tl D rad extNone Unit) theP H.shape
    (by
      show 1 < x.fs.NC
      rw [H.four]
      decide) hr p.ds hR
  have g := k3_att_stated G seatT arr smp claim readers codes shape a B B' h hOk hN
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hp hl hpc e hback hext H hr hR e' hsmp hseat σ₀
  have g2 := goodIn_atCap
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hle _ _ _ _ g
  rw [piece_err_back p ε' _ hcap] at g2
  exact g2

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {x : Desc.First.Look.Place} {q : LayPub} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE END THEOREM AT WHAT IS SEATED, AT THE CAP, at a layers' link.** -/
theorem k3_lay_stated_cap (claim : Aff → Cl)
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
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (LayFront G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW)
      (LayBehind G x q tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) := by
  obtain ⟨-, ε', e', -, -, hle⟩ := k3_rounds_at (layRider x q tl D rad oW wOf nr nc extNone Unit)
    theP H.shape
    (by
      show 1 < x.fs.NC
      rw [H.eight]
      decide) hr p.ds hR
  have g := k3_lay_stated G seatT arr smp smpW strW msgW claim readers codes shape a B B' h hOk hN
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hp hl hpc e hback hext H hpl hr hR e' hsmp hsmpW hstrW hseat σ₀ σW₀
  have g2 := goodIn_atCap
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hle _ _ _ _ g
  rw [piece_err_back p ε' _ hcap] at g2
  exact g2

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_att_stated_cap
#print axioms VerifiableInference.OnPublicFiles.k3_lay_stated_cap
