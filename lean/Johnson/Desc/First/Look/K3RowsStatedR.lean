-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
No witness and no real list of rounds is shown at which all premises hold.
Johnson/Desc/First/Look/K3RowsStatedR.lean: THE LOOKUP's ROWS ON THE CALLS AT THE TABLE OF JOINTS,
AT WHAT IS SEATED (Desc.K3.theStated's value), IN THE SECOND FORM OF THE CHAIN OF PROMISES: the two
theorems of K3RowsStated.lean over AttAtTableR and LayAtTableR: they end in p.Own (onR ...) (onQ ...
(k + 1)).
THE TEXT IS THE FIRST FORM's (Johnson/Desc/First/Look/K3RowsStated.lean), TURNED BY A PROGRAM, after
the pattern at the
head's calls (Johnson/Desc/First/Look/K3HeadAtTableR.lean); the law beneath is called as it lies;
the first form's file is not touched. NO SOUNDNESS IS CLAIMED.

Used by K3CallsSeatLawsR.lean (Johnson/Desc/First/Look/).
OBJECT, LETTERS: the first form's; and Rc (Rch): a condition on the statement that stands
  beside the table's promise in front (meant: "this verifier's state is reached from the state at
  the start by the sub-protocols in front"): A LETTER: no term is named here.

Main names: `k3_att_atTable_statedR`, `k3_lay_atTable_statedR`.

Limits. The first form's. Rc is a letter; ownIn is a premise, shown at no term.
Not claimed: anything on soundness, completeness or hiding.

-/
import Johnson.Desc.First.Look.K3CallsStatedCap
import Johnson.Desc.First.Look.K3CallsStatedYes
import Johnson.Desc.First.Look.K3AttAtTableR
import Johnson.Desc.First.Look.K3LayAtTableR

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
  {ps : List Desc.Place} {pi : P} {k m : ℕ} (Rc : Desc.First.S × Fr.E.Str → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE LOOKUP's ROW AT THE TABLE, AT WHAT IS SEATED, at an attention link.** -/
theorem k3_att_atTable_statedR (claim : Aff → Cl)
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
    (T : AttAtTableR (Fr := Fr) G x A tl D rad (Params.settingOf X.P.frame) seatT arr smp claim N
      Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c) Rc) :
    p.Own (onR N Mg links ps (fun s => (pi, s)) (fun _ => Rc) k)
      (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_att_atTable_ofR G seatT arr smp Rc p hext H.shape
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
  {ps : List Desc.Place} {pi : P} {k m : ℕ} (Rc : Desc.First.S × Fr.E.Str → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x

/-- **THE LOOKUP's ROW AT THE TABLE, AT WHAT IS SEATED, at a layers' link.** -/
theorem k3_lay_atTable_statedR (claim : Aff → Cl)
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
    (T : LayAtTableR (Fr := Fr) G x q tl D rad oW wOf nr nc (Params.settingOf X.P.frame) seatT arr
      smp smpW strW msgW claim N Mg links ps pi k m (fun a c => ∃ τ, p.ior.red.out a τ = some c)
      Rc) :
    p.Own (onR N Mg links ps (fun s => (pi, s)) (fun _ => Rc) k)
      (onQ N Mg links ps (fun s => (pi, s)) (k + 1))
      (meansQ N Mg (fun s => (pi, s))) (insQ links ps k) (outsQ links ps k) :=
  k3_lay_atTable_ofR G seatT arr smp smpW strW msgW Rc p hext H.shape
    (k3_lay_stated_cap G seatT arr smp smpW strW msgW claim readers codes shape a B B' h hOk hN p
      hp hl hpc e hback hext H hpl hr hR hcap hsmp hsmpW hstrW hseat σ₀ σW₀)
    (fun s τ c hc => by
      obtain ⟨laid, sent, rs, cols, hw, hd⟩ :=
        k3_calls_stated_yes claim readers codes shape a B B' h hOk hN p hp hl hpc e hback s c τ hc
      exact ⟨a.piece, laid, sent, [], rs, cols, hw, hd⟩) T

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_att_atTable_statedR
#print axioms VerifiableInference.OnPublicFiles.k3_lay_atTable_statedR
