-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadStated.lean: THE CALLS' END THEOREM AT THE OUTPUT HEAD's LINK AT WHAT
IS SEATED: at a piece that holds "below B'", B' any block that narrows the value of K3.theStated at
the address of the head's lookup on the calls. Three theorems: at the law's own list of errors; AT
THE CAP; AT THE HEAD's LINK OF A PUBLIC RECORD. Carriages: k3_head_goodIn_via
(Johnson/Desc/First/Look/K3HeadVia.lean) laid into k3_seated_goodIn
(Johnson/Desc/Sound/K3Seated.lean); then k3_rounds_at (Johnson/Desc/First/Look/K3RoundsAt.lean) and
goodIn_atCap (Johnson/Desc/Sound/GoodInErr.lean). The head's like of k3_lay_stated
(Johnson/Desc/First/Look/K3CallsStated.lean) and k3_lay_stated_cap
(Johnson/Desc/First/Look/K3CallsStatedCap.lean), binder for binder, but: HeadOK for LayOK; one
premise more: hTok; one premise lighter: e (WHICH PLACE, below). NO SOUNDNESS OF THE PROTOCOL IS
CLAIMED.

OBJECT: the value B of K3.theStated claim readers X codes shape a
  (Johnson/Desc/First/Look/K3Stated.lean), and any block B' that narrows it.
USER: nobody yet. Meant: the "law" of the tie of the first chain's table at the head's lookup on
  the calls (Johnson/Desc/Sound/ChainOfPromises.lean: TiedAt): o := HeadOn, o' := HeadOn', R :=
  HeadFront, R' := HeadBehind.
LETTERS: a: an address with a.link = some i, a.piece = K3.pieceAt X i false; x: a place whose
  parameters are the link's own (placeAt X i false = some (P.ofPlace … x)); the setting:
  Params.settingOf X.P.frame; guests := []; tok: a reader of the record that answers the reply's
  token, or nothing (a filling that meets hTok: k3_head_tok, K3HeadVia.lean).

WHICH PLACE. k3_lay_stated asks "lookAt X i false = some x". lookAt's place bears the plan's record
of the lookup (fs); headAt (K3CallerHead.lean) answers lookAt's place with the record that the
kind's own parameters make laid in. HeadOK's first field says that the parameters make the place's
record: at headAt's place by the make (headOK_at); AT lookAt's OWN PLACE BY THEOREM, wherever
Verify.publicOf returns the public record (head_shape, Johnson/Desc/First/Look/K3CallerAtPlan.lean):
there the two records are one. The two places have the same parameters: P.ofPlace does not read fs
(placeAt_headAt), and the block reads its parameters alone. So here the premise is on the
parameters: it is lighter than k3_lay_stated's, and both places meet it.

How it goes. As at a layers' link. Behind the lookup on the calls no step turns the record
(quiet_calls_same, K3CallsStated.lean: at the head there is none).

Limits. Those of K3HeadVia.lean, K3HeadGoodIn.lean, K3CallerHead.lean and K3CallsStated.lean. IN THE
FIRST TWO THEOREMS NOTHING SAYS THAT i IS THE HEAD's LINK: they hold at every link at which HeadOK
holds of the place: it is HeadOK (premises on public data) that speaks of the head. The premises on
the readers (hsmp, hsmpW, hTok) are asked at every pair of arguments (what must have been sent; the
count of padding places) AT WHICH blockVia's OWN TEST ON THE PLAN SAYS YES: lighter than
k3_lay_stated's, and just what k3_head_tok pays. That B' narrows B is a premise. The head's files'
three classes, adr, oW, wOf, nr, nc, floor are letters. The lift over the public part is not here.
The five ties to the table are not here.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3HeadVia
import Johnson.Desc.First.Look.K3CallerHeadTests
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
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider HeadOK head_says)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy] [Desc.Kinds.Head.Request]

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {adr : HeadAdr} {x : Desc.First.Look.Place} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc floor : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (tok : Desc.First.S → Option ℕ)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- **THE END THEOREM AT WHAT IS SEATED, at the head's link**, at the law's own list of errors. -/
theorem k3_head_stated (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (H : HeadOK (Params.settingOf X.P.frame) x floor)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hTok : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → tok s' = tok s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOn G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link))
      (HeadOn' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => (tok s).getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) := by
  refine k3_seated_goodIn claim readers X codes shape a B B' h hOk hN p hp _
    (HeadOn' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard (OwnIs D x.link)) _ _
    (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
      (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard) _ ?_ ?_ ?_
  · intro j digits P sent laid hj hpj hP _ _ hplan
    obtain rfl : i = j := Option.some.inj (hl.symm.trans hj)
    cases digits with
    | true => exact absurd (hpj.symm.trans hpc) (pieceAt_ne X i)
    | false =>
      have eP : P = theP := Option.some.inj (hP.symm.trans e)
      subst eP
      exact k3_head_goodIn_via G seatT arr smp smpW strW msgW tok claim a.piece laid sent [] _ rfl
        hplan hback hext H hpl hr hR hε (hsmp sent laid hplan) (hsmpW sent laid hplan)
        (hTok sent laid hplan) hstrW
        hseat σ₀ σW₀
  · intro f hf s' t y ht ho
    obtain rfl := quiet_calls_same X a i hl hpc f hf s' t ht
    exact ⟨ho, fun _ hw => hw⟩
  · intro _
    exact ⟨fun _ hb => hb, fun _ _ hw => hw⟩

/-- A piece whose errors are c is the piece with any errors laid and then c laid. -/
theorem piece_err_back' {S Cl W : Type} {C : Run.PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (ε c : Err (uLT C p.ds)) (h : p.err = c) :
    ({ ({ p with err := ε } : Piece C F S Cl W) with err := c } : Piece C F S Cl W) = p := by
  cases p
  subst h
  rfl

/-- **THE END THEOREM AT WHAT IS SEATED, AT THE CAP, at the head's link.** -/
theorem k3_head_stated_cap (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hl : a.link = some i) (hpc : a.piece = Desc.K3.pieceAt X i false)
    (e : placeAt X i false = some theP)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (H : HeadOK (Params.settingOf X.P.frame) x floor)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hTok : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → tok s' = tok s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOn G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link))
      (HeadOn' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => (tok s).getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) := by
  obtain ⟨-, ε', e', -, -, hle⟩ := k3_rounds_at theR theP H.shape
    (by
      show 1 < x.fs.NC
      rw [H.six]
      decide) hr p.ds hR
  have g := k3_head_stated (adr := adr) (tl := tl) (wOf := wOf) (nr := nr) (nc := nc) G seatT arr
    smp smpW strW msgW tok claim readers codes shape a B B' h hOk hN
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hp hl hpc e hback hext H hpl hr hR e' hsmp hsmpW hTok hstrW hseat σ₀ σW₀
  have g2 := goodIn_atCap
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hle _ _ _ _ g
  rw [piece_err_back' p ε' _ hcap] at g2
  exact g2

/-- The head's link's number, by headAt's own term. -/
def headLink (X : Verify.Public) : ℕ := (if X.p4 then 2 else 1) * X.NGr

/-- **The parameters at headAt's place are the link's own**: P.ofPlace does not read the place's
record of the lookup. -/
theorem placeAt_headAt {X : Verify.Public} {x : Desc.First.Look.Place}
    (hx : Desc.Kinds.Head.Law.headAt X = some x) :
    placeAt X (headLink X) false =
      some (Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x) := by
  unfold Desc.Kinds.Head.Law.headAt at hx
  obtain ⟨x', h1, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', -, hx⟩ := Option.map_eq_some_iff.1 hx
  subst hx
  unfold placeAt headLink
  rw [h1]
  rfl

/-- **At headAt's place the one Bool is all that is asked.** -/
theorem headOK_at {X : Verify.Public} {x : Desc.First.Look.Place} {floor : ℕ}
    (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (hB : Desc.Kinds.Head.Law.headB floor x.fs = true) :
    HeadOK (Params.settingOf X.P.frame) x floor := by
  refine Desc.Kinds.Head.Law.headOK_of ?_ hB
  unfold Desc.Kinds.Head.Law.headAt at hx
  obtain ⟨x', -, hx⟩ := Option.bind_eq_some_iff.1 hx
  obtain ⟨h', hh, hx⟩ := Option.map_eq_some_iff.1 hx
  subst hx
  exact hh

/-- **THE END THEOREM AT WHAT IS SEATED, AT THE CAP, AT THE HEAD's LINK OF A PUBLIC RECORD**: the
place is headAt's; the link is the head's; HeadOK is one Bool. -/
theorem k3_head_stated_at (claim : Aff → Cl)
    (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
    (codes : Codes) (shape : Params.ReqShape) (a : Desc.Place)
    (B B' : Desc.Block Desc.First.S Cl)
    (h : Desc.K3.theStated claim readers X codes shape a = some B) (hOk : B.planOk = true)
    (hN : B'.Narrows B)
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hp : p.b = below B')
    (hx : Desc.Kinds.Head.Law.headAt X = some x)
    (hl : a.link = some (headLink X)) (hpc : a.piece = Desc.K3.pieceAt X (headLink X) false)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w)
    (hB : Desc.Kinds.Head.Law.headB floor x.fs = true)
    (hpl : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (theP).entries.isSome = true) (hR : List.Forall₂ SameAs p.ds (theP).rounds)
    (hcap : p.err = Err.cap 128 (uLT (ckP .two) p.ds))
    (hsmp : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hTok : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → tok s' = tok s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOn G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link))
      (HeadOn' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => (tok s).getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_head_stated_cap (floor := floor) G seatT arr smp smpW strW msgW tok claim readers codes shape
    a B B' h hOk hN p hp hl hpc (placeAt_headAt hx) hback hext (headOK_at hx hB) hpl hr hR hcap
    hsmp hsmpW hTok hstrW hseat σ₀ σW₀

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_head_stated
#print axioms VerifiableInference.OnPublicFiles.k3_head_stated_cap
#print axioms VerifiableInference.OnPublicFiles.placeAt_headAt
#print axioms VerifiableInference.OnPublicFiles.headOK_at
#print axioms VerifiableInference.OnPublicFiles.k3_head_stated_at
