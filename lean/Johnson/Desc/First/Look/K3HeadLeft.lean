-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadLeft.lean: THE CALLS' END THEOREM AT THE OUTPUT HEAD's LINK AT WHAT IS
SEATED, AT THE CAP, WITH THE LOOKUP's SHARP PROMISE LAID BESIDE: behind a yes the record holds WHAT
THE LOOKUP LEFT (K3LeftAt, Johnson/Top/H/K3LeftStatement.lean): there are a ledger F in front, with
Q F and F.next the place's first slot, a ledger F' behind, what was heard g, and rounds rs with
K3Left … F F' g rs; g is what the record has heard and F' the ledger in hand. Definitions, four
theorems. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

Why. The table of joints' public item "left m" (Johnson/Desc/First/Borders.lean) is meant to say
K3LeftAt: made by the lookup's row at the calls, asked and dropped by the caller's. LayOn' (the
first half of HeadOn', the promise of k3_head_stated_cap,
Johnson/Desc/First/Look/K3HeadStated.lean) says less: that a sized
ledger and what was heard stand for SOME rounds; nothing of the ledger in front.
k3_left_beside (Johnson/Desc/First/Look/K3LeftAll.lean) lays the sharp promise beside ANY end
theorem whose condition in front is COn: here it is called at the head's.

OBJECT, LETTERS: those of K3HeadStated.lean; Q: any fact on the ledger in front; I, I': any facts on
  the record such that a yes of the block carries I in front to I' behind (hKeep): they ride beside.
USER: k3_head_free_at (Johnson/Desc/First/Look/K3KeepsFree.lean), which calls k3_head_left_at.
  Meant: o and o' of the tie of the first chain's table at the head's lookup on the
  calls, so that "left" at the border behind has its maker in o'.
  HeadOnQ, HeadOnQ': HeadOn with "Q of the ledger in hand" and I; HeadOn' with K3LeftAt at Q and I'.
  k3_head_left_via, k3_head_left_stated: at blockVia; at what is seated, at the law's own errors.
  k3_head_left_cap: the end theorem at the cap between HeadOnQ, HeadOnQ', HeadFront, HeadBehind.
  k3_head_left_at: the same at the head's link of a public record (headAt; one Bool for HeadOK).

Limits. Those of K3HeadStated.lean and K3LeftAll.lean. Q is a letter: at Q := "true of all" K3LeftAt
still names the ledger in front and its next slot. That the table's item is filled with K3LeftAt is
nobody's yet.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3HeadStated
import Johnson.Desc.First.Look.K3LeftAll

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
variable {S Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
  (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str) (tok : S → Option ℕ)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard) (Own : S → Prop) (Q : Fork → Prop)
  (I : S → Prop)

/-- **The condition in front**: the layers'; Q of the ledger in hand; a token is heard; I of the
record. -/
def HeadOnQ (a : S × Fr.E.Str) : Prop :=
  (LayOn G x D rad oW seatT smp smpW strW fork Own a ∧ ∀ F, fork a.1 = some F → Q F) ∧
    (tok a.1).isSome = true ∧ I a.1

/-- **The promise behind**: the layers'; WHAT THE LOOKUP LEFT; a token is heard; I of the record. -/
def HeadOnQ' (a : S × Fr.E.Str) : Prop :=
  (LayOn' G x D rad oW seatT smp smpW strW fork heard Own a ∧
      K3LeftAt fork heard x.fs x.lm x.F.next Q a.1) ∧
    (tok a.1).isSome = true ∧ I a.1

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) {adr : HeadAdr}
  {x : Desc.First.Look.Place} {tl : HTailF2} {D : Desc.First.Look.Sent}
  {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E} {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc : ℕ}
  {set : Params.Setting} {floor : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (tok : Desc.First.S → Option ℕ) (Q : Fork → Prop)
  (I I' : Desc.First.S → Prop)

local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- **At the block with the hearing exchanged**, with what the lookup left. -/
theorem k3_head_left_via (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (hb : p.b = below (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).planOk = true)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : HeadOK set x floor)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → smpW s' = smpW s)
    (hTok : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → tok s' = tok s)
    (hKeep : ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before
      (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s' → I s → I' s')
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOnQ G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link) Q I)
      (HeadOnQ' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q I')
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => (tok s).getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  goodIn_fence p _ _ (fun a => (tok a.1).isSome = true ∧ I a.1)
    (fun b => (tok b.1).isSome = true ∧ I' b.1) _ _
    (fun a τ b hI ho => by
      have hd := (piece_below_yes p _ hb a b τ ho).2.2.1
      refine ⟨?_, hKeep _ _ _ _ hd hI.2⟩
      rw [hTok _ _ _ _ hd]
      exact hI.1)
    (k3_left_beside claim piece laid before guests _
      (fun _ _ _ _ h => Desc.K3.Law.blockVia_decide hplan h) p hb hback H.shape _ _ _ _
      (k3_head_goodIn_any G seatT arr smp smpW strW msgW (fun s => (tok s).getD 0) claim piece laid
        before guests _ (fun _ _ _ _ h => Desc.K3.Law.blockVia_decide hplan h) p hb hback hext H hp
        hr hR hε hsmp hsmpW (fun s rs cols s' h => congrArg (·.getD 0) (hTok s rs cols s' h)) hstrW
        hseat σ₀ σW₀) Q)

end

section
variable {Cl Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  {X : Verify.Public} {i : ℕ} {adr : HeadAdr} {x : Desc.First.Look.Place} {tl : HTailF2}
  {D : Desc.First.Look.Sent} {rad : OracleShape → ℕ} {oW : Cb.OMsg Cb.Gl.E}
  {wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E} {nr nc floor : ℕ}
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : Desc.First.S → (i : Fin (sigListCalls D rad x.link).length) →
    Option ((attSg x D rad).om i).Smp)
  (smpW : Desc.First.S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (tok : Desc.First.S → Option ℕ) (Q : Fork → Prop)
  (I I' : Desc.First.S → Prop)

local notation "theP" => Desc.First.Look.P.ofPlace (Params.settingOf X.P.frame) false x
local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- **At what is seated**, at the law's own list of errors, with what the lookup left. -/
theorem k3_head_left_stated (claim : Aff → Cl) (readers : ℕ → Option (Desc.K3.Readers Desc.First.S))
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
    (hKeep : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → I s → I' s')
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOnQ G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link) Q I)
      (HeadOnQ' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q I')
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => (tok s).getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) := by
  refine k3_seated_goodIn claim readers X codes shape a B B' h hOk hN p hp _
    (HeadOnQ' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
      (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q I') _ _
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
      exact k3_head_left_via G seatT arr smp smpW strW msgW tok Q I I' claim a.piece laid sent [] _
        rfl
        hplan hback hext H hpl hr hR hε (hsmp sent laid hplan) (hsmpW sent laid hplan)
        (hTok sent laid hplan) (hKeep sent laid hplan) hstrW
        hseat σ₀ σW₀
  · intro f hf s' t y ht ho
    obtain rfl := quiet_calls_same X a i hl hpc f hf s' t ht
    exact ⟨ho, fun _ hw => hw⟩
  · intro _
    exact ⟨fun _ hb => hb, fun _ _ hw => hw⟩

/-- **THE END THEOREM AT WHAT IS SEATED, AT THE CAP, WITH WHAT THE LOOKUP LEFT**, at the head's
link. -/
theorem k3_head_left_cap (claim : Aff → Cl)
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
    (hKeep : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → I s → I' s')
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOnQ G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link) Q I)
      (HeadOnQ' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q I')
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
  have g := k3_head_left_stated (adr := adr) (tl := tl) (wOf := wOf) (nr := nr) (nc := nc) G seatT
    arr smp smpW strW msgW tok Q I I' claim readers codes shape a B B' h hOk hN
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hp hl hpc e hback hext H hpl hr hR e' hsmp hsmpW hTok hKeep hstrW hseat σ₀ σW₀
  have g2 := goodIn_atCap
    ({ p with err := ε' } : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    hle _ _ _ _ g
  rw [piece_err_back' p ε' _ hcap] at g2
  exact g2

/-- **THE SAME AT THE HEAD's LINK OF A PUBLIC RECORD.** -/
theorem k3_head_left_at (claim : Aff → Cl)
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
    (hKeep : ∀ sent laid, (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece laid sent theP
      []).planOk = true → ∀ s rs cols s', (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) a.piece
      laid sent theP []).decide s rs cols = .ok s' → I s → I' s')
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (HeadOnQ G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (OwnIs D x.link) Q I)
      (HeadOnQ' G x D rad oW seatT smp smpW strW tok (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link) Q I')
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        fun s => (tok s).getD 0)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW
        (fun s => (tok s).getD 0) (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard) :=
  k3_head_left_cap (floor := floor) G seatT arr smp smpW strW msgW tok Q I I' claim readers codes
    shape a B B' h hOk hN p hp hl hpc (placeAt_headAt hx) hback hext (headOK_at hx hB) hpl hr hR
    hcap hsmp hsmpW hTok hKeep hstrW hseat σ₀ σW₀

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.k3_head_left_via
#print axioms VerifiableInference.OnPublicFiles.k3_head_left_stated
#print axioms VerifiableInference.OnPublicFiles.k3_head_left_cap
#print axioms VerifiableInference.OnPublicFiles.k3_head_left_at
