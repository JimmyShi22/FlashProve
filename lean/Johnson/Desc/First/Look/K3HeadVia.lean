-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadVia.lean: THE CALLS' END THEOREM AT THE OUTPUT HEAD's LINK AT THE
LOOKUP's BLOCK WITH THE HEARING EXCHANGED (K3.Law.blockVia, Johnson/Desc/First/Look/Via/Via.lean),
WITH THE TOKEN FENCED. The head's like of Johnson/Desc/First/Look/K3LayVia.lean. Definitions,
statements and proofs. NO SOUNDNESS OF THE PROTOCOL IS CLAIMED.

OBJECT: Desc.K3.Law.blockVia's decide, at the calls' seat.
USER: Johnson/Desc/First/Look/K3HeadStated.lean.
LETTERS: seat := seatCalls claim; piece, laid, before, guests free; p := P.ofPlace set false x; tok:
  a reader of the record that answers the reply's token, or nothing.

Why a fence. k3_head_goodIn_any (Johnson/Desc/First/Look/K3HeadGoodIn.lean) takes the token as a
reader tokOf : S → ℕ. Its condition in front (LayOn) does not say that a token WAS heard: at a
reader that answers a default where none was heard, HeadFront would speak of that default, in
silence. Here the
reader is an Option, tokOf is its value or 0, AND "THE READER ANSWERS" STANDS IN THE CONDITION IN
FRONT AND IN THE PROMISE BEHIND.
  goodIn_fence: general in the piece: a fact I in front that a yes of the piece carries to I' behind
    can be laid beside the condition and the promise of any GoodIn.
  HeadOn, HeadOn': LayOn and LayOn', and the reader answers.
  k3_head_goodIn_via: THE END THEOREM at blockVia, between HeadOn, HeadOn', HeadFront, HeadBehind.
  k3_head_tok: THE READER HAS A FILLING: the record's own replyTok? (Johnson/Desc/First/State.lean:
    what was heard as the reply, as a token's number) is not turned by a yes of blockVia at the
    calls' seat: by k3_calls_sameBut (Johnson/Desc/First/Look/K3CallsTurns.lean): the field "out"
    stays.

Limits. Those of K3HeadGoodIn.lean and K3CallerHead.lean. One way: nothing is said on where blockVia
says yes. ONE PUBLIC PREMISE MORE than k3_head_goodIn_any: blockVia's planOk says yes. That the
reply IS heard in front of this block is the condition's word, shown of no description.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3HeadGoodIn
import Johnson.Desc.First.Look.K3CallsTurns
import Johnson.Top.H.K3Via.Blocks

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider HeadOK head_says)

/-- **A fact that a yes carries can stand beside the condition and the promise.** -/
theorem goodIn_fence {S Cl W : Type} {C : _root_.Run.PQ.CK} {F : Frame} (p : Piece C F S Cl W)
    (on on' I I' : S × F.E.Str → Prop) (R R' : S × F.E.Str → W → Prop)
    (hk : ∀ a τ b, I a → p.ior.red.out a τ = some b → I' b) (g : p.GoodIn on on' R R') :
    p.GoodIn (fun a => on a ∧ I a) (fun b => on' b ∧ I' b) R R' := fun a ha =>
  Doomed.mono _ _ (fun τ hτ b hb => ⟨⟨(hτ b hb).1, hk a τ b ha.2 hb⟩, (hτ b hb).2⟩) (g a ha.1)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy] [Desc.Kinds.Head.Request]

section
variable {S Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi)
  (x : Desc.First.Look.Place) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ)
  (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
  (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str) (tok : S → Option ℕ)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard) (Own : S → Prop)

/-- **The condition in front at the head**: the layers', and a token is heard. -/
def HeadOn (a : S × Fr.E.Str) : Prop :=
  LayOn G x D rad oW seatT smp smpW strW fork Own a ∧ (tok a.1).isSome = true

/-- **The promise behind at the head**: the layers', and a token is heard. -/
def HeadOn' (a : S × Fr.E.Str) : Prop :=
  LayOn' G x D rad oW seatT smp smpW strW fork heard Own a ∧ (tok a.1).isSome = true

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
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (tok : Desc.First.S → Option ℕ)

local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- **THE END THEOREM AT THE BLOCK WITH THE HEARING EXCHANGED, at the head's link.** -/
theorem k3_head_goodIn_via (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
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
  goodIn_fence p _ _ (fun a => (tok a.1).isSome = true) (fun b => (tok b.1).isSome = true) _ _
    (fun a τ b hI ho => by
      show (tok b.1).isSome = true
      rw [hTok _ _ _ _ (piece_below_yes p _ hb a b τ ho).2.2.1]
      exact hI)
    (k3_head_goodIn_any G seatT arr smp smpW strW msgW (fun s => (tok s).getD 0) claim piece laid
      before guests _ (fun _ _ _ _ h => Desc.K3.Law.blockVia_decide hplan h) p hb hback hext H hp
      hr hR hε hsmp hsmpW (fun s rs cols s' h => congrArg (·.getD 0) (hTok s rs cols s' h)) hstrW
      hseat σ₀ σW₀)

end

/-- **The reader has a filling**: a yes of blockVia at the calls' seat does not turn the record's
own reading of the heard reply as a token. -/
theorem k3_head_tok {Cl : Type} (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (P : Desc.First.Look.P)
    (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (hplan : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before P guests).planOk =
      true)
    (s s' : Desc.First.S) (rs : List Fmt.RoundView) (cols : List (List (ℕ × List UInt64)))
    (h : (Desc.K3.Law.blockVia (Desc.K3.seatCalls claim) piece laid before P guests).decide s rs
      cols = .ok s') : s'.replyTok? = s.replyTok? := by
  have e := (k3_calls_sameBut claim piece laid before P guests s s' rs cols
    (Desc.K3.Law.blockVia_decide hplan h)).out
  unfold Desc.First.S.replyTok?
  rw [e]

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.goodIn_fence
#print axioms VerifiableInference.OnPublicFiles.k3_head_goodIn_via
#print axioms VerifiableInference.OnPublicFiles.k3_head_tok
