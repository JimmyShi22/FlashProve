-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/First/Look/K3HeadGoodIn.lean: THE CLOSING FILE OF A FOURTH CHAIN: the lookup on the
CALLS of THE OUTPUT HEAD's link, WITH ITS RIDERS: from the law on the kind's decide and the closed
caller (Johnson/Desc/First/Look/K3CallerHead.lean: headRider) to the form that the rule of
composition asks of a block (Piece.GoodIn): an instance of k3_goodIn_calls
(Johnson/Desc/First/Look/K3GoodInCalls.lean). Definitions, and one theorem with two corollaries. NO
SOUNDNESS OF THE PROTOCOL IS CLAIMED: the premises that are not theorems are premises.

WHAT DIFFERS FROM THE LAYERS (Johnson/Desc/First/Look/K3LayGoodIn.lean), whose signature, readers,
LayCond, LayPin, LayOn and LayOn' it shares. THE CALLER's STATE IS THE REPLY's TOKEN THAT WAS HEARD:
a part of the statement in front: here a reader of the record, tokOf, A LETTER, with one law: a yes
of decide does not turn it (hTok). The keys are the head's kind's own table at that token; the
riders are its two guests' arrays at the last places of zx.

THE END THEOREM k3_head_goodIn_any: at a piece p that holds "below b", b any block whose decide says
yes only where K3.block's does at the calls' seat and the place x, and under the twelve further
hypotheses of its statement (hback · hext · H · hp · hr · hR · hε · hsmp · hsmpW · hTok · hstrW ·
hseat): p has GoodIn between
  on   LayOn · on' LayOn': as at the layers;
  RA   HeadFront: LayPin, AND (HeadSays, at the record's token) every place of every call's key
       vector is a row of its table in the verifier's record, AND the two guests' arrays are 0 on
       their cubes;
  RB   HeadBehind: LayPin still; THE ROW OUT (K3Out) at the record's token; AND ITS FOURTH ITEM
       (K3OutRider) at the same token.
  err  the least written errors that bear the proved block's; k3_head_err: each ≤ 2^-157.

THE RIDERS ARE IN THE CHAIN ON THE PROVED BLOCK's SIDE, AND NOWHERE ON THE TEXT's: "guests" is a
letter that decide and the four relations never read.

Limits. Those of K3LayGoodIn.lean and K3CallerHead.lean. tokOf IS TIED TO NO TEXT: that it reads the
token that the head's kind has heard is nobody's yet. adr, oW, wOf, nr, nc and the head's kind's
three classes are letters. The guards of the reading (planesAtB, masksAtB; the cells that adr
names) stand beside, or nowhere.
Not claimed: anything on completeness or hiding.

-/
import Johnson.Desc.First.Look.K3LayGoodIn
import Johnson.Desc.First.Look.K3CallerHead

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace VerifiableInference.OnPublicFiles
open KObj Iop Prob Hiop IOR Cb Cb.Fo Cb.Fo.NumsEq Cb.LdLkp Cb.Lkp Cb.Rider TWhole TwV Tw
open OnBytes OnBytes.Slice OnBytes.Flat OnBytes.Model OnBytes.Maker Run Fo Fo.Peel TwRound
open Cb.Fo.Pin
open VerifiableInference.Desc.First.Look VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Kinds.Head.Law (HeadAdr headLay headRider HeadOK head_says)

variable [Desc.Kinds.Head.Sizes] [Desc.Kinds.Head.Policy] [Desc.Kinds.Head.Request]

section
variable {S Cells Tok Xi : Type} {Fr : Frame} (G : Desc.FileDescription Xi) (adr : HeadAdr)
  (x : Desc.First.Look.Place) (tl : HTailF2) (D : Desc.First.Look.Sent)
  (rad : OracleShape → ℕ) (oW : Cb.OMsg Cb.Gl.E) (wOf : oW.Msg → ℕ → ℕ → Cb.Gl.E) (nr nc : ℕ)
  (seatT : Fin (sigListCalls D rad x.link).length → ℕ × ℕ) (arr : ℕ → ℕ → ℕ)
  (smp : S → (i : Fin (sigListCalls D rad x.link).length) → Option ((attSg x D rad).om i).Smp)
  (smpW : S → Option oW.Smp) (strW : Fr.E.Str → oW.Str)
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (tokOf : S → ℕ)
  (fork : S → Option Fork) (heard : S → Option Forest.Heard)

local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- **What the joint in front says of a tuple of messages, at a token** (head_says' right side). -/
def HeadSays (y : ℕ) (m : (laySg x D rad oW).Msg) : Prop :=
  (∀ k < x.fs.NC, ∀ b < 2 ^ Cb.LdLkp.Port.nOf x.fs k, ∃ u < 2 ^ Cb.LdLkp.Port.kOf x.fs k,
    (headLay adr x.fs x.lm x.F.next x.ns tl nr nc).K y (msgLay x tl D rad oW wOf nr nc m) k b =
      ((FoNums.tauN x.fs k u : ℕ) : Cb.Gl.E)) ∧
  (theR).src m (y, ())

/-- The reading of the places: a mask, a cell of the planes' matrix. -/
def headNu (w : Desc.Wit Cells Tok MsgT) (pq : _root_.Fo.Pl) : Cb.Gl.E :=
  zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w)
    (placeOf (lyMask x.ns tl nr nc) (lyCell x.ns tl nr nc adr.iB) pq)

/-- **The relation in front.** -/
def HeadFront (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  LayPin G x D rad oW seatT arr smp smpW strW msgW a w ∧
    HeadSays adr x tl D rad oW wOf nr nc (tokOf a.1) (layMs x D rad oW seatT arr msgW w)

/-- **The relation behind: what the later blocks owe.** -/
def HeadBehind (a : S × Fr.E.Str) (w : Desc.Wit Cells Tok MsgT) : Prop :=
  LayPin G x D rad oW seatT arr smp smpW strW msgW a w ∧
    ∃ (g : Forest.Heard) (F' : Fork), fork a.1 = some F' ∧ heard a.1 = some g ∧
      K3Out x.fs x.lm x.F.next (headNu adr x tl D rad oW wOf nr nc seatT arr msgW w)
        (forK Cb.Gl.E (headLay adr x.fs x.lm x.F.next x.ns tl nr nc) (tokOf a.1)
          (zext (layMu x tl D rad oW wOf nr nc seatT arr msgW w))) Reading.gl g F' ∧
      K3OutRider theR x.lm x.F.next (tokOf a.1) (layMs x D rad oW seatT arr msgW w) g F'

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
  (msgW : Desc.Wit Cells Tok MsgT → oW.Msg) (tokOf : Desc.First.S → ℕ)

local notation "theR" => headRider adr x tl D rad oW wOf nr nc extNone Unit

/-- The riders' choice of places is lawful. -/
theorem head_sel (H : HeadOK set x floor) : SelLookupCR [theR] :=
  riderOf_sel fun Gd hG => by
    obtain ⟨z, _, rfl⟩ := List.mem_map.1 hG
    exact tailId_lawful (foOk_of_shape H.shape) H.tail z.1 z.2

/-- **THE END THEOREM OF THE CALLS' CHAIN AT THE HEAD's LINK, at any block whose decide says yes
only where K3.block's does.** -/
theorem k3_head_goodIn_any (claim : Aff → Cl) (piece : ℕ) (laid : Array Nat)
    (before : List (ℕ × ℕ)) (guests : List (Desc.First.Look.Guest Desc.First.S Cl))
    (b : Desc.Block Desc.First.S Cl)
    (hyes : ∀ s rs cols s', b.decide s rs cols = .ok s' →
      (Desc.K3.block (Desc.K3.seatCalls claim) piece laid before
        (Desc.First.Look.P.ofPlace set false x) guests).decide s rs cols = .ok s')
    (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT)) (hb : p.b = below b)
    (hback : p.back = []) (hext : ∀ a τ w, p.ext a τ w = w) (H : HeadOK set x floor)
    (hp : (Forest.planeCols x.fs x.lm).toBool = true)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err)
    (hsmp : ∀ s rs cols s', b.decide s rs cols = .ok s' → smp s' = smp s)
    (hsmpW : ∀ s rs cols s', b.decide s rs cols = .ok s' → smpW s' = smpW s)
    (hTok : ∀ s rs cols s', b.decide s rs cols = .ok s' → tokOf s' = tokOf s)
    (hstrW : ∀ y (τ : Tr (uLT (ckP .two) p.ds)),
      strW (behind (ckP .two) Fr p.base p.ds y τ) = strW y)
    (hseat : ∀ i, (seatT i).1 < p.base) (σ₀ : (attSg x D rad).Smp) (σW₀ : oW.Smp) :
    p.GoodIn
      (LayOn G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork (OwnIs D x.link))
      (LayOn' G x D rad oW seatT smp smpW strW (Desc.K3.seatCalls claim).fork
        (Desc.K3.seatCalls claim).heard (OwnIs D x.link))
      (HeadFront G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW tokOf)
      (HeadBehind G adr x tl D rad oW wOf nr nc seatT arr smp smpW strW msgW tokOf
        (Desc.K3.seatCalls claim).fork (Desc.K3.seatCalls claim).heard) :=
  k3_goodIn_calls (r := theR) (mk := lyMask x.ns tl nr nc)
    (pl := lyCell x.ns tl nr nc adr.iB) (st := fun a => tokOf a.1) (y₀ := ())
    (sm := laySm x D rad oW smp smpW σ₀ σW₀) (wd := layWd G x D rad oW seatT strW)
    (wt := layWt x D rad oW seatT arr msgW)
    (Cond := LayCond G x D rad oW seatT smp smpW strW (OwnIs D x.link))
    (Pin := LayPin G x D rad oW seatT arr smp smpW strW msgW)
    (Says := fun a w => HeadSays adr x tl D rad oW wOf nr nc (tokOf a.1)
      (layMs x D rad oW seatT arr msgW w))
    claim piece laid before guests b hyes p hb hback hext (head_sel H) H.shape
    (by
      show 1 < x.fs.NC
      rw [H.six]
      decide)
    hp (fun _ => rfl) (fun _ _ _ _ => rfl) hr hR hε
    (fun s _ _ rs cols s' hd => hTok s rs cols s' hd)
    (fun a h => ⟨layCond_cf G seatT smp smpW strW (OwnIs D x.link) σ₀ σW₀ a h, trivial⟩)
    (fun s y τ rs cols s' hd h =>
      layCond_stays G seatT smp smpW strW (OwnIs D x.link) p.base p.ds hseat s s' y τ
        (hsmp s rs cols s' hd) (hsmpW s rs cols s' hd) (hstrW y τ)
        (ownIs_calls claim piece laid before _ guests D x.link s s' rs cols
          (hyes s rs cols s' hd)) h)
    (fun s y τ rs cols s' w hd h =>
      layPin_back G seatT arr smp smpW strW msgW p.base p.ds hseat s s' y τ
        (hsmp s rs cols s' hd) (hsmpW s rs cols s' hd) (hstrW y τ) w h)
    (fun a w h i => layPin_decs G seatT arr smp smpW strW msgW σ₀ σW₀ a w h i)
    (fun _ _ ho ht => ⟨⟨trivial, ho⟩, ht⟩)
    (fun a w h => head_says extNone Unit (tokOf a.1, ())
      (layMs x D rad oW seatT arr msgW w, ()) h)

/-- **The end theorem's errors, as a number.** -/
theorem k3_head_err (p : Piece (ckP .two) Fr Desc.First.S Cl (Desc.Wit Cells Tok MsgT))
    (H : HeadOK set x floor)
    (hr : (Desc.First.Look.P.ofPlace set false x).entries.isSome = true)
    (hR : List.Forall₂ SameAs p.ds (Desc.First.Look.P.ofPlace set false x).rounds)
    (hε : bearT p.ds _ ((kLookupCRN [theR]).ε theR) = some p.err) :
    Iop.Err.Below p.err ((2 : ENNReal)⁻¹ ^ 157) :=
  k3_calls_err (r := theR) p H.shape
    (by
      show 1 < x.fs.NC
      rw [H.six]
      decide)
    hr hR hε

end

end VerifiableInference.OnPublicFiles

#print axioms VerifiableInference.OnPublicFiles.head_sel
#print axioms VerifiableInference.OnPublicFiles.k3_head_goodIn_any
#print axioms VerifiableInference.OnPublicFiles.k3_head_err
