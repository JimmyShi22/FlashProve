-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Goal/Meaning/SpentHears.lean: the field `back` of TieOwes
(Johnson/Goal/Meaning/SpentAtPlain.lean) FROM THE RECORD `FileDescription.Hears`
(Johnson/Desc/Sound/FoldHeard.lean): a description that hears the reply.

  `heardTok H t₀`: the token that is read off what the first chain hands on: what H's reading
    `heard` says of the first chain's last record; t₀ where it says none.
  `back_of_hears`: at a description with `F.Hears` at asked := the request's own reply: where the
    last test says yes at (x, rec) and s₁, that token, put into x without its reply, gives x. By the
    record's field `fins` and `putReq_glue` (Johnson/Flat/TiesAtReq.lean).
  `tieOwes_of_hears`: so TieOwes at `hidBy` with that token, from `Hears` and the field `on`.
  `tokOfE`, `tokOfE_replyOf`, `hearsTok`: WHERE WHAT IS HEARD IS AN ELEMENT OF THE EXTENSION FIELD,
    as in the first chain's record (`S.heard`; `fin_is_canonical`, Johnson/Flat/FinIsCanonical.lean,
    ends in "heard = some (replyOf x)"): the element's first word as a token; at `replyOf x` it is
    x's reply, if the vocabulary has at most 2^32 tokens; so `FileDescription.Hears.mapTok`
    (Johnson/Desc/Sound/FoldHeardProofs.lean) carries a record at asked := replyOf to one at the
    request's own reply.
So the way is: fin_is_canonical ⟶ `Hears.fins` at asked := replyOf ⟶ `hearsTok` ⟶ `back`. A
description over instances of its own comes to pairs (request, record) by
`FileDescription.Hears.pull`.
It spends of the record the reading and `fins` alone: `lays` and `leaves` (that what is heard is
what
the transcript names) are spent where the first chain's laws are shown, not here.
Nearest kin: tieBack_of_reads_fins (Johnson/Goal/Meaning/Row.lean): the same step on the road with
extractors, at the extractors' token. saidOfEnds (Johnson/Desc/Sound/FoldHeardProofs.lean) spends
`fins` toward the token that a view names.
Limits. The one member of `FileDescription.Hears` that is laid is a toy's. `fins` asks the heard token to
be
the reply at EVERY request, also where the reply does not count: more than `back` needs
(putReq_back_iff). Nothing is paid at a description of the protocol.
-/
import Johnson.Goal.Meaning.SpentAtPlain
import Johnson.Desc.Sound.FoldHeardProofs
import Johnson.Flat.FinIsCanonical

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace OnBytes.Flat
open Inst.Model OnBytes.Model OnBytes.Model.Verify

/-- An element's first word as a token; t₀ where that word is no token. -/
def tokOfE (t₀ : Fin ppref.V) (e : E) : Fin ppref.V :=
  if h : e.c0.toNat < ppref.V then ⟨e.c0.toNat, h⟩ else t₀

/-- **At a request's reply as an element it is the reply.** -/
theorem tokOfE_replyOf (hV : ppref.V ≤ 2 ^ 32) (t₀ : Fin ppref.V) (x : Instance ppref) :
    tokOfE t₀ (replyOf x) = x.y := by
  have hp : (2 : ℕ) ^ 32 < pW.toNat := by decide
  have e : (replyOf x).c0.toNat = x.y.val :=
    c0_ofNat (lt_trans (lt_of_lt_of_le x.y.isLt hV) hp)
  unfold tokOfE
  rw [dif_pos (by rw [e]; exact x.y.isLt)]
  exact Fin.ext e

end OnBytes.Flat

namespace VerifiableInference.OnPublicFiles
open OnBytes.Flat OnBytes.Slice OnBytes.Maker OnBytes.RunA
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ
open VerifiableInference.Desc VerifiableInference.Desc.Sound VerifiableInference.Desc.Plain

variable (N₀ : MatrixNums) (pp : Inst.Model.ScalesAndPolicy)
  (E : Coding (claimsReqAt (frS.toDecR frZ 402653181) N₀ pp)) (DP : WholeD)
  (F : FileDescription ((kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec)) (all : List LeftT)
  {rd : List Fmt.RoundView → Option (Fin Inst.Model.ppref.V)}
  (H : F.Hears (fun a : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec => dropReq a.1) rd)
  (t₀ : Fin Inst.Model.ppref.V)

/-- The token that is read off what the first chain hands on. -/
def heardTok : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → Fin Inst.Model.ppref.V :=
  fun b => (H.heard b.1.2).getD t₀

/-- **Where the last test says yes, the heard token put back gives the request.** -/
theorem back_of_hears (x : Flat.Req) (rec : (kcReq N₀ pp E).conf.Rec) (s₁ : F.S₁) (s₂ : F.S₂) (s₃ :
    F.S₃)
    (z : (EAll (DP.at frS.P.T.a) all).Str) (hf : F.fin (x, rec) s₁ s₂ s₃ = true) :
    putReq (reqWithoutReply x) (heardTok N₀ pp E DP F all H t₀ ((F.pub (x, rec), s₁), z)) =
      x := by
  have e : heardTok N₀ pp E DP F all H t₀ ((F.pub (x, rec), s₁), z) = dropReq x := by
    show (H.heard s₁).getD t₀ = dropReq x
    rw [H.fins (x, rec) s₁ s₂ s₃ hf]
    rfl
  rw [e]
  exact putReq_glue x

/-- **A record that hears the reply as an element, carried to the reply as a token.** -/
def hearsTok (hV : Inst.Model.ppref.V ≤ 2 ^ 32) {rdE : List Fmt.RoundView → Option OnBytes.E}
    (HE : F.Hears
      (fun a : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec => replyOf a.1.val) rdE) :
    F.Hears (fun a : (kcReq N₀ pp E).conf.X × (kcReq N₀ pp E).conf.Rec => dropReq a.1)
      fun rs => (rdE rs).bind fun e => some (tokOfE t₀ e) :=
  HE.mapTok (fun e => some (tokOfE t₀ e)) _ fun a => congrArg some (tokOfE_replyOf hV t₀ a.1.val)

variable {X₁ X₂ W : Type} (T : ThreeAt (ckP .two) (DP.at frS.P.T.a) all F X₁ X₂ W)
  (g : F.XiPub → F.S₁ → F.S₂ → F.S₃ → Bool)
  (Pl : PPlaces (DP.at frS.P.T.a) all (F.XiPub × F.S₁) ((F.XiPub × F.S₁) × F.S₂)
    ((F.XiPub × F.S₁ × F.S₂) × F.S₃))
  (X : OnBytes.Model.Verify.Public) (s : ℕ → Cb.Pv.Tail.Size)
  (seat : ∀ k, Fin (s k).NM → ℕ → ℕ → ℕ × ℕ × ℕ)
  (msgOf : (F.XiPub × F.S₁) × (EAll (DP.at frS.P.T.a) all).Str → ℕ → _root_.Meaning.Msgs)

/-- **TieOwes from a description that hears the reply, and the first border's condition.** -/
theorem tieOwes_of_hears
    (on : ∀ (x : Flat.Req) rec (y : (oneExternalString (2 ^ (DP.at frS.P.T.a).a) SgX).Str) M,
      F.okStart (x, rec) = true → (kcReq N₀ pp E).conf.D y rec = some M →
        Pl.on₁ 0 ((atDescFin F g T).in₁ (reqWithoutReply x, rec), (y, fun _ => []))) :
    TieOwes N₀ pp E DP F all T g Pl
      (hidBy N₀ pp E DP F all X s seat (heardTok N₀ pp E DP F all H t₀) msgOf) :=
  ⟨on, fun x rec s₁ s₂ s₃ z _ hf =>
    back_of_hears N₀ pp E DP F all H t₀ x rec s₁ s₂ s₃ z hf⟩

end VerifiableInference.OnPublicFiles

#print axioms OnBytes.Flat.tokOfE_replyOf
#print axioms VerifiableInference.OnPublicFiles.hearsTok
#print axioms VerifiableInference.OnPublicFiles.back_of_hears
#print axioms VerifiableInference.OnPublicFiles.tieOwes_of_hears
