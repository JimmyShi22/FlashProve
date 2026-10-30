-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Desc/Sound/HrowsNineG.lean: **hrows_nine (HrowsNine.lean) WITH TWO OF ITS PREMISES PAID**: hG ("the statement behind the test has grown out of the one in front") by k12_grows through the seat's doors (GrowsThrough.lean) · hIn ("the
statement in front is in order") from a promise that holds "tidy" at the border 9. Statements; each proof is calls of what lies.
  grows_nine       hG, to the letter, at a piece whose block is alike to the held test on G_u: NO PREMISE MORE.
  tidy_nine        at such a piece: Codes.lengthsOk and Tidy at the record in front give Tidy at the record behind (TidyThrough.lean): the hand-on of "tidy" from the border 9 to the border 10, at the piece.
  **hrows_nine_G** hrows_nine without hG.
Limits: those of HrowsNine.lean. It closes no row. NO SOUNDNESS.

-/
import Johnson.Desc.Sound.HrowsNine
import Johnson.Desc.K12.Coin.GrowsThrough
import Johnson.Desc.K12.Coin.TidyThrough

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Desc.K14.Law.Fence
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Maker Desc.Plain Johnson.Pack Cb
open Iop Prob _root_.Run
open OnBytes.Means (Words InOrder Tidy)
open VerifiableInference.Desc (Block FileDescription Strs Wit Grows)
open VerifiableInference.Desc.K12 (P12 T12 proximityTestKind guardedProximityTestParts Seat.onGu)
open VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Shared
open _root_.Desc.K14.Law (mgI rgOf SampleRides)

section
variable {P₁ Cl W : Type} {Fr : Frame} (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl W)
  (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)

include hb in
/-- **hG, at the piece.** -/
theorem grows_nine (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (hout : x.ior.red.out a τ = some b) : Grows a.1.2.st b.1.2.st := by
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  exact onGu_grows π _ _ rs gs hd

include hb in
/-- **"Tidy" from the border 9 to the border 10, at the piece.** -/
theorem tidy_nine (a b : (P₁ × St) × Fr.E.Str) (τ : Iop.Tr (uLT (ckP .two) x.ds))
    (hout : x.ior.red.out a τ = some b) (hl : a.1.2.st.codes.lengthsOk = true)
    (hT : Tidy a.1.2.st) : Tidy b.1.2.st ∧ b.1.2.st.codes.lengthsOk = true := by
  obtain ⟨rs, gs, hd, _⟩ := held_decides _ x hb a b τ hout
  refine ⟨onGu_tidy π _ _ rs gs hd hl hT, ?_⟩
  rw [(onGu_grows π _ _ rs gs hd).1]
  exact hl

end

section
variable (cs : Codes) {Xi P₁ Cl Cells Tok : Type} (G : FileDescription Xi) (arr : ℕ → ℕ → ℕ) (ms : List Mem)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → St → Option Cells) (c₀ : Cells) (N : NumbersS)
  (Mg₀ : MeaningS St P₁ (Wit Cells Tok MsgT)) (Pm₀ : PromMeaning St) (Oc : P₁ → Strs → Prop)
  {Fr : Frame} (oNo : Mem → ℕ) (P : P14) (sentU : Array OracleNotice) (layU layO : TreeLay)
  (f : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))
  (l : List (Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT)))
  (mem : ℕ → Option Mem) (rd : (x : Mem) → ((sigOf cs x.1.l).om x.2).Msg → Part → ℕ → GE)
  (Q : Par) (uR : St → St) (omW : Wit Cells Tok MsgT → ℕ → GE) (e' n : ℕ) (num : Msg2 → ℕ)
  (π : P12) (x : Piece (ckP .two) Fr (P₁ × St) Cl (Wit Cells Tok MsgT))

/-- **nine_paid's hrows AT mgI, WITHOUT hG.** -/
theorem hrows_nine_G
    (hb : Alike (held (P := P₁) (Seat.onGu (proximityTestKind guardedProximityTestParts π : Block T12 Unit))) x.b)
    (he : π.early = true) (ha1 : π.answers = 1) (hsU : sentU.size = 2)
    (hsO : (withOmega P.S).size = 2)
    (hIn : ∀ a, onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      InOrder a.1.2.st)
    (xO xS : Mem) (hmO : mem sentU.size = some xO) (hmS : mem (sentU.size + 1) = some xS)
    (sO : SitsAt xO (N.tenant .oOmega).1 (N.tenant .oOmega).2)
    (sS : SitsAt xS (N.tenant .oSp).1 (N.tenant .oSp).2)
    (hapO : apartAt N arr true 9 (.msg .oOmega) = true)
    (hapS : apartAt N arr true 9 (.msg .oSp) = true)
    (hsr : SampleRides Mg₀ num) (hso : SampleOwn N arr Mg₀)
    (hnO : num .oOmega = sentU.size) (hnS : num .oSp = sentU.size + 1) :
    ∀ i ∈ [ItemS.row (.sample .oOmega), .row (.sample .oSp), .row .foldOmega], ∀ a τ b w,
      onQ₂ N (pmX cs G ms N Pm₀ oNo P sentU layU layO) Oc true f l 9 a →
      x.ior.red.out a τ = some b →
      muQ N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂
        (mgI cs arr Mg₀ mem rd Q uR omW e' n)) f l i 10 ((actQ N f l 10).2 b) w →
      muQ N (meaningSigS cs G arr (smpSt cs oNo stSh) ms decT₂
        (mgI cs arr Mg₀ mem rd Q uR omW e' n)) f l i 9 ((actQ N f l 9).2 a)
        (e₀H cs G arr (smpSt cs oNo stSh) ms decT₂ c₀ N true Fr 9 ((actQ N f l 9).2 a) w) :=
  hrows_nine cs G arr ms decT₂ c₀ N Mg₀ Pm₀ Oc oNo P sentU layU layO f l mem rd Q uR omW e' n num π x
    hb he ha1 hsU hsO hIn xO xS hmO hmS sO sS hapO hapS hsr hso
    (fun a τ b _ hout => grows_nine π x hb a b τ hout) hnO hnS

end

end Desc.K14.Law.Fence

#print axioms Desc.K14.Law.Fence.grows_nine
#print axioms Desc.K14.Law.Fence.tidy_nine
#print axioms Desc.K14.Law.Fence.hrows_nine_G
