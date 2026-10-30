-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K15/HsemAtV.lean: WHAT IS PROVED OF THE LINK's DECISION (Johnson/Desc/K15/HsemAt.lean)
HOLDS OF THE SEATED TEXT's (the kind K1's own block at the sending:
Johnson/Desc/Link/LinkDesc.lean): the six statements of that file,
TO THE LETTER BUT FOR THE DECISION's NAME (linkDescriptionAt for descOf), each from its elder by the tie
(Johnson/Desc/K15/SendOwnLaw.lean: descV_run), UNDER THE TIE's ONE NAMED PREMISE SendPOfDecide (a
proposition on another kind's block; it is paid over that kind's files' own theorem
(sendP_of_decide, Johnson/Desc/K1/Law/SendP3.lean) in Johnson/Desc/K15/SendOwnPaid.lean),
and by this: the written protocol's yes is monotone in its decision (accept_mono).
The statements are made by program out of HsemAt.lean's text. All that HsemAt.lean's head does not
claim is not claimed here either.
-/
import Johnson.Desc.K15.HsemAt
import Johnson.Desc.K15.SendOwnLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Desc.K15
open H2K.Sw H2K.JointK
open OnBytes OnBytes.Params OnBytes.Slice Desc.Plain
open Iop Prob Cb Cb.Ood _root_.Run Blocks
open OnBytes.Params (recordRead smallRecordRead)
open VerifiableInference.Desc VerifiableInference.Desc.K12

/-- The written protocol's yes is monotone in its decision on the view. -/
theorem accept_mono (ds : List PQ.RD) (a : ℕ) (xs : List PQ.XO) (dec dec' : PQ.View → Bool)
    (hdd : ∀ V, dec V = true → dec' V = true)
    (y : (twoExternalStrings (2 ^ a) PQ.SgX).Str) (τ : Tr (PQ.uL (ckP .two) ds))
    (m0 : (PQ.s0 (ckP .two)).up.Msg) (c0 : (PQ.s0 (ckP .two)).up.Chal)
    (h : (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs dec).up.loc.accept () y (m0, c0, τ) = true) :
    (PQ.skeletonOverBothExternalStrings (ckP .two) ds a xs dec').up.loc.accept () y (m0, c0, τ) = true := by
  have h4 : (PQ.passSL (ckP .two) ds _ && _ && _ && dec (PQ.viewX (ckP .two) ds a xs y τ)) = true :=
      h
  show (PQ.passSL (ckP .two) ds _ && _ && _ && dec' (PQ.viewX (ckP .two) ds a xs y τ)) = true
  simp only [Bool.and_eq_true] at h4 ⊢
  exact ⟨h4.1, hdd _ h4.2⟩

/-! ## The full size -/

theorem fr_yes_descV (hSP : SendPOfDecide) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey)
    (xs : List PQ.XO) (r : (frS.lkR frZ).X0) (hs : P.set.samples = 1) (hS : P.S = recordRead.link)
    (hC : P.codes = recordRead.codes) (hpub : PubAt P frC recordRead.codes) (hopen : OpensAt P frC)
    (hK0 : first.fits recordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1)
    (hK1 : further.fits recordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2)
    (y : (frS.lkR frZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : frC.Bl)
    (hacc : (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        (fun V => (linkDescriptionAt P plan ok).run (first, further) V)).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, frC.trL b) = true) :
    frC.Acc (sumStmR frN 97
        (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
            c5).1).1
        (frRows (st4R frS frZ r (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) y c1 m2 c2 m3 c4
            c5).1).2
        (drawnE (frRd 5) cA))
      (frW m2.1) (frF m2.1) (frW m2.1) b :=
  fr_yes_desc P plan ok first further xs r hs hS hC hpub hopen hK0 hK1 y m0 c0 m1 c1 m2 c2 m3 c3 m4
      c4 m5 c5 mA cA b
    (accept_mono _ _ xs _ _ (fun V hV =>
      descV_run hSP P plan ok (first, further) V hV) y _ m0 c0 hacc)

theorem fr_link_sound_descV (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (P : P15)
    (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey) (xs : List PQ.XO) (r : (frS.lkR frZ).X0) (hs : P.set.samples = 1)
    (hS : P.S = recordRead.link) (hC : P.codes = recordRead.codes)
        (hpub : PubAt P frC recordRead.codes)
    (hopen : OpensAt P frC)
    (hK0 : first.fits recordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side false 1).index first r.1)
    (hK1 : further.fits recordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR frS.P.v 29 1 (recordRead.link.side true 1).index further r.2) :
    (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) xs
        (fun V => (linkDescriptionAt P plan ok).run (first, further) V)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 r y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fr_link_joh hA xs _ r fun y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc =>
    fr_yes_descV hSP P plan ok first further xs r hs hS hC hpub hopen hK0 hK1 y m0 c0 m1 c1 m2 c2 m3
        c3 m4 c4 m5 c5 mA
      cA b hacc

/-! ## The small example -/

theorem sr_yes_descV (hSP : SendPOfDecide) (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey)
    (xs : List PQ.XO) (r : (srS.lkR srZ).X0) (hs : P.set.samples = 1)
        (hS : P.S = smallRecordRead.link)
    (hC : P.codes = smallRecordRead.codes) (hpub : PubAt P srC smallRecordRead.codes)
        (hopen : OpensAt P srC)
    (hK0 : first.fits smallRecordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1)
    (hK1 : further.fits smallRecordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2)
    (y : (srS.lkR srZ).E0.Str) m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA (b : srC.Bl)
    (hacc : (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        (fun V => (linkDescriptionAt P plan ok).run (first, further) V)).accept () y
      (m0, c0, m1, c1, m2, c2, m3, c3, m4, c4, m5, c5, mA, cA, srC.trL b) = true) :
    srC.Acc (sumStmR srN 97
        (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
            c5).1).1
        (srRows (st4R srS srZ r (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) y c1 m2 c2 m3 c4
            c5).1).2
        (drawnE (srRd 5) cA))
      (srW m2.1) (srF m2.1) (srW m2.1) b :=
  sr_yes_desc P plan ok first further xs r hs hS hC hpub hopen hK0 hK1 y m0 c0 m1 c1 m2 c2 m3 c3 m4
      c4 m5 c5 mA cA b
    (accept_mono _ _ xs _ _ (fun V hV =>
      descV_run hSP P plan ok (first, further) V hV) y _ m0 c0 hacc)

theorem sr_link_sound_descV (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (P : P15)
    (plan : List Fmt.DeclaredRound) (ok : Bool)
    (first further : TableKey) (xs : List PQ.XO) (r : (srS.lkR srZ).X0) (hs : P.set.samples = 1)
    (hS : P.S = smallRecordRead.link) (hC : P.codes = smallRecordRead.codes)
        (hpub : PubAt P srC smallRecordRead.codes)
    (hopen : OpensAt P srC)
    (hK0 : first.fits smallRecordRead.link.table = true → (first.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side false 1).index first r.1)
    (hK1 : further.fits smallRecordRead.link.table = true → (further.seeds.all fun x =>
      !isZeroE x.beta) = true →
      KeyHasR srS.P.v 19 1 (smallRecordRead.link.side true 1).index further r.2) :
    (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) xs
        (fun V => (linkDescriptionAt P plan ok).run (first, further) V)).Sound
      (fun _ y => srS.LangE2T srZ 524285 r y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  sr_link_joh hA xs _ r fun y m0 c0 m1 c1 m2 c2 m3 c3 m4 c4 m5 c5 mA cA b hacc =>
    sr_yes_descV hSP P plan ok first further xs r hs hS hC hpub hopen hK0 hK1 y m0 c0 m1 c1 m2 c2 m3
        c3 m4 c4 m5 c5 mA
      cA b hacc

/-! ## Another file's premise H, to the letter, at the seated decision -/

section
open OnBytes.Flat TypedOracleCompiler.Slice OnBytes.Tie

def decDescFullV (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (x : XE AnsT 29 1) : PQ.View →
    Bool :=
  fun V => (linkDescriptionAt P plan ok).run (keysOfX frS.P.v 29 1 (anT frS.P.v 1) x) V

def decDescSmallV (P : P15) (plan : List Fmt.DeclaredRound) (ok : Bool) (x : XE AnsT 19 1) : PQ.View →
    Bool :=
  fun V => (linkDescriptionAt P plan ok).run (keysOfX srS.P.v 19 1 (anT srS.P.v 1) x) V

set_option maxRecDepth 100000 in
theorem H_fullV (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (P : P15) (plan : List Fmt.DeclaredRound)
    (ok : Bool)
    (hs : P.set.samples = 1) (hS : P.S = recordRead.link) (hC : P.codes = recordRead.codes)
    (hpub : PubAt P frC recordRead.codes) (hopen : OpensAt P frC) :
    ∀ x, (written frS (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frRd 5 :: frC.rds) frD.xs
        (decDescFullV P plan ok x)).Sound
      (fun _ y => frS.LangE2T frZ 402653181 (recOf frS 29 1 (anT frS.P.v 1) x) y)
      (0, coreErrR frS frZ (frRd 0) (frRd 1) (frRd 2) (frRd 3) (frRd 4) (frS.badJ frS.e0)
        (frS.badJ frS.e1)
        (fun _ => Cb.listMax (2 ^ frS.P.C.a) (2 ^ frS.P.C.a - (frS.P.C.r + frS.P.C.l) + 1) frS.eU)
        (batErrR frN ((frS.sg 97).lstJ frC.rad) (frRd 5), frC.errL)) :=
  fun x =>
    fr_link_sound_descV hSP hA P plan ok _ _ frD.xs (recOf frS 29 1 (anT frS.P.v 1) x) hs hS hC hpub
        hopen
    (fun _ _ => keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).1 _ rfl rfl Shapes.zFull_lg 0)
    (fun _ _ => keyHasR_keyOf (recOf frS 29 1 (anT frS.P.v 1) x).2 _ rfl rfl Shapes.zFull_lg 1)

set_option maxRecDepth 100000 in
theorem H_smallV (hSP : SendPOfDecide) (hA : BCHKS46At GF GE) (P : P15) (plan : List Fmt.DeclaredRound)
    (ok : Bool)
    (hs : P.set.samples = 1) (hS : P.S = smallRecordRead.link)
        (hC : P.codes = smallRecordRead.codes)
    (hpub : PubAt P srC smallRecordRead.codes) (hopen : OpensAt P srC) :
    ∀ x, (written srS (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srRd 5 :: srC.rds) srD.xs
        (decDescSmallV P plan ok x)).Sound
      (fun _ y => srS.LangE2T srZ 524285 (recOf srS 19 1 (anT srS.P.v 1) x) y)
      (0, coreErrR srS srZ (srRd 0) (srRd 1) (srRd 2) (srRd 3) (srRd 4) (srS.badJ srS.e0)
        (srS.badJ srS.e1)
        (fun _ => Cb.listMax (2 ^ srS.P.C.a) (2 ^ srS.P.C.a - (srS.P.C.r + srS.P.C.l) + 1) srS.eU)
        (batErrR srN ((srS.sg 97).lstJ srC.rad) (srRd 5), srC.errL)) :=
  fun x =>
    sr_link_sound_descV hSP hA P plan ok _ _ srD.xs (recOf srS 19 1 (anT srS.P.v 1) x) hs hS hC hpub
        hopen
    (fun _ _ => keyHasR_keyOf (recOf srS 19 1 (anT srS.P.v 1) x).1 _ rfl rfl Shapes.zSmall_lg 0)
    (fun _ _ => keyHasR_keyOf (recOf srS 19 1 (anT srS.P.v 1) x).2 _ rfl rfl Shapes.zSmall_lg 1)

end

end Desc.K15

#print axioms Desc.K15.accept_mono
#print axioms Desc.K15.H_fullV
#print axioms Desc.K15.H_smallV
#print axioms Desc.K15.fr_yes_descV
#print axioms Desc.K15.fr_link_sound_descV
#print axioms Desc.K15.sr_yes_descV
#print axioms Desc.K15.sr_link_sound_descV
