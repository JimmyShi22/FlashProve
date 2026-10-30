-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/RunOne/KeyRowsAtPlan.lean: THE KEY FILE, ROWS 2.7 · 2.4 · 2.1: THE PREMISE h ("the kind's
blocks can be said, and are these eight") STRUCK: under the
description's own tests on the plan it is a theorem: the key file's owner's blocks_of_planOk
(Johnson/RunOne/Sound/KeyEightLight.lean) with eight_of_blocks
(Johnson/RunOne/KeyK14Sits.lean). No letter b1 … b8 is left in the statements.

  r2_7_plan | r2_4_plan | r2_1_plan : r2_k_frame's conclusion (Johnson/RunOne/KeyRowsAtFrame.lean)
  from hpl : (Key.descriptionFromSource X N P).planOk = true in the place of h

LEFT     the scope's four · hpl · hD · q₂ · hbk · hcut · hbase · CellOnly coll · hsame · hcap ·
(2.4: henc · hm) · (2.1: hst · hK · hof · henc · two comparisons ·
         CollTie · DecTie)
What is not claimed. IT FIXES THE RELEASE's ONE CONFIGURATION (VerifierAndGoals.InScope). NO MEMBER SHOWN
of on₂ … k: the laws may be true and empty at the real
protocol. No soundness of a verifier.

-/
import Johnson.RunOne.KeyRowsAtFrame
import Johnson.RunOne.Sound.KeyEightLight

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Johnson.RunOne.KeyRows23
open OnBytes OnBytes.Params OnBytes.Maker OnBytes.Flat
open OnBytes.Model.Verify (Public)
open Johnson.G.OfPlan (Made)
open _root_.Run (ckP)
open _root_.Iop (Reduction Err)
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Plain
    VerifiableInference.Desc.Sound
open VerifiableInference.Desc.K13.Law (ρg)
open Johnson.RunOne.KeyRows1 (plan₁)
open Johnson.RunOne.Law.AtFreeCfg (ReadOf)
open scoped ENNReal

section
variable {XI Cells M Smp Rec W : Type} (F : FileDescription XI) (Fr₂ : Frame) (T : BaseSt Cells M Smp Rec)
    (at_ : Where)
  (K₁ : KPlan) (R : KRead Cells M) (enc : (Nat → E) → Nat → E) (rad a : Nat)
  (coll : Strs → Rec → Prop) (last₁ : FirstState → Bool) (off₂ : Nat → Nat)
  (X : Source) (N : H2U.PlaceNums) (P : LaterPlaces) (hpl : (descriptionFromSource X N P).planOk = true)
include hpl

theorem r2_7_plan (file : String) (D : WholeD) (hD : (descriptionFromSource X N P).data file = .ok D) (c₂ : Block St₂
                     Claim) (k₂ : List (Block St₂ Claim))
    (q₂ : (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf Zp.pol Z) {cfg :
                ByteArray} {m : Made}
    (hmd : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (b : Block St₂ Claim) (hbk : (descriptionFromSource X N P).shared.blocksInOrder[7]? = some b)
    (d : RDT) (hcut : LPFD.cutDs D.ds₂ c₂ k₂ 7 = [d]) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 7), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ OnBytes.Model.Reading.gl.val x = OnBytes.Model.Reading.gl.val y)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad a coll last₁ off₂ 7) (on₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc rad a coll last₁ off₂ (7 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc rad 7) (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc
            rad (7 + 1)) x.err ∧
      Err.le x.err x'.err := by
  obtain ⟨l, hl⟩ := Johnson.RunOne.Sound.Light.blocks_of_planOk X N P hpl
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight_of_blocks _ l hl
  exact r2_7_frame F Fr₂ T at_ K₁ R enc rad a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 hl file
      D hD c₂ k₂ q₂ hZ hRd hmd hX b hbk d hcut base hbase hcC
    hsame x' hcap

theorem r2_4_plan (file : String) (D : WholeD) (hD : (descriptionFromSource X N P).data file = .ok D) (c₂ : Block St₂
                     Claim) (k₂ : List (Block St₂ Claim))
    (q₂ : (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf Zp.pol Z) {cfg :
                ByteArray} {m : Made}
    (hmd : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    {K : Type} [Field K] (ρ : Model.Reading K) (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[4]? = some b)
    (d : RDT) (hcut : LPFD.cutDs D.ds₂ c₂ k₂ 4 = [d]) (dep : Nat → Option Nat)
    (hm : Matches Fr₂.a dep b.rounds [d]) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 4), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρ.val x = ρ.val y) (henc : EncIs ρ (p14At X P).par.S.fold enc)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂ 4)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius a coll last₁ off₂
            (4 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S K₁ R enc OnBytes.Params.recordRadius 4) (L₂ F Fr₂ T.h₂ at_
            (p14At X P).S K₁ R enc OnBytes.Params.recordRadius (4 + 1)) x.err ∧
      Err.le x.err x'.err := by
  obtain ⟨l, hl⟩ := Johnson.RunOne.Sound.Light.blocks_of_planOk X N P hpl
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight_of_blocks _ l hl
  exact r2_4_frame F Fr₂ T at_ K₁ R enc a coll last₁ off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 hl file D hD
      c₂ k₂ q₂ hZ hRd hmd hX ρ b hbk d hcut dep hm base hbase
    hcC hsame henc x' hcap

theorem r2_1_plan (file : String) (D : WholeD) (hD : (descriptionFromSource X N P).data file = .ok D) (c₂ : Block St₂
                     Claim) (k₂ : List (Block St₂ Claim))
    (q₂ : (descriptionFromSource X N P).shared.blocksInOrder = c₂ :: k₂)
    {Zp : VerifierAndGoals.PublicFiles} (hZ : VerifierAndGoals.InScope Zp = true) {Z : Public} (hRd : ReadOf Zp.pol Z) {cfg :
                ByteArray} {m : Made}
    (hmd : madeAt Z Zp.lay cfg = .ok m) (hX : sourceOf m = .ok X)
    (one : OneTime) (hst : 1 ≤ one.ranges.stages.length) (hK : one.lin = (p14At X P).par.S)
    (err eM : Nat) (rank : ((Fin (p14At X P).par.S.fold.index.v → Bool) → Fin ((p14At X
        P).par.S.fold.index.code.r + (p14At X P).par.S.fold.index.code.ell) → Cb.Gl.E) → Nat)
    (b : Block St₂ Claim)
    (hbk : (descriptionFromSource X N P).shared.blocksInOrder[1]? = some b)
    (d : RDT) (hcut : LPFD.cutDs D.ds₂ c₂ k₂ 1 = [d]) (base : Nat)
    (hbase : ∀ j ∈ pinned (open₂ 1), (at_ j).1 < base) (hcC : CellOnly coll)
    (hsame : ∀ x y, R.same x y ↔ ρg.val x = ρg.val y)
    (hof : ∀ (w : Wit Cells Unit M) c k, R.of { w with cells := c } k = R.of w k)
    (henc : EncIs ρg (p14At X P).par.S.fold enc)
    (hle : 2852142980 ≤ eM) (hM : eM < 3848273922)
    (hcoll : CollTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At
        one) off₂ err eM rank)
    (hdec : DecTie F Fr₂ T.h₂ at_ (p14At X P).par (plan₁ one) R enc 2852142980 a coll (last₁At one)
        off₂ err eM rank)
    (x' : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d]) (hcap : x'.err = Err.cap 128 (uLT (ckP .two) [d])) :
    ∃ x : Rest (ckP .two) Fr₂ (P₂ × St₂) W [d],
      (pieceOf (held b) base [d] [] x).ior.red.Keeps
        (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂ 1)
            (on₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 a coll (last₁At one) off₂
            (1 + 1))
        (L₂ F Fr₂ T.h₂ at_ (p14At X P).S (plan₁ one) R enc 2852142980 1) (L₂ F Fr₂ T.h₂ at_ (p14At X
            P).S (plan₁ one) R enc 2852142980 (1 + 1)) x.err ∧
      Err.le x.err x'.err := by
  obtain ⟨l, hl⟩ := Johnson.RunOne.Sound.Light.blocks_of_planOk X N P hpl
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, rfl⟩ := eight_of_blocks _ l hl
  exact r2_1_frame F Fr₂ T at_ R enc a coll off₂ X N P b1 b2 b3 b4 b5 b6 b7 b8 hl file D hD c₂ k₂ q₂
      hZ hRd hmd hX one hst hK err eM rank b hbk d hcut base
    hbase hcC hsame hof henc hle hM hcoll hdec x' hcap

end

end Johnson.RunOne.KeyRows23
