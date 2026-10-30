-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseSevenKFirst.lean: Johnson/Road/K4/CloseSevenFirst.lean's
`Plan4LF.eight_of_yes` WITH NINE OF ITS PREMISES CONCLUDED: the six facts on what was heard
(`Plan4LF.heard_KF`, CloseKitFirst.lean) and the three ties of the masks (`masks_KF`,
MasksKFirst.lean). The twin of Johnson/Road/K4/CloseSevenK.lean. One theorem. Glue: no new argument,
no count.

  `Plan4LF.eight_at`: `Plan4LF.EightAt` (the parts sq bat led terms gated hot stack emb of
    `Plan4F.clKF` at `Plan4F.yKF`) at a yes, under what the row opens.

The choices of the value's letters at a place are asked by the later groups' own record
`Plan4L.ValueIs` (CloseSevenK.lean), at the letters that the first group's value shares with a later
group's (QF.toPlan4L): that record names no group, and its field nI counts one weight claim fewer
where the place's group is the first.

Limits. K04_law IS NOT PROVED BY THIS. The part merge is not spoken of. PREMISES THAT STAY: the
seat's two laws at the record in front · the ledger in front has arrays of the right sizes, and its
next free slot is the value's n0 · `ValueIs` · `PubLines`, `LookLines`, the rotary tables' fit ·
zOf, kTg at the first statement; the lookup's end form names filled slots alone · OF THE WORLD: the
statement's mask row is the value's at part w; matrices Mt whose reads are true in the worlds of the
two ledgers behind the runs, and whose cells are the message's · THE FIVE OWN ROWS u1 u2 u5 u6 u4 ·
uE: THE LIBRARY's CLAIM ON THE STREAM THAT COMES IN IS WORTH 0 AT `yKF`: NOT PAID HERE.
`Plan4F.MeetsF` and pc.ds = dsFirst par. Nothing shows that these can be met together.
-/
import Johnson.Road.K4.CloseSevenFirst
import Johnson.Road.K4.CloseSevenK
import Johnson.Road.K4.MasksKFirst
import Johnson.Road.K4.CloseKitFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QF : Plan4LF Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The eight parts at a yes in the first group, under what the row opens** and the premises that
the head lists, the five own rows and the embedding's claim among them. -/
theorem Plan4LF.eight_at (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt}
    (hds : pc.ds = dsFirst par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (a : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (w : Wt)
    (hB : Behind L Sm Lt par (behindOf L pc a τ o G) w) (hL : SeatOk L a.1)
    (hF : PscRun.Sized (L.fork a.1)) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QF.planF.fullF.D
      QF.planF.fullF.tb s lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QF.planF.fullF.D QF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (lw : ℕ → LW Cb.Gl.E) (hz0 : QF.planF.fullF.zOf (fa a).1 = zAt fo)
    (hk0 : QF.planF.fullF.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QF.planF.fullF.D
        QF.planF.fullF.tb hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QF.planF.fullF.D (cellsAt par.P.y Mt) =
      QF.planF.fullF.rd (QF.planF.fullF.msg (part w)))
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (h0 : QF.n0 = (L.fork a.1).next)
    (hSm : Sm.mask w = QF.planF.maskAt (part w))
    (u1 : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (u1At QF.planF.fullF.ofp.nr
        ((tailW QF.planF.fullF).b1 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).2) = 0)
    (u2 : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (u2At QF.planF.fullF.ofp.nr
        ((tailW QF.planF.fullF).b2 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).2) = 0)
    (u5 : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (prodU QF.planF.fullF.fp.gp
        ((tailW QF.planF.fullF).b5 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).2) = 0)
    (u6 : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (prodU QF.planF.fullF.fp.rt.L
        ((tailW QF.planF.fullF).b6 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).2) = 0)
    (u4 : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (upForm (J₂ := J4 (roomKF QF.planF par hS))
        (Cb.Sub.formU QF.planF.fullF.ip.inn.toSum.T.par (fun _ b _ _ => PEmpty.elim b)
          ((tailW QF.planF.fullF).b4
            (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).2)) = 0)
    (uE : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (embClaim (lateF (roomKF QF.planF par hS)) Sum.inr
        (((tailW QF.planF.fullF).y7 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).1.2
          (0 : Fin 1))
        QF.planF.fullF.mkE QF.planF.fullF.nb QF.planF.fullF.gB
        (stF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).pb) = 0) :
    Plan4LF.EightAt A Ex hds fa part a τ w := by
  obtain ⟨hinv, hscl, hvy, hL0, Nw, hsB⟩ :=
    Plan4LF.heard_KF A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5', Ld⟩ := own_ledG hF Y.hears
  obtain ⟨Mk, mA, mB⟩ := masks_KF QF (P := { par.P with tokv := L.tokv a.1 }) A.hy A.hrd A.Z A.hl
    A.hn hF Y.hears A.hg Ld h0 V.nT V.nI V.numT V.hEnd V.room V.iA V.iB (A.lamM (L.tokv a.1))
    (part w)
    (lateAtF QF.planF.fullF (lateF (roomKF QF.planF par hS))
      (fmOfF QF.planF.fullF (ztSF QF.planF.fullF) (par.P.y.lPd - par.P.y.ls) par.P.y.ls
        par.P.y.ls)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
    (readsAt (lateF (roomKF QF.planF par hS)) fun x => Sum.inl (Sum.inl x))
    (readsT (lateF (roomKF QF.planF par hS)) fun x => Sum.inl (Sum.inr (Sum.inl x)))
    (gReadsAt (lateF (roomKF QF.planF par hS)) fun x => Sum.inl (Sum.inr (Sum.inr x)))
  rw [← hSm] at Mk mA mB
  exact Plan4LF.eight_of_yes A L Sm Lt Ex hds fa part a τ Y w hB hL hF B K Rp hinv hscl hvy hL0 Nw
    hsB lw hz0 hk0 hfil Mt hR hcells Mk mA mB u1 u2 u5 u6 u4 uE

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.eight_at
