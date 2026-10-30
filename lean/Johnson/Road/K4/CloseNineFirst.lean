-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseNineFirst.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST
GROUP, AND UNDER WHAT K4's ROW OPENS: ALL NINE PARTS sq bat led terms gated hot stack emb merge OF
THE LIBRARY's LEDGER (`Plan4F.clKF` at `Plan4F.yKF`, Johnson/Road/K4/CloseFirst.lean: nine of the
twelve fields of `Plan4F.PaysF`), THE FIVE OWN ROWS BEING PREMISES NO MORE. One theorem. Glue:
`Plan4LF.rows_atF` (CloseRowsFirst.lean) laid into `Plan4LF.eight_at` (CloseSevenKFirst.lean). No
new argument, no draw, no count. It has no model among the later groups' files of that name: there
the two are laid together inside Johnson/Road/K4/CloseK2.lean.

  `Plan4LF.nine_at`: `Plan4LF.EightAt` and the part merge, at a yes, under what the row opens.

Limits. K04_law IS NOT PROVED BY THIS. ONE PREMISE IS A CLAIM OF THE LEDGER ITSELF: uE: THE
LIBRARY's CLAIM ON THE STREAM THAT COMES IN (`embClaim`) IS WORTH 0 AT `yKF`: NOT PAID HERE: the
part emb is that claim's ledger, so of emb this file shows nothing. PREMISES THAT STAY BESIDE: those
of `rows_atF`: the seat's two laws · the ledger in front has arrays of the right sizes and its next
free slot is the value's n0 · `ValueIs`, `ValueMoreF` · `PubLines`, `LookLines`, the rotary tables'
fit · zOf, kTg, kIncS at the first statement; the lookup's end form: filled slots alone, no entry,
slots below ns + 1 · the statement's mask row is the value's at part w · matrices Mt whose reads are
true in the worlds of the ledgers behind the runs, and whose cells are the message's.
`Plan4F.MeetsF` and pc.ds = dsFirst par. Nothing on `PaysF`' fields kept, pending, first; nothing on
tok. Nothing shows that these can be met together.
-/
import Johnson.Road.K4.CloseRowsFirst

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

/-- **The nine parts at a yes in the first group, under what the row opens**, the premises that the
head lists, and uE: the embedding's claim is worth 0. -/
theorem Plan4LF.nine_at (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
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
    (hkS : ∀ s, QF.planF.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s)
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (he : fo.cEnd.ents = #[])
    (hsl : ∀ y ∈ fo.cEnd.slots.toList, y.1 < QF.ns + 1) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QF.planF.fullF.D
        QF.planF.fullF.tb hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QF.planF.fullF.D (cellsAt par.P.y Mt) =
      QF.planF.fullF.rd (QF.planF.fullF.msg (part w)))
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QF)
    (h0 : QF.n0 = (L.fork a.1).next) (hSm : Sm.mask w = QF.planF.maskAt (part w))
    (uE : Blocks.Form.val (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))
      (embClaim (lateF (roomKF QF.planF par hS)) Sum.inr
        (((tailW QF.planF.fullF).y7 (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).1.2
          (0 : Fin 1))
        QF.planF.fullF.mkE QF.planF.fullF.nb QF.planF.fullF.gB
        (stF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).pb) = 0) :
    Plan4LF.EightAt A Ex hds fa part a τ w ∧
      Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
          (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).merge
        (QF.planF.yKF par hS (ztSF QF.planF.fullF)
          (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) := by
  obtain ⟨u1, u2, u5, u6, u4, mg⟩ := Plan4LF.rows_atF A L Sm Lt Ex hds fa part a τ Y w hB hL hF B K
    Rp lw hz0 hk0 hkS hfil he hsl Mt hR hcells V V2 h0 hSm
  exact ⟨Plan4LF.eight_at A L Sm Lt Ex hds fa part a τ Y w hB hL hF B K Rp lw hz0 hk0 hfil Mt hR
    hcells V h0 hSm u1 u2 u5 u6 u4 uE, mg⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.nine_at
