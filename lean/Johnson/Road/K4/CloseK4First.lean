-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK4First.lean: Johnson/Road/K4/CloseK3First.lean's TOP WITH THE TWO FIELDS ON
TRUE READS CONCLUDED, where the statement's letter for the true value of an entry is filled by the
definition `entryTrue` at the value's own matrices (`ReadsAre`, Johnson/Road/K4/CloseReads.lean).
The twin of Johnson/Road/K4/CloseK4.lean. A record and two theorems. Glue: `reads_at`
(CloseReads.lean) and `Plan4LF.planes_atF` (CloseReadsFirst.lean) laid into `Plan4KF.Owes3F`. No
draw, no count.

  `Plan4KF.Owes4F`: WHAT IS STILL OWED: THREE FIELDS: kept (the promise behind holds at a yes) · wo
    (what the row opens on the committed weights gives the first group's pending row at the merge's
    record) · emb (THE LIBRARY's CLAIM ON THE STREAM THAT COMES IN IS WORTH 0).
  `Plan4KF.owes3F_of4`: `Owes3F` from `Owes4F`, `ValueIs`, `FrontIs`, the public lines, the rotary
    tables' fit and `ReadsAre`.
  `Plan4KF.k04LawAt_K4F`: `K04LawAt QK.L Sm Lt part par bk pc` at a piece whose errors are the cap.

Limits. K04_law IS NOT PROVED BY THIS. ALL THREE FIELDS OF `Owes4F`, EVERY LINE OF `ReadsAre`, OF
`FrontIs` AND OF `LettersAreF` ARE UNPAID HERE; so are `MeetsF`, `ValueIs`, `ValueMoreF`, pc.ds,
pc.back, that the errors are the cap, C, hk, the bound on Q3, the layout's line, the matrices'
zeros, the seat's two laws, the public lines and the rotary tables' fit. THE READS ARE TRUE BY MAKE
(EntryTrue.lean's limits): that the committed reads are these is another row's matter. Nothing shows
that all can be met together. The letters `Sem`, `Letters`, part, fe, Ex, nu, first, h3, Q3 and
those of `Plan4KF` are not filled in this file: CloseFillFirst.lean lays `Letters`
(`Plan4KF.lettersOfF`) and CloseFill.lean `Sem` and nu (`Plan4K.semOf`, `nuOf`) from the others,
which they do not fill. The first group alone. USER: `Plan4KF.k04LawAt_K5F` (CloseK5First.lean).

-/
import Johnson.Road.K4.CloseCapFirst
import Johnson.Road.K4.CloseReadsFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own matIx)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl Tg7 aS7)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind K04LawAt frontRun)
open VerifiableInference.OnPublicFiles (K4ReadsTrue K3LeftAt)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (LW Dim)

variable [scl : Scl] {Mm T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **What is still owed in the first group where the reads are true by make.** -/
structure Plan4KF.Owes4F (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
    Lt.on' (behindOf QK.L pc a τ o G)
  /-- what the row opens on the committed weights gives the first group's pending row at the merge's
  record -/
  wo : ∀ a τ fo o G w (g7 : Tg7) H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5, Lt.on a →
    Yes QK.L par pc a τ fo o G →
    LedG { par.P with tokv := QK.L.tokv a.1 } par.hp par.g fo o (QK.L.fork a.1) G
      (tapeAt par pc τ) [] H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 →
    TgRecF g7 { par.P with tokv := QK.L.tokv a.1 } par.hp par.g o (tapeAt par pc τ) H1 tT F4 G2
      G3 G3' →
    Lt.wo (behindOf QK.L pc a τ o G) w →
    WoSaysF QK.toLF.planF.fullF
      (aS7 (Plan4F.tailMKF A (numsKF QK.toLF.planF.fullF))
        (ksOf { par.P with tokv := QK.L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
        (Plan4F.nzAtF A (QK.L.tokv a.1) hds τ _) (x3Of QK.toLF.planF a.1 (tapeAt par pc τ)) g7).1.1
      (aS7 (Plan4F.tailMKF A (numsKF QK.toLF.planF.fullF))
        (ksOf { par.P with tokv := QK.L.tokv a.1 } par.hp) (tb3 (tapeAt par pc τ))
        (Plan4F.nzAtF A (QK.L.tokv a.1) hds τ _) (x3Of QK.toLF.planF a.1 (tapeAt par pc τ)) g7).2
      o.wo (part w)
  /-- the library's claim on the stream that comes in is worth 0 -/
  emb : ∀ a τ fo o G w, Lt.on a → Yes QK.L par pc a τ fo o G →
    Behind QK.L Sm Lt par (behindOf QK.L pc a τ o G) w →
    Blocks.Form.val (QK.toLF.planF.yKF par hS (ztSF QK.toLF.planF.fullF)
        (Plan4F.eKF A (numsKF QK.toLF.planF.fullF) Ex hds (a.1, fe a) τ) (part w))
      (embClaim (lateF (roomKF QK.toLF.planF par hS)) Sum.inr
        (((tailW QK.toLF.planF.fullF).y7
          (Plan4F.eKF A (numsKF QK.toLF.planF.fullF) Ex hds (a.1, fe a) τ)).1.2 (0 : Fin 1))
        QK.toLF.planF.fullF.mkE QK.toLF.planF.fullF.nb QK.toLF.planF.fullF.gB
        (stF QK.toLF.planF.fullF
          (Plan4F.eKF A (numsKF QK.toLF.planF.fullF) Ex hds (a.1, fe a) τ)).pb) = 0

/-- **The five fields from the three**, the value's choices, the promise's line, the public lines,
the rotary tables' fit and the four lines on the reads. -/
theorem Plan4KF.owes3F_of4 (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {s : WsShape} {lk first : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (V : Plan4L.ValueIs QK.toLF.toPlan4L par hS)
    (N : Plan4L.FrontIs QK.toLF.toPlan4L par QK.L Lt first s0 h3 Q3)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toLF.planF.fullF.D
      QK.toLF.planF.fullF.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toLF.planF.fullF.D QK.toLF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (R : ReadsAre par Sm nu tl h3 fun w => QK.mats (part w))
    (O : QK.Owes4F A Sm Lt Ex pc hds fe part) : QK.Owes3F A Sm Lt Ex pc hds fe part nu :=
  { kept := O.kept
    reads := fun a _ _ _ _ w _ Y _ Xp G2 t4 PX Fl _ =>
      reads_at QK.L Y (hl (QK.L.tokv a.1)) Sm R w Xp G2 t4 PX Fl
    planes := fun a τ fo o G w _ _ ha Y _ h1 =>
      have fr := front_of_leftAt QK.L (N.on a ha)
        (Pp := { par.P with tokv := QK.L.tokv a.1 }) N.fo N.pub N.ok
      Plan4LF.planes_atF A QK.L Y fr.1 (hl (QK.L.tokv a.1)) (fr.2.2 fo Y.look).1 (hr a τ fo o G Y)
        V Sm R (shape_of_leftAt QK.L (N.on a ha) Y.look) w h1
    wo := O.wo
    emb := O.emb }

/-- **`K04LawAt` at the first group, at a value that reads its letters off a seat, the reads true by
make**, at a piece whose errors are the cap, from `MeetsF`, the piece's rounds and back, C, hk,
`ValueIs`, `ValueMoreF`, the bound on Q3, the layout's line, the matrices' zeros, the seat's two
laws, the public lines, the rotary tables' fit, `LettersAreF`, `FrontIs`, `ReadsAre` and
`Owes4F`. -/
theorem Plan4KF.k04LawAt_K4F (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl)
    (Sm : Sem Wt) (Lt : Letters T Wt Fr) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par)
    (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds))
    (C : QK.toLF.planF.D.ChOK)
    (hk : ∀ l, l < QK.toLF.planF.D.nl → (QK.toLF.planF.D.Pl l).kq = (QK.toLF.planF.D.Pl l).kk ∨
      (16 ≤ (QK.toLF.planF.D.Pl l).kq ∧ 16 ≤ (QK.toLF.planF.D.Pl l).kk))
    (V : Plan4L.ValueIs QK.toLF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QK.toLF)
    (lw : ℕ → LW Cb.Gl.E)
    {s : WsShape} {lk : ℕ} {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (hQ : ∀ F, Q3 F → F.ns ≤ QK.ns + 1) (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toLF.planF.fullF.D
      QK.toLF.planF.fullF.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toLF.planF.fullF.D QK.toLF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (M : Plan4LF.LettersAreF A QK.L Sm Lt Ex pc hds (fun a => (a.1, fe a)) part nu first)
    (N : Plan4L.FrontIs QK.toLF.toPlan4L par QK.L Lt first s0 h3 Q3)
    (R : ReadsAre par Sm nu tl h3 fun w => QK.mats (part w))
    (O : QK.Owes4F A Sm Lt Ex pc hds fe part) : K04LawAt QK.L Sm Lt part par bk pc :=
  QK.k04LawAt_K3capF A Sm Lt Ex bk pc hds fe part hback hcap C hk V V2 lw hQ hy hz hseat hl hr M N
    (QK.owes3F_of4 A Sm Lt Ex pc hds fe part V N hl hr R O)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4KF.owes3F_of4
#print axioms OnBytes.Road.K4.Plan4KF.k04LawAt_K4F
