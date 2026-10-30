-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK3First.lean: Johnson/Road/K4/CloseKFirst.lean's TOP AT THE FIRST GROUP's VALUE
THAT READS ITS LETTERS OFF A SEAT (`Plan4KF`, Johnson/Road/K4/ValueSeatFirst.lean), the first
statement being the record itself AND THE VALUE's TOKENS BEING THE SEAT's. The twin of
Johnson/Road/K4/CloseK3.lean. Of the ten fields of `Plan4LF.OwesF`, ties is concluded; of reads the
clause on the cells; ns from the promise's line and a bound on the letter Q3. seat, lines and rope
move out of the record and stand as premises of their own, in the forms of CloseK3.lean. A record
and two theorems. Glue: `Plan4KF.look_atF` and `Plan4KF.readsAtF` laid into the record;
`ns_of_leftAt` (CloseK3.lean) names no group and is taken as it stands. No draw, no count.

  `Plan4KF.Owes3F`: WHAT IS STILL OWED: FIVE FIELDS: kept · reads (the reads of the value's own
    matrices of part w are true) · planes (`K4ReadsTrue`) · wo · emb (THE LIBRARY's CLAIM ON THE
    STREAM THAT COMES IN IS WORTH 0).
  `Plan4KF.owesF_of3`: `OwesF` from `Owes3F`, `FrontIs`, the bound on Q3, the layout's line, «the
    matrices read as 0 outside the bounds», the seat's two laws wherever the seat finds the lookup's
    return, the plan's public lines and the rotary tables' fit.
  `Plan4KF.k04LawAt_K3F`: `K04LawAt QK.L Sm Lt part par bk pc`.

THE TOKENS. At this value `Plan4F.J11` in the line idn of `LettersAreF` speaks of the tokens
(QK.L.tokv a.1).getD p 0 (`Plan4KF.tok_at`): those that K4's hearing reads at the record in front.

Limits. K04_law IS NOT PROVED BY THIS. EVERY FIELD OF `Owes3F`, EVERY LINE OF `FrontIs` AND OF
`LettersAreF` IS UNPAID HERE; so are `MeetsF`, `ValueIs`, `ValueMoreF`, pc.ds, pc.back, the errors'
premise (NOT concluded at the cap), C, hk, the bound on Q3, the layout's line, the matrices' zeros,
the seat's two laws, the public lines and the rotary tables' fit. Nothing shows that all can be met
together. The letters `Sem`, `Letters`, part, fe, Ex, nu, first, h3, Q3 and those of `Plan4KF` are
not filled in this file: CloseFillFirst.lean lays `Letters` (`Plan4KF.lettersOfF`) and
CloseFill.lean `Sem` and nu (`Plan4K.semOf`, `nuOf`) from the others, which they do not fill. The
first group alone.
-/
import Johnson.Road.K4.CloseK3
import Johnson.Road.K4.ValueSeatFirst

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
open OnBytes.Desc.First.P1 (gl Tg7 aS7)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind K04LawAt frontRun)
open VerifiableInference.OnPublicFiles (K4ReadsTrue K3LeftAt)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **What is still owed at the first group's value that reads its letters off a seat.** -/
structure Plan4KF.Owes3F (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
    Lt.on' (behindOf QK.L pc a τ o G)
  /-- the reads of the value's own matrices are true -/
  reads : ∀ a τ fo o G w, Lt.on a → Yes QK.L par pc a τ fo o G →
    Behind QK.L Sm Lt par (behindOf QK.L pc a τ o G) w →
    ∀ (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt Xp { par.P with tokv := QK.L.tokv a.1 } par.hp fo o G2 t4 QK.toLF.planF.fullF.D
        QK.toLF.planF.fullF.tb hS →
      ∀ Fl, Fo.Later G Fl →
        Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) (QK.mats (part w))
  /-- the three planes' tables' reads are true in the world of the ledger behind the first run -/
  planes : ∀ a τ fo o G w fs₁ F₁, Lt.on a → Yes QK.L par pc a τ fo o G →
    Behind QK.L Sm Lt par (behindOf QK.L pc a τ o G) w → frontRun par o G = some (fs₁, F₁) →
    K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w)
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

/-- **The ten fields from the five**, the promise's line, the bound on Q3, the layout's line, the
matrices' zeros, the seat's two laws, the public lines and the rotary tables' fit. -/
theorem Plan4KF.owesF_of3 (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {s : WsShape} {lk first : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (N : Plan4L.FrontIs QK.toLF.toPlan4L par QK.L Lt first s0 h3 Q3)
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
    (O : QK.Owes3F A Sm Lt Ex pc hds fe part nu) :
    Plan4LF.OwesF A QK.L Sm Lt Ex pc hds (fun a => (a.1, fe a)) part nu s lk s0 tl :=
  { kept := O.kept
    seat := fun a _ fo _ _ _ Y => hseat a.1 fo Y.look
    ns := fun a ha => ns_of_leftAt QK.L (N.on a ha) hQ
    lines := hl
    ties := fun _ _ _ _ _ _ Y => QK.look_atF Y.look
    rope := fun a τ fo o G _ Y => hr a τ fo o G Y
    reads := fun a τ fo o G w ha Y hB =>
      ⟨QK.mats (part w), QK.readsAtF Sm part hy a.1 fo o G w (hz (part w))
        (O.reads a τ fo o G w ha Y hB)⟩
    planes := O.planes
    wo := O.wo
    emb := O.emb }

/-- **`K04LawAt` at the first group, at a value that reads its letters off a seat**, from `MeetsF`,
the piece's rounds and back, the errors' premise, C, hk, `ValueIs`, `ValueMoreF`, the bound on Q3,
the layout's line, the matrices' zeros, the seat's two laws, the public lines, the rotary tables'
fit, `LettersAreF`, `FrontIs` and `Owes3F`. -/
theorem Plan4KF.k04LawAt_K3F (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl)
    (Sm : Sem Wt) (Lt : Letters T Wt Fr) (Ex : ExtSpec)
    (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par)
    (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (herr : Err.le ((Plan4F.mapsAtF A (numsKF QK.toLF.planF.fullF) Ex hds).err
      ((chFF QK.toLF.planF.fullF).eps Ex)) pc.err)
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
    (O : QK.Owes3F A Sm Lt Ex pc hds fe part nu) :
    K04LawAt QK.L Sm Lt part par bk pc :=
  Plan4LF.k04LawAt_KF A QK.L Sm Lt Ex bk pc hds (fun a => (a.1, fe a)) part hback herr C hk V V2
    lw M N (QK.owesF_of3 A Sm Lt Ex pc hds fe part N hQ hy hz hseat hl hr O)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4KF.owesF_of3
#print axioms OnBytes.Road.K4.Plan4KF.k04LawAt_K3F
