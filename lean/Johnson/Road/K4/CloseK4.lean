-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK4.lean: Johnson/Road/K4/CloseK3.lean's TOP WITH THE TWO FIELDS ON TRUE READS
CONCLUDED, where the statement's letter for the true value of an entry is filled by the definition
`entryTrue` at the value's own matrices (`ReadsAre`, Johnson/Road/K4/CloseReads.lean). A record and
two theorems. Glue: `reads_at` and `Plan4L.planes_at` laid into `Plan4K.Owes3`. No draw, no count.

  `Plan4K.Owes4`: WHAT IS STILL OWED: TWO FIELDS: kept (the promise behind holds at a yes) · wo
  (what the row opens on the committed weights gives the pending row at the merge's record).
  `Plan4K.owes3_of4`: `Owes3` from `Owes4`, `ValueIs`, `FrontIs`, the public lines, the rotary
  tables' fit and `ReadsAre`.
  `Plan4K.k04LawAt_K4`: `K04LawAt QK.L Sm Lt part par bk pc` at a piece whose errors are the cap.

Limits. K04_law IS NOT PROVED BY THIS. BOTH FIELDS OF `Owes4`, EVERY LINE OF `ReadsAre`, OF
`FrontIs` AND OF `LettersAre` ARE UNPAID HERE; so are `Meets`, `ValueIs`, `ValueMore`, pc.ds,
pc.back, that the errors are the cap, C, hk, the bound on Q3, the layout's line, the matrices'
zeros, the seat's two laws, the public lines and the rotary tables' fit. THE READS ARE TRUE BY MAKE
(EntryTrue.lean's limits): that the committed reads are these is another row's matter. Nothing shows
that all can be met together. The letters `Sem`, `Letters`, part, fe, Ex, nu, first, h3, Q3 and
those of `Plan4K` are not filled in this file: CloseFill.lean lays `Sem`, `Letters` and nu from the
others (`Plan4K.semOf`, `lettersOf`, `nuOf`), which it does not fill. A group that is not the first.
USER: `Plan4K.k04LawAt_K5` (CloseK5.lean).
-/
import Johnson.Road.K4.CloseK3
import Johnson.Road.K4.CloseReads

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

/-- **What is still owed where the reads are true by make.** -/
structure Plan4K.Owes4 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl)
    (Lt : Letters T Wt Fr) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (part : Wt → Mm) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
    Lt.on' (behindOf QK.L pc a τ o G)
  /-- what the row opens on the committed weights gives the pending row at the merge's record -/
  wo : ∀ a τ fo o G w (g7 : Tg7) H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4, Lt.on a →
    Yes QK.L par pc a τ fo o G →
    Led7 { par.P with tokv := QK.L.tokv a.1 } par.hp par.g fo o (QK.L.fork a.1) G
      (tapeAt par pc τ) [] H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 →
    TgRec g7 { par.P with tokv := QK.L.tokv a.1 } par.hp o (tapeAt par pc τ) H1 tT F4 G2 G3 G3' →
    Lt.wo (behindOf QK.L pc a τ o G) w →
    WoSays QK.toL.plan.full (aS7 (Plan4.tailMK A (numsK QK.toL.plan.full))
      (ksOf { par.P with tokv := QK.L.tokv a.1 } par.hp) ((tapeAt par pc τ).drop 1)
      (Plan4.nzAt A (QK.L.tokv a.1) hds τ _) (a.1, ptOf QK.toL.plan (tapeAt par pc τ)) g7)
      o.wo (part w)

/-- **The four fields from the two**, the value's choices, the promise's line, the public lines,
the rotary tables' fit and the four lines on the reads. -/
theorem Plan4K.owes3_of4 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {s : WsShape} {lk first : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (V : Plan4L.ValueIs QK.toL par hS) (N : Plan4L.FrontIs QK.toL par QK.L Lt first s0 h3 Q3)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toL.plan.full.D
      QK.toL.plan.full.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toL.plan.full.D QK.toL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (R : ReadsAre par Sm nu tl h3 fun w => QK.mats (part w))
    (O : QK.Owes4 A Lt pc hds part) : QK.Owes3 A Sm Lt Ex pc hds fe part nu :=
  { kept := O.kept
    reads := fun a _ _ _ _ w _ Y _ Xp G2 t4 PX Fl _ =>
      reads_at QK.L Y (hl (QK.L.tokv a.1)) Sm R w Xp G2 t4 PX Fl
    planes := fun a τ fo o G w _ _ ha Y _ h1 =>
      have fr := front_of_leftAt QK.L (N.on a ha)
        (Pp := { par.P with tokv := QK.L.tokv a.1 }) N.fo N.pub N.ok
      Plan4L.planes_at A QK.L Y fr.1 (hl (QK.L.tokv a.1)) (fr.2.2 fo Y.look).1 (hr a τ fo o G Y) V
        Sm R (shape_of_leftAt QK.L (N.on a ha) Y.look) w h1
    wo := O.wo }

/-- **`K04LawAt` at a group that is not the first, at a value that reads its letters off a seat,
the reads true by make**, at a piece whose errors are the cap, from `Meets`, the piece's rounds and
back, C, hk, `ValueIs`, `ValueMore`, the bound on Q3, the layout's line, the matrices' zeros, the
seat's two laws, the public lines, the rotary tables' fit, `LettersAre`, `FrontIs`, `ReadsAre` and
`Owes4`. -/
theorem Plan4K.k04LawAt_K4 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsLater par)
    (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QK.toL.plan.D.ChOK)
    (hk : ∀ l, l < QK.toL.plan.D.nl → (QK.toL.plan.D.Pl l).kq = (QK.toL.plan.D.Pl l).kk ∨
      (16 ≤ (QK.toL.plan.D.Pl l).kq ∧ 16 ≤ (QK.toL.plan.D.Pl l).kk))
    (V : Plan4L.ValueIs QK.toL par hS) (V2 : Plan4L.ValueMore QK.toL) (lw : ℕ → LW Cb.Gl.E)
    {s : WsShape} {lk : ℕ} {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (hQ : ∀ F, Q3 F → F.ns ≤ QK.ns + 1) (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toL.plan.full.D
      QK.toL.plan.full.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toL.plan.full.D QK.toL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (M : Plan4L.LettersAre A QK.L Sm Lt Ex pc hds (fun a => (a.1, fe a)) part nu first)
    (N : Plan4L.FrontIs QK.toL par QK.L Lt first s0 h3 Q3)
    (R : ReadsAre par Sm nu tl h3 fun w => QK.mats (part w))
    (O : QK.Owes4 A Lt pc hds part) : K04LawAt QK.L Sm Lt part par bk pc :=
  QK.k04LawAt_K3 A Sm Lt Ex bk pc hds fe part hback hcap C hk V V2 lw hQ hy hz hseat hl hr M N
    (QK.owes3_of4 A Sm Lt Ex pc hds fe part V N hl hr R O)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4K.owes3_of4
#print axioms OnBytes.Road.K4.Plan4K.k04LawAt_K4
