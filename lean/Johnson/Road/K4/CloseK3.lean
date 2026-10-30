-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK3.lean: Johnson/Road/K4/CloseK2.lean's TOP AT THE VALUE THAT READS ITS LETTERS
OFF A SEAT (`Plan4K`, Johnson/Road/K4/ValueSeat.lean), the first statement being the record itself.
Of the nine fields of `Plan4L.Owes2`, ties is concluded; of reads the clause on the cells; ns from
the promise's line and a bound on the letter Q3. seat, lines and rope move out of the record and
stand as premises of their own, in the forms in which CloseSeated.lean and MemberOwes.lean conclude
them. A record and three theorems. Glue: `Plan4K.look_at` and `Plan4K.readsAt` (CloseAt.lean) laid
into the record. No draw, no count.

  `ns_of_leftAt`: under `K3LeftAt` the ledger in hand has the number of slots of the ledger in front
  of the lookup (`PadLeft.rest`): a bound that Q gives of that ledger holds of the one in hand.
  `Plan4K.Owes3`: WHAT IS STILL OWED: FOUR FIELDS: kept · reads (the reads of the value's own
  matrices of part w are true) · planes (`K4ReadsTrue`) · wo.
  `Plan4K.owes2_of3`: `Owes2` from `Owes3`, `FrontIs`, the bound on Q3, the layout's line, «the
  matrices read as 0 outside the bounds», the seat's two laws wherever the seat finds the lookup's
  return, the plan's public lines and the rotary tables' fit.
  `Plan4K.k04LawAt_K3`: `K04LawAt QK.L Sm Lt part par bk pc` at a piece whose errors are the cap.

Limits. K04_law IS NOT PROVED BY THIS. EVERY FIELD OF `Owes3`, EVERY LINE OF `FrontIs` AND OF
`LettersAre` IS UNPAID HERE; so are `Meets`, `ValueIs`, `ValueMore`, pc.ds, pc.back, that the errors
are the cap, C, hk, the bound on Q3, the layout's line, the matrices' zeros, the seat's two laws,
the public lines and the rotary tables' fit. Nothing shows that all can be met together. The letters
`Sem`, `Letters`, part, fe, Ex, nu, first, h3, Q3 and those of `Plan4K` are not filled in this file:
CloseFill.lean lays `Sem`, `Letters` and nu from the others (`Plan4K.semOf`, `lettersOf`, `nuOf`),
which it does not fill. WHAT BINDS reads AND planes TOGETHER IS NOT SAID HERE: both speak of the
entries of the three tables on the planes' matrix, the one through the value's matrices, the other
through nu: they can hold together only if nu's cells are that matrix's entries (`ReadsAre.cell`,
CloseReads.lean). USER: `Plan4K.k04LawAt_K4` (CloseK4.lean). A group that is not the first.

-/
import Johnson.Road.K4.CloseK2
import Johnson.Road.K4.CloseAt

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

omit scl in
/-- **The number of slots of the ledger in hand**, from the sharp promise and a bound that its
letter Q gives of the ledger in front of the lookup. -/
theorem ns_of_leftAt (L : Seat T) {h : OnBytes.Model.Forest.Shape} {lm first n : ℕ}
    {Q : Fork → Prop} {x : T} (H : K3LeftAt (fun s => some (L.fork s)) L.look h lm first Q x)
    (hQ : ∀ F, Q F → F.ns ≤ n) : (L.fork x).ns ≤ n := by
  obtain ⟨F, F', g, rs, hq, _, K, _, hk⟩ := H
  obtain rfl : L.fork x = F' := Option.some.inj hk
  rw [K.padLeft.rest.2.1]
  exact hQ F hq

/-- **What is still owed at a value that reads its letters off a seat.** -/
structure Plan4K.Owes3 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    (nu : Wt → _root_.Fo.Pl → Cb.Gl.E) : Prop where
  /-- the promise behind holds -/
  kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
    Lt.on' (behindOf QK.L pc a τ o G)
  /-- the reads of the value's own matrices are true -/
  reads : ∀ a τ fo o G w, Lt.on a → Yes QK.L par pc a τ fo o G →
    Behind QK.L Sm Lt par (behindOf QK.L pc a τ o G) w →
    ∀ (Xp : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt Xp { par.P with tokv := QK.L.tokv a.1 } par.hp fo o G2 t4 QK.toL.plan.full.D
        QK.toL.plan.full.tb hS →
      ∀ Fl, Fo.Later G Fl →
        Xp.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) (QK.mats (part w))
  /-- the three planes' tables' reads are true in the world of the ledger behind the first run -/
  planes : ∀ a τ fo o G w fs₁ F₁, Lt.on a → Yes QK.L par pc a τ fo o G →
    Behind QK.L Sm Lt par (behindOf QK.L pc a τ o G) w → frontRun par o G = some (fs₁, F₁) →
    K4ReadsTrue gl o.v fo F₁ (nu w) (Sm.entryT o w)
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

/-- **The nine fields from the four**, the promise's line, the bound on Q3, the layout's line, the
matrices' zeros, the seat's two laws, the public lines and the rotary tables' fit. -/
theorem Plan4K.owes2_of3 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {s : WsShape} {lk first : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (N : Plan4L.FrontIs QK.toL par QK.L Lt first s0 h3 Q3)
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
    (O : QK.Owes3 A Sm Lt Ex pc hds fe part nu) :
    Plan4L.Owes2 A QK.L Sm Lt Ex pc hds (fun a => (a.1, fe a)) part nu s lk s0 tl :=
  { kept := O.kept
    seat := fun a _ fo _ _ _ Y => hseat a.1 fo Y.look
    ns := fun a ha => ns_of_leftAt QK.L (N.on a ha) hQ
    lines := hl
    ties := fun _ _ _ _ _ _ Y => QK.look_at Y.look
    rope := fun a τ fo o G _ Y => hr a τ fo o G Y
    reads := fun a τ fo o G w ha Y hB =>
      ⟨QK.mats (part w), QK.readsAt Sm part hy a.1 fo o G w (hz (part w))
        (O.reads a τ fo o G w ha Y hB)⟩
    planes := O.planes
    wo := O.wo }

/-- **`K04LawAt` at a group that is not the first, at a value that reads its letters off a seat**,
at a piece whose errors are the cap, from `Meets`, the piece's rounds and back, C, hk, `ValueIs`,
`ValueMore`, the bound on Q3, the layout's line, the matrices' zeros, the seat's two laws, the
public lines, the rotary tables' fit, `LettersAre`, `FrontIs` and `Owes3`. -/
theorem Plan4K.k04LawAt_K3 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl) (Sm : Sem Wt)
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
    (O : QK.Owes3 A Sm Lt Ex pc hds fe part nu) :
    K04LawAt QK.L Sm Lt part par bk pc :=
  Plan4L.k04LawAt_K2 A QK.L Sm Lt Ex bk pc hds (fun a => (a.1, fe a)) part hback hcap C hk V V2 lw
    M N (QK.owes2_of3 A Sm Lt Ex pc hds fe part N hQ hy hz hseat hl hr O)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.ns_of_leftAt
#print axioms OnBytes.Road.K4.Plan4K.owes2_of3
#print axioms OnBytes.Road.K4.Plan4K.k04LawAt_K3
