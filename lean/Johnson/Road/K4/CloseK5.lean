-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK5.lean: Johnson/Road/K4/CloseK4.lean's TOP WITH THE FIELD wo BROUGHT DOWN TO
ONE LINE ON THE STATEMENT's LETTER `Letters.wo`. A definition and two theorems. Glue:
`Plan4L.wo_at` (CloseWo.lean) laid into `Plan4K.Owes4`. No draw, no count.

  `Plan4K.WoRow par o m`: THE ROW's SENTENCE, at a record o of K4's hearing, of which it reads o.wo
  («the record wo» below): there are a number of claims, a shape, a number im, messages os and os',
  a row r and a reading idx of the index masks' entries with: `pendingRowO` at the plan's layout of
  the weights, im, the record wo, these claims, shape and messages returns (r, os') · each mask
  entry that r names reads as the value's own mask entry c7 of m · the sum over the cube's rows of
  the row's weight times the committed matrix's row read at r's point turned round, plus the named
  mask entries times their factors, is the reading of r's target.
  `Plan4K.owes4_of_row`: `Owes4` from kept, from the line «`Lt.wo` b w gives `WoRow` at the record
  that the seat finds in b and at part w», and from what `wo_at` asks beside.
  `Plan4K.k04LawAt_K5`: `K04LawAt QK.L Sm Lt part par bk pc` at a piece whose errors are the cap.

Limits. K04_law IS NOT PROVED BY THIS. kept AND THE LINE ON `Lt.wo` ARE UNPAID HERE; so is every
premise of `k04LawAt_K4` but `Owes4`. `WoRow` SAYS «THERE ARE»: im, os, the claims' number and the
shape are tied to nothing: that a layers' link's end calls `pendingRowO` at the index masks' number,
the statement's messages and the plan's count is not said here; by `wo_at` the sentence is worth the
same at each choice at which the routine returns and the mask entries read so. The cells are the
value's own weights of m. Nothing shows that all can be met together. A group that is not the first.
USER: `Plan4K.k04LawAt_fill` (CloseFill.lean), `RefSeat.k04LawAt_ref` (CloseRef.lean).
-/
import Johnson.Road.K4.CloseK4
import Johnson.Road.K4.CloseWo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Finset
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker OnBytes.Road OnBytes.Road.Rows
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters K04LawAt)
open VerifiableInference.Desc.First.Pend (pendingRowO)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The row's sentence**, at a record o of K4's hearing and a tuple m of messages. -/
def Plan4K.WoRow (QK : Plan4K Mm T) (par : Par) (o : Own) (m : Mm) : Prop :=
  ∃ (claims : ℕ) (S : Params.LinShape) (im : ℕ) (os os' : Array Oracle) (r : TensorRow)
    (idx : ℕ → Cb.Gl.E),
    pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os') ∧
    (∀ y ∈ r.masks, idx y.1.index = QK.toL.plan.full.msg m QK.toL.plan.full.c7) ∧
    ∑ j ∈ range (2 ^ S.kRow),
        pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
          (QK.toL.plan.full.Wn (QK.toL.plan.full.msg m)) j +
      (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target

/-- **The two fields from kept and the line on `Lt.wo`.** -/
theorem Plan4K.owes4_of_row (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsLater par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    {s : WsShape} {lk first : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (V : Plan4L.ValueIs QK.toL par hS) (V2 : Plan4L.ValueMore QK.toL) (lw : ℕ → LW Cb.Gl.E)
    (N : Plan4L.FrontIs QK.toL par QK.L Lt first s0 h3 Q3)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toL.plan.full.D
      QK.toL.plan.full.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toL.plan.full.D QK.toL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
      Lt.on' (behindOf QK.L pc a τ o G))
    (hwo : ∀ b w o, Lt.wo b w → QK.L.own b.1 = some o → QK.WoRow par o (part w)) :
    QK.Owes4 A Lt pc hds part :=
  { kept := kept
    wo := fun a τ fo o G w g7 _ _ _ _ _ _ _ _ _ _ _ _ ha Y Ld I hw => by
      obtain ⟨claims, S, im, os, os', r, idx, hrow, hidx, hsum⟩ :=
        hwo _ w o hw ((hseat a.1 fo Y.look).own G o)
      have fr := front_of_leftAt QK.L (N.on a ha)
        (Pp := { par.P with tokv := QK.L.tokv a.1 }) N.fo N.pub N.ok
      obtain ⟨K, hfil, _⟩ := fr.2.2 fo Y.look
      obtain ⟨hz0, hk0, _⟩ := QK.look_at Y.look
      exact (Plan4L.wo_at A QK.L Ex hds (fun a => (a.1, fe a)) part a τ Y w fr.1
        (hl (QK.L.tokv a.1)) K (hr a τ fo o G Y) lw hz0 hk0 hfil V V2 g7 Ld I claims S hrow
        idx hidx).2 hsum }

/-- **`K04LawAt` at a group that is not the first, at a value that reads its letters off a seat,
the reads true by make, the field wo a line on the letter**, at a piece whose errors are the cap. -/
theorem Plan4K.k04LawAt_K5 (QK : Plan4K Mm T) (A : QK.toL.plan.Meets par hS pcl) (Sm : Sem Wt)
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
    (kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
      Lt.on' (behindOf QK.L pc a τ o G))
    (hwo : ∀ b w o, Lt.wo b w → QK.L.own b.1 = some o → QK.WoRow par o (part w)) :
    K04LawAt QK.L Sm Lt part par bk pc :=
  QK.k04LawAt_K4 A Sm Lt Ex bk pc hds fe part hback hcap C hk V V2 lw hQ hy hz hseat hl hr M N R
    (QK.owes4_of_row A Lt Ex pc hds fe part V V2 lw N hseat hl hr kept hwo)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4K.owes4_of_row
#print axioms OnBytes.Road.K4.Plan4K.k04LawAt_K5
