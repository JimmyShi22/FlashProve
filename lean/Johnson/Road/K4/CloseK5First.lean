-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseK5First.lean: Johnson/Road/K4/CloseK4First.lean's TOP WITH THE FIELD wo BROUGHT
DOWN TO ONE LINE ON THE STATEMENT's LETTER `Letters.wo`, AND THE FIELD emb PAID, AT THE LIBRARY's
REFERENCE SIZES. The twin of Johnson/Road/K4/CloseK5.lean. A definition and two theorems. Glue:
`Plan4LF.wo_atF_ref` (Johnson/Road/K4/CloseWoFirst.lean) and `Plan4LF.emb_at`
(Johnson/Road/K4/CloseEmbFirst.lean) laid into `Plan4KF.Owes4F`. No draw, no count.

  `Plan4KF.WoRowF par o m`: THE ROW's SENTENCE, `Plan4K.WoRow` (CloseK5.lean) word for word at the
    first group's value's letters: there are a number of claims, a shape, a number im, messages os
    and os', a row r and a reading idx of the index masks' entries with: `pendingRowO` at the plan's
    layout of the weights, im, the record o.wo, these claims, shape and messages returns (r, os') ·
    each mask entry that r names reads as the value's own mask entry c7 of m · the sum over the
    cube's rows of the row's weight times the committed matrix's row read at r's point turned round,
    plus the named mask entries times their factors, is the reading of r's target.
  `Plan4KF.owes4F_of_row`: `Owes4F` from kept, from the line «`Lt.wo` b w gives `WoRowF` at the
    record that the seat finds in b and at part w», and from what `wo_atF_ref` and `emb_at` ask
    beside.
  `Plan4KF.k04LawAt_K5F`: `K04LawAt QK.L Sm Lt part par bk pc` at a piece whose errors are the cap.

WHAT IS OTHER THAN IN A LATER GROUP: FOUR PREMISES ON SIZES: the value's sizes are the library's
reference ones (D.P = ppref, kW = kRef), the plan's size of the vocabulary is ppref.V, and `EmbNums`
(Johnson/Meaning/EmbWeight.lean) holds of the plan's layout: `wo_atF_ref` asks them for the one
claim more, the embedding's. THE TIE OF THE TOKENS IS HAD BY THE VALUE's OWN MAKE, by unfolding
(what `Plan4KF.tok_at`, ValueSeatFirst.lean, says; that lemma is not called). OF THE FIELD wo THE
EMBEDDING's SHARE ALONE IS PAID SO: the field itself goes down to the line on `Lt.wo`, as in a later
group.

Limits. K04_law IS NOT PROVED BY THIS. kept AND THE LINE ON `Lt.wo` ARE UNPAID HERE; so are the four
premises on sizes and every premise of `k04LawAt_K4F` but `Owes4F`. `WoRowF` SAYS «THERE ARE»: im,
os, the claims' number and the shape are tied to nothing (CloseK5.lean's limits). Nothing shows that
all can be met together. The reference sizes alone. The first group alone. USER:
`RefSeat.k04LawAt_refF` (CloseRefFirst.lean), `Plan4KF.k04LawAt_fillF` (CloseFillFirst.lean).

-/
import Johnson.Road.K4.CloseK4First
import Johnson.Road.K4.CloseK5
import Johnson.Road.K4.CloseWoFirst
import Johnson.Road.K4.CloseEmbFirst

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
open Inst.Model (Scl ppref)
open Inst.Model.Layout (kRef)
open Meaning.Emb (EmbNums)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The row's sentence**, at a record o of K4's hearing and a tuple m of messages, at the first
group's value's letters. -/
def Plan4KF.WoRowF (QK : Plan4KF Mm T) (par : Par) (o : Own) (m : Mm) : Prop :=
  ∃ (claims : ℕ) (S : Params.LinShape) (im : ℕ) (os os' : Array Oracle) (r : TensorRow)
    (idx : ℕ → Cb.Gl.E),
    pendingRowO par.P.wsLay im o.wo claims S os = .ok (r, os') ∧
    (∀ y ∈ r.masks, idx y.1.index = QK.toLF.planF.fullF.msg m QK.toLF.planF.fullF.c7) ∧
    ∑ j ∈ range (2 ^ S.kRow),
        pendWeight gl r.g j * rowAt gl par.P.wsLay.lk r.psi.reverse.toArray
          (QK.toLF.planF.fullF.Wn (QK.toLF.planF.fullF.msg m)) j +
      (r.masks.map fun y => idx y.1.index * gl.val y.2).sum = gl.val r.target

/-- **The three fields from kept and the line on `Lt.wo`**, the value's choices, the promise's line,
the layout's line, the matrices' zeros, the seat's two laws, the public lines, the rotary tables'
fit, the masks' line, `ReadsAre` and the four premises on sizes. -/
theorem Plan4KF.owes4F_of_row (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl)
    (Sm : Sem Wt) (Lt : Letters T Wt Fr) (Ex : ExtSpec) (pc : Piece (ckP .two) Fr T Cl Wt)
    (hds : pc.ds = dsFirst par) (fe : T × Fr.E.Str → Ex.Str) (part : Wt → Mm)
    {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {s : WsShape} {lk first : ℕ}
    {s0 h3 : OnBytes.Model.Forest.Shape} {tl : HTailF2} {Q3 : Fork → Prop}
    (V : Plan4L.ValueIs QK.toLF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QK.toLF)
    (lw : ℕ → LW Cb.Gl.E) (N : Plan4L.FrontIs QK.toLF.toPlan4L par QK.L Lt first s0 h3 Q3)
    (hy : QK.y = par.P.y)
    (hz : ∀ m a b c, ¬ (a < QK.nM ∧ b < QK.nR ∧ c < QK.nC) → QK.mats m a b c = 0)
    (hseat : ∀ x fo, QK.L.look x = some fo → SeatOk QK.L x)
    (hl : ∀ tk, PubLines { par.P with tokv := tk } par.g hS pcl QK.toLF.planF.fullF.D
      QK.toLF.planF.fullF.tb s lk s0 tl)
    (hr : ∀ a τ fo o G, Yes QK.L par pc a τ fo o G →
      ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
        RopeFits Reading.gl
          { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
          QK.toLF.planF.fullF.D QK.toLF.planF.fullF.tb (par.g * par.P.y.Lam) lam)
    (hSm : ∀ w, Sm.mask w = QK.toLF.planF.maskAt (part w))
    (R : ReadsAre par Sm nu tl h3 fun w => QK.mats (part w))
    (hP : QK.toLF.planF.fullF.D.P = ppref) (hkR : QK.toLF.planF.fullF.kW = kRef)
    (hV : par.P.V = ppref.V) (NE : EmbNums par.P.y)
    (kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
      Lt.on' (behindOf QK.L pc a τ o G))
    (hwo : ∀ b w o, Lt.wo b w → QK.L.own b.1 = some o → QK.WoRowF par o (part w)) :
    QK.Owes4F A Sm Lt Ex pc hds fe part :=
  { kept := kept
    wo := fun a τ fo o G w g7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ ha Y Ld I hw => by
      obtain ⟨claims, S, im, os, os', r, idx, hrow, hidx, hsum⟩ :=
        hwo _ w o hw ((hseat a.1 fo Y.look).own G o)
      have fr := front_of_leftAt QK.L (N.on a ha)
        (Pp := { par.P with tokv := QK.L.tokv a.1 }) N.fo N.pub N.ok
      obtain ⟨K, hfil, _⟩ := fr.2.2 fo Y.look
      obtain ⟨hz0, hk0, _⟩ := QK.look_atF Y.look
      exact (Plan4LF.wo_atF_ref A QK.L Ex hds (fun a => (a.1, fe a)) part a τ Y w fr.1
        (hl (QK.L.tokv a.1)) K (hr a τ fo o G Y) lw hz0 hk0 hfil V V2 g7 Ld I hP hkR hV
        (fun _ _ => rfl) NE claims S hrow idx hidx).2 hsum
    emb := fun a τ fo o G w ha Y hB => by
      have fr := front_of_leftAt QK.L (N.on a ha)
        (Pp := { par.P with tokv := QK.L.tokv a.1 }) N.fo N.pub N.ok
      obtain ⟨K, hfil, _⟩ := fr.2.2 fo Y.look
      obtain ⟨hz0, hk0, _⟩ := QK.look_atF Y.look
      obtain ⟨hR, hcells⟩ := QK.readsAtF Sm part hy a.1 fo o G w (hz (part w))
        (fun Xp G2 t4 PX Fl _ => reads_at QK.L Y (hl (QK.L.tokv a.1)) Sm R w Xp G2 t4 PX Fl)
      have nx : QK.toLF.n0 = (QK.L.fork a.1).next := by
        rw [fr.2.1]
        exact N.n0
      exact Plan4LF.emb_at A QK.L Sm Lt Ex hds (a.1, fe a) part a τ Y w hB
        (hseat a.1 fo Y.look) fr.1 (hl (QK.L.tokv a.1)) K (hr a τ fo o G Y) lw hz0 hk0 hfil
        (QK.mats (part w)) hR hcells V V2 nx (hSm w) }

/-- **`K04LawAt` at the first group, at a value that reads its letters off a seat, the reads true by
make, the field wo a line on the letter**, at a piece whose errors are the cap: from `MeetsF`, the
piece's rounds and back, that its errors are the cap, C, hk, `ValueIs`, `ValueMoreF`, the bound on
Q3, the layout's line, the matrices' zeros, the seat's two laws, the public lines, the rotary
tables' fit, `LettersAreF`, `FrontIs`, `ReadsAre`, the four premises on sizes, kept and the line on
`Lt.wo`. -/
theorem Plan4KF.k04LawAt_K5F (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl)
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
    (hP : QK.toLF.planF.fullF.D.P = ppref) (hkR : QK.toLF.planF.fullF.kW = kRef)
    (hV : par.P.V = ppref.V) (NE : EmbNums par.P.y)
    (kept : ∀ a τ fo o G, Lt.on a → Yes QK.L par pc a τ fo o G →
      Lt.on' (behindOf QK.L pc a τ o G))
    (hwo : ∀ b w o, Lt.wo b w → QK.L.own b.1 = some o → QK.WoRowF par o (part w)) :
    K04LawAt QK.L Sm Lt part par bk pc :=
  QK.k04LawAt_K4F A Sm Lt Ex bk pc hds fe part hback hcap C hk V V2 lw hQ hy hz hseat hl hr M N R
    (QK.owes4F_of_row A Sm Lt Ex pc hds fe part V V2 lw N hy hz hseat hl hr M.mask R hP hkR hV NE
      kept hwo)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4KF.owes4F_of_row
#print axioms OnBytes.Road.K4.Plan4KF.k04LawAt_K5F
