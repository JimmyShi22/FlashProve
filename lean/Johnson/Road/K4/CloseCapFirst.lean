-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseCapFirst.lean: THE FIRST GROUP's TWO TOPS (`Plan4LF.k04LawAt_KF`,
Johnson/Road/K4/CloseKFirst.lean; `Plan4KF.k04LawAt_K3F`, Johnson/Road/K4/CloseK3First.lean) AT A
PIECE WHOSE ERRORS ARE THE CAP (128 bits a written challenge): the errors' premise is concluded
(`Plan4F.herr_capF`, Johnson/Road/K4/CapFromMeetsFirst.lean). The twin of `Plan4L.k04LawAt_cap`
(CloseK.lean). Two theorems, each one call. No draw, no count.

Limits. K04_law IS NOT PROVED BY THIS. Those of the three files named, but for the errors' premise:
that the piece's errors are the cap is a premise in its place. EVERY FIELD OF `OwesF` | `Owes3F`,
EVERY LINE OF `LettersAreF` AND OF `FrontIs` IS UNPAID. The first group alone.
-/
import Johnson.Road.K4.CloseK3First
import Johnson.Road.K4.CapFromMeetsFirst

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
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters K04LawAt)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **`K04LawAt` at the first group, at a piece whose errors are the cap**, from `MeetsF`, the
piece's rounds and back, C, hk, `ValueIs`, `ValueMoreF`, `LettersAreF`, `FrontIs` and `OwesF`. -/
theorem Plan4LF.k04LawAt_capF {QF : Plan4LF Cb.Gl.E Mm X} (A : QF.planF.MeetsF par hS pcl)
    (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) (bk : VerifiableInference.Desc.Block T Cl)
    (pc : Piece (ckP .two) Fr T Cl Wt) (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (hback : pc.back = [])
    (hcap : pc.err = Err.cap 128 (uLT (ckP .two) pc.ds)) (C : QF.planF.D.ChOK)
    (hk : ∀ l, l < QF.planF.D.nl → (QF.planF.D.Pl l).kq = (QF.planF.D.Pl l).kk ∨
      (16 ≤ (QF.planF.D.Pl l).kq ∧ 16 ≤ (QF.planF.D.Pl l).kk))
    (V : Plan4L.ValueIs QF.toPlan4L par hS) (V2 : Plan4LF.ValueMoreF QF)
    (lw : ℕ → LW Cb.Gl.E) {s : WsShape} {lk : ℕ} {s0 h3 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2} {nu : Wt → _root_.Fo.Pl → Cb.Gl.E} {first : ℕ} {Q3 : Fork → Prop}
    (M : Plan4LF.LettersAreF A L Sm Lt Ex pc hds fa part nu first)
    (N : Plan4L.FrontIs QF.toPlan4L par L Lt first s0 h3 Q3)
    (O : Plan4LF.OwesF A L Sm Lt Ex pc hds fa part nu s lk s0 tl) :
    K04LawAt L Sm Lt part par bk pc :=
  Plan4LF.k04LawAt_KF A L Sm Lt Ex bk pc hds fa part hback
    (hcap ▸ Plan4F.herr_capF A (numsKF QF.planF.fullF) Ex hds) C hk V V2 lw M N O

/-- **The same at a value that reads its letters off a seat**, from `MeetsF`, the piece's rounds and
back, that the errors are the cap, C, hk, `ValueIs`, `ValueMoreF`, the bound on Q3, the layout's
line, the matrices' zeros, the seat's two laws, the public lines, the rotary tables' fit,
`LettersAreF`, `FrontIs` and `Owes3F`. -/
theorem Plan4KF.k04LawAt_K3capF (QK : Plan4KF Mm T) (A : QK.toLF.planF.MeetsF par hS pcl)
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
    (O : QK.Owes3F A Sm Lt Ex pc hds fe part nu) :
    K04LawAt QK.L Sm Lt part par bk pc :=
  QK.k04LawAt_K3F A Sm Lt Ex bk pc hds fe part hback
    (hcap ▸ Plan4F.herr_capF A (numsKF QK.toLF.planF.fullF) Ex hds) C hk V V2 lw hQ hy hz hseat hl
    hr M N O

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.k04LawAt_capF
#print axioms OnBytes.Road.K4.Plan4KF.k04LawAt_K3capF
