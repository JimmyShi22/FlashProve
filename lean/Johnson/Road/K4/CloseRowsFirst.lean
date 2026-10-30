-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRowsFirst.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST
GROUP, AND UNDER WHAT K4's ROW OPENS: THE FIVE OWN ROWS AND THE PART merge OF THE LIBRARY's LEDGER
(`RowsSayF`, Johnson/Road/K4/SixKFirst.lean) AT THE FIRST CHAIN's LAST STATEMENT `Plan4F.eKF` AND AT
THE ENTRIES `Plan4F.yKF` (CloseFirst.lean). The twin of Johnson/Road/K4/CloseRows.lean. A record and
one theorem. Glue: `Plan4LF.six_ledF` laid over `Plan4F.atYesF` (ClaimsYesFirst.lean),
`pubAtMore_of_ledF` and `Plan4LF.heard_KF` (CloseKitFirst.lean), `forms_of_behind`
(CloseBehind.lean), `Plan4F.val_of_claimsF` (CloseYesFirst.lean). No draw, no count.

  `Plan4LF.ValueMoreF QF`: three choices more of the value's letters, beside `Plan4L.ValueIs`
    (CloseSevenK.lean) at QF.toPlan4L: numI is `num4` at the value's numbering of the weight claims;
    that numbering gives `numK`'s numbers; there is room for the merge's own slots, which begin one
    slot later than in a later group.
  `Plan4LF.rows_atF`: `RowsSayF` at a yes, under what the row opens.

Limits. K04_law IS NOT PROVED BY THIS. PREMISES THAT STAY: the seat's two laws · the ledger in front
has arrays of the right sizes and its next free slot is the value's n0 · `ValueIs`, `ValueMoreF` ·
`PubLines`, `LookLines`, the rotary tables' fit · zOf, kTg, kIncS at the first statement; the
lookup's end form: filled slots alone, no entry, slots below ns + 1 · the statement's mask row is
the value's at part w · matrices Mt whose reads are true in the worlds of the ledgers behind the
runs, and whose cells are the message's. `Plan4F.MeetsF` and pc.ds = dsFirst par. Nothing on the
embedding's own claim (the part emb), on the pending row, on tok. Nothing shows that these can be
met together.
-/
import Johnson.Road.K4.SixKFirst
import Johnson.Road.K4.CloseSevenKFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open TWhole Iop Cb Cb.Sub Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At Cb.Pv.Lay.End Cb.Pv.Lay.End.Gated
open OnBytes OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model (Reading Fork Forest.Heard WsShape HTailF2)
open OnBytes.Model.Layer (Own)
open OnBytes.Desc.First.K4 (Par Seat k0 later_fo formsFrontWith_later formsBack_later)
open OnBytes.Desc.First.P1 (gl addsOf NzT tailT)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QF : Plan4LF Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **Three choices more of the first group's value's letters.** -/
structure Plan4LF.ValueMoreF (QF : Plan4LF Cb.Gl.E Mm X) : Prop where
  numI : QF.numI = num4 QF.D QF.num
  n4 : ∀ q, num4 QF.planF.fullF.D QF.planF.fullF.num q =
    num4 QF.planF.fullF.D (numK QF.planF.fullF.D) q
  room7F : QF.toPlan4L.slots.f7 + 1 + 1 + (2 * QF.planF.kW + 1) ≤ QF.ns

/-- **The five own rows and merge at a yes in the first group, under what the row opens** and the
premises that the head lists. -/
theorem Plan4LF.rows_atF (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
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
    (h0 : QF.n0 = (L.fork a.1).next) (hSm : Sm.mask w = QF.planF.maskAt (part w)) :
    RowsSayF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)
      (lateAtF QF.planF.fullF (lateF (roomKF QF.planF par hS))
        (fmOfF QF.planF.fullF (ztSF QF.planF.fullF) (par.P.y.lPd - par.P.y.ls) par.P.y.ls
          par.P.y.ls)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) := by
  obtain ⟨hinv, hscl, hvy, _, _, _⟩ :=
    Plan4LF.heard_KF A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5', g7, Ld, I, hc⟩ :=
    Plan4F.atYesF A (numsKF QF.planF.fullF) L hds a τ Y (fa a).1 hF B.S B.hs B.hg B.hrd B.hmats
      B.hρ B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM
      B.hpad hinv hscl hvy (A.lamM (L.tokv a.1)) gl_half
      (nums4_num4K QF.planF.fullF.toFullPar) lw hz0 hk0 hfil
  obtain ⟨Xp, PX, Xrd, Xe⟩ := pubAtMore_of_ledF Y.hears Ld B K Rp hinv
  obtain ⟨_, ⟨fs₁, F₁, fs₂, F₂, h1, h2, z1, z2⟩, _⟩ :=
    forms_of_behind L Sm Lt par pc a τ o G w hL hB
  have l1 : Fo.Later G F₁ := later_fo (formsFrontWith_later h1)
  have l2 : Fo.Later G F₂ := l1.trans (later_fo (formsBack_later h2))
  have he7 : Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ = _ :=
    Plan4F.val_of_claimsF A (numsKF QF.planF.fullF) Ex (L.tokv a.1) hds τ (fa a) _ hc
  -- the tape behind three single drops is the tape on which the lower files speak
  have key : ∀ (t' : Tape), (tapeAt par pc τ).drop (k0 par.g) = t' →
      ∀ nz : NzT QF.planF.fullF.ownF.toOwn.tail
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t',
      (tailT (Plan4F.tailMKF A (numsKF QF.planF.fullF))
        (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
        (addsOf (Plan4F.tailMKF A (numsKF QF.planF.fullF))
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
          (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7)).Claims
        (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) →
      Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ =
        (tailT (Plan4F.tailMKF A (numsKF QF.planF.fullF))
          (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
          (addsOf (Plan4F.tailMKF A (numsKF QF.planF.fullF))
            (ksOf { par.P with tokv := L.tokv a.1 } par.hp) t' nz
            (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7)).z7
          (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) →
      RowsSayF QF.planF.fullF (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)
        (part w)
        (lateAtF QF.planF.fullF (lateF (roomKF QF.planF par hS))
          (fmOfF QF.planF.fullF (ztSF QF.planF.fullF) (par.P.y.lPd - par.P.y.ls) par.P.y.ls
            par.P.y.ls)
          (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) := by
    intro t' e nz hc' he'
    subst e
    rw [he']
    exact Plan4LF.six_ledF A (L.tokv a.1) hF Y.hears Ld nz
      (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7 I hc'.c4 (fun _ => rfl) hz0 hk0 hkS hfil he hsl
      Xp PX Xrd Xe hvy hscl hinv lw (part w) (Sm.mask w) (Sm.entryT o w)
      ⟨h0, V.nT, V.nI, V2.numI, fun n _ => (congrFun hSm n).symm, V.room⟩ V2.room7F V2.n4 Ex
      (fa a).2 h1 h2 (fun q hq => (z1 q hq).2) (fun q hq => (z2 q hq).2) Mt
      (hR Xp _ _ PX F₁ l1) (hR Xp _ _ PX F₂ l2) hcells _
  exact key _ (tb3_eq _ A.hg) _ hc he7

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.rows_atF
