-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseSevenFirst.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST
GROUP, AND UNDER WHAT K4's ROW OPENS: EIGHT OF THE NINE PARTS OF THE LIBRARY's LEDGER THAT
`Plan4F.PaysF` ASKS (sq, bat, led, terms, gated, hot, stack, emb of `Plan4F.clKF`,
Johnson/Road/K4/CloseFirst.lean), AT THE FIRST GROUP's VALUE WITH ITS SLOTS AND ORDERS LAID
(`Plan4LF.planF`, ValueSlotsFirst.lean), THE NUMBERING `numsKF` AND zt := `ztSF`. The twin of
Johnson/Road/K4/CloseSeven.lean. A definition and one theorem. Glue, and long: it lays together
`Plan4F.atYesF` (ClaimsYesFirst.lean), `pubAt_of_ledF` (PubAtFirst.lean), `outTies_KF`
(OutTiesKFirst.lean), `outs_of_ledF` (StageOutsAllFirst.lean), `forms_of_behind`
(CloseBehind.lean), `sevenSizesF_K` (SevenPaidFirst.lean), `numTiesF_K` (NumTiesKFirst.lean),
`eight_of_ledF` (SevenOfLedFirst.lean) and `side_mem` (SevenExtras.lean). No draw, no count.

  `Plan4LF.EightAt`: the eight parts of `clKF` at `yKF`, at the chain's last statement `eKF`, as one
    sentence.
  `Plan4LF.eight_of_yes`: `EightAt` at a yes, under what the row opens and the premises below.

What is other than in a later group. The record of calls and ledgers is `LedG`; the chain's value is
named on the tape behind three single drops (`tb3`), the lower files' statements on
t0.drop (k0 g): the two are one tape in the first group (`tb3_eq`), and the proof passes over that
equation once. One part more, emb, and for it one premise more, uE.

Limits. K04_law IS NOT PROVED BY THIS. The part merge is not spoken of. PREMISES THAT STAY: the
seat's two laws at the record in front · the ledger in front has arrays of the right sizes ·
`PubLines`, `LookLines`, the rotary tables' fit, the inverse of the terms' coefficient · the table
of scales is the shape's; o.v.y is the plan's layout; L0; `NormWords`; the place of the second
side's slot · zOf, kTg at the first statement; the lookup's end form names filled slots alone · OF
THE WORLD: matrices Mt whose reads are true in the worlds of the two ledgers behind the runs, and
whose cells are the message's · `MaskTies`, and the two sides' masks · THE FIVE OWN ROWS u1 u2 u5 u6
u4 · uE: THE LIBRARY's CLAIM ON THE STREAM THAT COMES IN (`embClaim`) IS WORTH 0 AT `yKF`: NOT
PAID HERE. `Plan4F.MeetsF` and pc.ds = dsFirst par. Nothing ties Q.tok to the seat's tokens.
Nothing shows that these can be met together.
-/
import Johnson.Road.K4.CloseFirst
import Johnson.Road.K4.CloseBehind
import Johnson.Road.K4.ClaimsYesFirst
import Johnson.Road.K4.PubAtFirst
import Johnson.Road.K4.StageOutsAllFirst
import Johnson.Road.K4.SevenExtras
import Johnson.Road.K4.SevenPaidFirst
import Johnson.Road.K4.NumTiesKFirst
import Johnson.Road.K4.OutTiesKFirst
import Johnson.Road.K4.ClaimsPaid
import Johnson.Desc.First.K4.LedgerKeeps

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
open OnBytes.Desc.First.P1 (gl addsOf drawnOf NzT tailT)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW zpos)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QF : Plan4LF Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- The eight parts sq bat led terms gated hot stack emb, as one sentence. -/
def Plan4LF.EightAt (A : QF.planF.MeetsF par hS pcl) (Ex : ExtSpec)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (w : Wt) : Prop :=
  Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).sq
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).bat
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).led
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).terms
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).gated
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).hot
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).stack
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)) ∧
    Ledger.Holds (QF.planF.clKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ)).emb
    (QF.planF.yKF par hS (ztSF QF.planF.fullF)
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w))

/-- **Eight parts of the first group's ledger, at a yes, under what the row opens** and the premises
that the head lists, the five own rows and the embedding's claim among them. -/
theorem Plan4LF.eight_of_yes (A : QF.planF.MeetsF par hS pcl) (L : Seat T) (Sm : Sem Wt)
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
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam) (hvy : o.v.y = par.P.y)
    (hL0 : o.v.g * o.v.y.Lam = QF.planF.fullF.ip.L0) (Nw : NormWords o.v QF.planF.fullF.D)
    (hsB : o.K.sB0 = o.K.sA0 + (1 + (1 + par.P.y.LamM)))
    (lw : ℕ → LW Cb.Gl.E)
    (hz0 : QF.planF.fullF.zOf (fa a).1 = zAt fo)
    (hk0 : QF.planF.fullF.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QF.planF.fullF.D
        QF.planF.fullF.tb hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QF.planF.fullF.D (cellsAt par.P.y Mt) =
      QF.planF.fullF.rd (QF.planF.fullF.msg (part w)))
    (Mk : MaskTies (Sm.mask w) o QF.planF.fullF.D
      (namesAt QF.planF.fullF.ofp.nr (readsAt (lateF (roomKF QF.planF par hS))
        fun x => Sum.inl (Sum.inl x)))
      (namesT QF.planF.fullF.tp (readsT (lateF (roomKF QF.planF par hS))
        fun x => Sum.inl (Sum.inr (Sum.inl x))))
      (gNamesAt QF.planF.fullF.fp (gReadsAt (lateF (roomKF QF.planF par hS))
        fun x => Sum.inl (Sum.inr (Sum.inr x))))
      (QF.planF.yKF par hS (ztSF QF.planF.fullF)
        (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) (part w)))
    (mA : QF.planF.fullF.msg (part w) (QF.planF.fullF.ip.cI (.inl (.inl ()))) =
      Sm.mask w o.K.sA0)
    (mB : QF.planF.fullF.msg (part w) (QF.planF.fullF.ip.cI (.inr (.inl ()))) =
      Sm.mask w o.K.sB0)
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
  have Sz := sevenSizesF_K A (L.tokv a.1)
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5', g7, Ld, I, hc⟩ :=
    Plan4F.atYesF A (numsKF QF.planF.fullF) L hds a τ Y (fa a).1 hF B.S B.hs B.hg B.hrd B.hmats
      B.hρ B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM
      B.hpad hinv hscl hvy Sz.hLM gl_half (nums4_num4K QF.planF.fullF.toFullPar) lw hz0 hk0 hfil
  obtain ⟨X, PX⟩ := pubAt_of_ledF Y.hears Ld B K Rp hinv
  have OT := outTies_KF A (L.tokv a.1) Ld.c4
  obtain ⟨_, ⟨fs₁, F₁, fs₂, F₂, h1, h2, z1, z2⟩, _⟩ :=
    forms_of_behind L Sm Lt par pc a τ o G w hL hB
  have l1 : Fo.Later G F₁ := later_fo (formsFrontWith_later h1)
  have l2 : Fo.Later G F₂ := l1.trans (later_fo (formsBack_later h2))
  have hzp : ∀ j, j < QF.planF.fullF.D.lT →
      zpos QF.planF.fullF.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE) := by
    intro j hj
    have q := zpos_pub X (by rw [PX.D, PX.v, hvy]; exact OT.lt) j (by rw [PX.D]; exact hj)
    rw [PX.D, PX.H, PX.fo, Ld.ztF] at q
    exact q
  have he : Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ = _ :=
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
      Plan4LF.EightAt A Ex hds fa part a τ w := by
    intro t' e nz hc' he'
    subst e
    obtain ⟨O1, O2, O3, O4, O5, O6, _⟩ := outs_of_ledF QF.planF.fullF
      (Plan4F.tailMKF A (numsKF QF.planF.fullF)) Ld OT nz
      (x3Of QF.planF (fa a).1 (tapeAt par pc τ)) g7 I (fun _ => rfl) hz0 hzp
    exact eight_of_ledF QF.planF.fullF (Plan4F.tailMKF A (numsKF QF.planF.fullF))
      (par.P.y.lPd - par.P.y.ls) (hS.d / par.P.y.S2) par.P.y.ls (noRest2 QF.planF.fullF) (part w)
      hF Ld nz _ (x3Of QF.planF (fa a).1 (tapeAt par pc τ))
      (Plan4F.eKF A (numsKF QF.planF.fullF) Ex hds (fa a) τ) he' O1 O2 O3 O4 O5 O6
      (numTiesF_K QF.planF.fullF _ _ Sz.hLM) hc'.c4 Sz.k1
      Sz.k2 Sz.k3 Sz.k4 Sz.k5 Sz.k6 Sz.e1 Sz.n5 Sz.e5 Sz.n6 Sz.e6 X PX.ρ PX.H PX.v PX.rs PX.hd
      PX.hd2 PX.lam PX.sA PX.sB PX.om PX.sh (Sm.mask w) (Sm.entryT o w) l1 l2 Mt
      (hR X _ _ PX F₁ l1) (hR X _ _ PX F₂ l2) (by rw [PX.h, PX.v]; exact hscl) hvy Sz.hls PX.D
      PX.tb (by rw [PX.c]; exact hL0) Nw Sz.Z Sz.hB Sz.h0 Sz.nl Sz.nd Sz.nB Sz.g1 Sz.gs1 Sz.gs2
      Sz.gfe Sz.hNS Sz.hNP Sz.hNO Sz.hEnd Sz.hNN Sz.hLM Sz.hNE hsB Sz.hla Sz.s1 Sz.s5 Sz.s6 Sz.s2
      Sz.w1 Sz.wP Sz.wS Sz.wn Sz.w5 Sz.w5s Sz.w6 (by rw [PX.v, hvy]; exact hcells)
      (fun _ => rfl) (by rw [he', PX.fo]; exact hz0) (by rw [he', PX.fo]; exact hz0) Mk mA mB h1
      (fun f hf => (z1 f hf).2)
      (fun f hf => (z2 f (side_mem X PX.sA PX.sB PX.fin h2 f hf)).2) u1 u2 u5 u6 u4 uE
  exact key _ (tb3_eq _ A.hg) _ hc he

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4LF.eight_of_yes
