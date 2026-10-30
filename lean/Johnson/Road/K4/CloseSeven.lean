-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseSeven.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN A GROUP THAT IS NOT
THE FIRST, AND UNDER WHAT K4's ROW OPENS: SEVEN OF THE EIGHT PARTS OF THE LIBRARY's LEDGER (sq, bat,
led, terms, gated, hot, stack of `Plan4.clK`, Johnson/Road/K4/CloseLater.lean), AT THE VALUE WITH
ITS SLOTS AND ORDERS LAID (`Plan4L`, ValueSlots.lean), THE NUMBERING `numsK` AND zt := `ztS`. One
theorem. Glue, and long: it lays together `Plan4.atYes` (ClaimsYes.lean), `pubAt_of_led`
(PubAt.lean), `outs_of_led` (StageOutsAll.lean), `forms_of_behind` (CloseBehind.lean),
`sevenSizes_of_meets`, `numTies_K`, `seven_of_sizes` and `side_mem`. No draw, no count.

  `Plan4L.seven_of_yes`: the seven `Ledger.Holds`, as one conjunction.

Limits. PREMISES THAT STAY: the seat's two laws at the record in front · the ledger in front has
arrays of the right sizes · `PubLines`, `LookLines`, the rotary tables' fit, the inverse of the
terms' coefficient · the table of scales is the shape's; o.v.y is the plan's layout; L0;
`NormWords`; the place of the second side's slot · zOf, kTg at the first statement; the lookup's end
form names filled slots alone · OF THE WORLD: matrices Mt whose reads are true in the worlds of the
two ledgers behind the runs, and whose cells are the message's · `MaskTies`, and the two sides'
masks · THE FIVE OWN ROWS u1 u2 u5 u6 u4. `Plan4.Meets` and pc.ds = dsLater par. Nothing shows that
these can be met together.
-/
import Johnson.Road.K4.CloseLater
import Johnson.Road.K4.CloseBehind
import Johnson.Road.K4.ClaimsYes
import Johnson.Road.K4.PubAt
import Johnson.Road.K4.StageOutsAll
import Johnson.Road.K4.SevenExtras
import Johnson.Road.K4.MeetsCovers
import Johnson.Road.K4.NumTiesK
import Johnson.Road.K4.OutTiesK
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
open OnBytes.Desc.First.K4 (Par Seat later_fo formsFrontWith_later formsBack_later)
open OnBytes.Desc.First.P1 (gl addsOf drawnOf)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW zpos)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **Seven parts of the ledger, at a yes, under what the row opens.** -/
theorem Plan4L.seven_of_yes (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
    (Lt : Letters T Wt Fr) (Ex : ExtSpec) {pc : Piece (ckP .two) Fr T Cl Wt}
    (hds : pc.ds = dsLater par) (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm)
    (a : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (w : Wt)
    (hB : Behind L Sm Lt par (behindOf L pc a τ o G) w) (hL : SeatOk L a.1)
    (hF : PscRun.Sized (L.fork a.1)) {s : WsShape} {lk : ℕ} {s0 : OnBytes.Model.Forest.Shape}
    {tl : HTailF2}
    (B : PubLines { par.P with tokv := L.tokv a.1 } par.g hS pcl QL.plan.full.D QL.plan.full.tb s
      lk s0 tl)
    (K : LookLines { par.P with tokv := L.tokv a.1 } fo s0)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt }
        QL.plan.full.D QL.plan.full.tb (par.g * par.P.y.Lam) lam)
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam) (hvy : o.v.y = par.P.y)
    (hL0 : o.v.g * o.v.y.Lam = QL.plan.full.ip.L0) (Nw : NormWords o.v QL.plan.full.D)
    (hsB : o.K.sB0 = o.K.sA0 + (1 + (1 + par.P.y.LamM)))
    (lw : ℕ → LW Cb.Gl.E)
    (hz0 : QL.plan.full.zOf (fa a).1 = zAt fo)
    (hk0 : QL.plan.full.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QL.plan.full.D QL.plan.full.tb
        hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QL.plan.full.D (cellsAt par.P.y Mt) =
      QL.plan.full.rd (QL.plan.full.msg (part w)))
    (Mk : MaskTies (Sm.mask w) o QL.plan.full.D
      (namesAt QL.plan.full.nr (readsAt (lateOf (roomK QL.plan par hS)) Sum.inl))
      (namesT QL.plan.full.tp (readsT (lateOf (roomK QL.plan par hS))
        fun x => Sum.inr (Sum.inl x)))
      (gNamesAt QL.plan.full.fp (gReadsAt (lateOf (roomK QL.plan par hS))
        fun x => Sum.inr (Sum.inr x)))
      (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)))
    (mA : QL.plan.full.msg (part w) (QL.plan.full.ip.cI (.inl (.inl ()))) = Sm.mask w o.K.sA0)
    (mB : QL.plan.full.msg (part w) (QL.plan.full.ip.cI (.inr (.inl ()))) = Sm.mask w o.K.sB0)
    (u1 : Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (u1At QL.plan.full.nr
        ((tailF QL.plan.full).b1 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0)
    (u2 : Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (u2At QL.plan.full.nr
        ((tailF QL.plan.full).b2 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0)
    (u5 : Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (prodU QL.plan.full.fp.gp
        ((tailF QL.plan.full).b5 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0)
    (u6 : Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (prodU QL.plan.full.fp.rt.L
        ((tailF QL.plan.full).b6 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2) = 0)
    (u4 : Blocks.Form.val (QL.plan.yK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
      (upForm (J₂ := J3 (roomK QL.plan par hS)) (Cb.Sub.formU QL.plan.full.ip.inn.toSum.T.par
        (fun _ b _ _ => PEmpty.elim b)
        ((tailF QL.plan.full).b4 (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).2)) = 0) :
    Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).sq
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) ∧
      Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).bat
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) ∧
      Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).led
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) ∧
      Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).terms
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) ∧
      Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).gated
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) ∧
      Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).hot
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) ∧
      Ledger.Holds (QL.plan.clK par hS (ztS QL.plan.full)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ)).stack
        (QL.plan.yK par hS (ztS QL.plan.full)
          (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, g7, Ld, I, hc⟩ :=
    Plan4.atYes A (numsK QL.plan.full) L hds a τ Y (fa a).1 hF B.S B.hs B.hg B.hrd B.hmats B.hρ
      B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM
      B.hpad hinv hscl hvy (A.lamM (L.tokv a.1)) gl_half (nums4_numsK QL.plan.full) lw hz0 hk0
      hfil
  obtain ⟨X, PX⟩ := pubAt_of_led Y.hears Ld B K Rp hinv
  have OT := outTies_K A (L.tokv a.1) Ld.c4
  obtain ⟨_, ⟨fs₁, F₁, fs₂, F₂, h1, h2, z1, z2⟩, _⟩ :=
    forms_of_behind L Sm Lt par pc a τ o G w hL hB
  have l1 : Fo.Later G F₁ := later_fo (formsFrontWith_later h1)
  have l2 : Fo.Later G F₂ := l1.trans (later_fo (formsBack_later h2))
  have hzp : ∀ j, j < QL.plan.full.D.lT →
      zpos QL.plan.full.D (zAt fo) j = gl.val (H1.ztF.getD j zeroE) := by
    intro j hj
    have q := zpos_pub X (by rw [PX.D, PX.v, hvy]; exact OT.lt) j (by rw [PX.D]; exact hj)
    rw [PX.D, PX.H, PX.fo, Ld.ztF] at q
    exact q
  obtain ⟨O1, O2, O3, O4, O5, O6, _⟩ := outs_of_led QL.plan.full
    (Plan4.tailMK A (numsK QL.plan.full)) Ld OT (Plan4.nzAt A (L.tokv a.1) hds τ _)
    ((fa a).1, ptOf QL.plan (tapeAt par pc τ)) g7 I (fun _ => rfl) hz0 hzp
  have he : Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ = _ :=
    Plan4.val_of_claims A (numsK QL.plan.full) Ex (L.tokv a.1) hds τ (fa a) _ hc
  exact seven_of_sizes QL.plan.full (Plan4.tailMK A (numsK QL.plan.full))
    (par.P.y.lPd - par.P.y.ls) (hS.d / par.P.y.S2) par.P.y.ls (noRest3 QL.plan.full) (part w)
    (sevenSizes_of_meets A (L.tokv a.1)) hF A.hg Ld _ _ _ _ he O1 O2 O3 O4 O5 O6
    (numTies_K QL.plan.full _ _ (A.lamM (L.tokv a.1))) hc.c4 X PX.ρ PX.H PX.v PX.rs PX.hd PX.hd2
    PX.lam PX.sA PX.sB PX.om PX.sh (Sm.mask w) (Sm.entryT o w) l1 l2 Mt (hR X _ _ PX F₁ l1)
    (hR X _ _ PX F₂ l2) (by rw [PX.h, PX.v]; exact hscl) hvy PX.D PX.tb
    (by rw [PX.c]; exact hL0) Nw hsB (by rw [PX.v, hvy]; exact hcells) (fun _ => rfl)
    (by rw [he, PX.fo]; exact hz0) (by rw [he, PX.fo]; exact hz0) Mk mA mB h1
    (fun f hf => (z1 f hf).2)
    (fun f hf => (z2 f (side_mem X PX.sA PX.sB PX.fin h2 f hf)).2) u1 u2 u5 u6 u4

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.seven_of_yes
