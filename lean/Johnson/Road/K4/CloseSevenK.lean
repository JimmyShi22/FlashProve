-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseSevenK.lean: Johnson/Road/K4/CloseSeven.lean's `Plan4L.seven_of_yes` WITH NINE
OF ITS PREMISES CONCLUDED: the six facts on what was heard (`Plan4L.heard_K`, HeardK.lean) and the
three ties of the masks (`masks_K`, MasksK.lean). A record, a definition and one theorem. Glue: no
new argument, no count.

  `Plan4L.ValueIs QL par hS`: the choices of the value's letters at a place: nT, nI, numT, two
  values of numI, two bounds, the table of scales, L0.
  `Plan4L.SevenAt`: the seven parts sq bat led terms gated hot stack of `Plan4.clK` at `Plan4.yK`,
  as one sentence.
  `Plan4L.seven_at`: `SevenAt` at a yes, under what the row opens.

Limits. PREMISES THAT STAY: the seat's two laws at the record in front · the ledger in front has
arrays of the right sizes, and its next free slot is the value's n0 · `ValueIs` · `PubLines`,
`LookLines`, the rotary tables' fit · zOf, kTg at the first statement; the lookup's end form names
filled slots alone · OF THE WORLD: the statement's mask row is the value's at part w; matrices Mt
whose reads are true in the worlds of the two ledgers behind the runs, and whose cells are the
message's · THE FIVE OWN ROWS u1 u2 u5 u6 u4. `Plan4.Meets` and pc.ds = dsLater par. Nothing shows
that these can be met together.
-/
import Johnson.Road.K4.CloseSeven
import Johnson.Road.K4.MasksK
import Johnson.Road.K4.HeardK

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
open OnBytes.Desc.First.P1 (gl)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **The choices of the value's letters at a place**: numbers alone, and the table of scales. -/
structure Plan4L.ValueIs (QL : Plan4L Cb.Gl.E Mm X) (par : Par)
    (hS : OnBytes.Model.Layer.Shape) : Prop where
  nT : QL.nT = OnBytes.Model.Layer.nEndT par.P.y
  nI : QL.nI = 2 + (1 + par.P.y.LamM) + (par.hp.NCL - (if (par.g == 0) = true then 1 else 0))
  numT : ∀ q, QL.numT q = numA QL.D q
  hEnd : QL.D.nNu + QL.D.ne + QL.D.ne * QL.D.nx ≤ QL.nT
  room : QL.slots.f7 ≤ QL.ns
  iA : QL.numI (Sum.inl (Sum.inl ())) = 0
  iB : QL.numI (Sum.inr (Sum.inl ())) = 2 + QL.D.ne
  scl : scl = sclOf hS par.P.sc par.g par.P.y.Lam
  L0 : par.g * par.P.y.Lam = QL.L0

/-- The seven parts, as one sentence. -/
def Plan4L.SevenAt (A : QL.plan.Meets par hS pcl) (Ex : ExtSpec)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par)
    (fa : T × Fr.E.Str → X × Ex.Str) (part : Wt → Mm) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (w : Wt) : Prop :=
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
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))

/-- **The seven parts at a yes, under what the row opens.** -/
theorem Plan4L.seven_at (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
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
    (lw : ℕ → LW Cb.Gl.E) (hz0 : QL.plan.full.zOf (fa a).1 = zAt fo)
    (hk0 : QL.plan.full.kTg (fa a).1 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QL.plan.full.D QL.plan.full.tb
        hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QL.plan.full.D (cellsAt par.P.y Mt) =
      QL.plan.full.rd (QL.plan.full.msg (part w)))
    (V : Plan4L.ValueIs QL par hS) (h0 : QL.n0 = (L.fork a.1).next)
    (hSm : Sm.mask w = QL.plan.maskAt (part w))
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
    Plan4L.SevenAt A Ex hds fa part a τ w := by
  obtain ⟨hinv, hscl, hvy, hL0, Nw, hsB⟩ :=
    Plan4L.heard_K A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, Ld⟩ := own_led7 hF Y.hears A.hg
  obtain ⟨Mk, mA, mB⟩ := masks_K QL (P := { par.P with tokv := L.tokv a.1 }) A.hy A.hrd A.Z A.hl
    A.hn hF Y.hears A.hg Ld h0 V.nT V.nI V.numT V.hEnd V.room V.iA V.iB (A.lamM (L.tokv a.1))
    (part w)
    (lateAt QL.plan.full (lateOf (roomK QL.plan par hS))
      (fmOf QL.plan.full (ztS QL.plan.full) (par.P.y.lPd - par.P.y.ls) par.P.y.ls par.P.y.ls)
      (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w))
    (readsAt (lateOf (roomK QL.plan par hS)) Sum.inl)
    (readsT (lateOf (roomK QL.plan par hS)) fun x => Sum.inr (Sum.inl x))
    (gReadsAt (lateOf (roomK QL.plan par hS)) fun x => Sum.inr (Sum.inr x))
  rw [← hSm] at Mk mA mB
  exact Plan4L.seven_of_yes A L Sm Lt Ex hds fa part a τ Y w hB hL hF B K Rp hinv hscl hvy hL0 Nw
    hsB lw hz0 hk0 hfil Mt hR hcells Mk mA mB u1 u2 u5 u6 u4

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.seven_at
