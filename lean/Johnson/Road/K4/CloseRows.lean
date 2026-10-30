-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/CloseRows.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN A GROUP THAT IS NOT
THE FIRST, AND UNDER WHAT K4's ROW OPENS: THE FIVE OWN ROWS AND THE PART merge OF THE LIBRARY's
LEDGER (`RowsSay`, Johnson/Road/K4/SixK.lean) AT THE CHAIN's LAST STATEMENT `Plan4.eK` AND AT THE
ENTRIES `Plan4.yK`. A record and one theorem. Glue: `Plan4L.six_led` laid over `Plan4.atYes`
(ClaimsYes.lean), `pubAtMore_of_led` (PubAtMore.lean), `forms_of_behind` (CloseBehind.lean),
`Plan4L.heard_K` (HeardK.lean). No draw, no count.

  `Plan4L.ValueMore QL`: three choices more of the value's letters, beside `ValueIs`
  (CloseSevenK.lean): numI is `num4` at the value's numbering of the weight claims; that numbering
  gives `numK`'s numbers; there is room for the merge's own slots.
  `Plan4L.rows_at`: `RowsSay` at a yes, under what the row opens.

Limits. PREMISES THAT STAY: the seat's two laws · the ledger in front has arrays of the right sizes
and its next free slot is the value's n0 · `ValueIs`, `ValueMore` · `PubLines`, `LookLines`, the
rotary tables' fit · zOf, kTg, kIncS at the first statement; the lookup's end form: filled slots
alone, no entry, slots below ns + 1 · the statement's mask row is the value's at part w · matrices
Mt whose reads are true in the worlds of the ledgers behind the runs, and whose cells are the
message's. `Plan4.Meets` and pc.ds = dsLater par. Nothing shows that these can be met together.

-/
import Johnson.Road.K4.SixK
import Johnson.Road.K4.CloseSevenK

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
open OnBytes.Desc.First.P1 (gl)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open VerifiableInference.Desc.Plain.K04 (Sem Letters Behind)
open Inst.Model (Scl)
open Inst.Model.FFSeg (LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {QL : Plan4L Cb.Gl.E Mm X} {par : Par}
  {hS : OnBytes.Model.Layer.Shape} {pcl : List (List String)}

/-- **Three choices more of the value's letters.** -/
structure Plan4L.ValueMore (QL : Plan4L Cb.Gl.E Mm X) : Prop where
  numI : QL.numI = num4 QL.D QL.num
  n4 : ∀ q, num4 QL.plan.full.D QL.plan.full.num q =
    num4 QL.plan.full.D (numK QL.plan.full.D) q
  room7 : QL.slots.f7 + 1 + (2 * QL.plan.kW + 1) ≤ QL.ns

/-- **The five own rows and merge at a yes, under what the row opens.** -/
theorem Plan4L.rows_at (A : QL.plan.Meets par hS pcl) (L : Seat T) (Sm : Sem Wt)
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
    (hkS : ∀ s, QL.plan.kIncS (fa a).1 s = kIncAt fo (L.fork a.1) s)
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) (he : fo.cEnd.ents = #[])
    (hsl : ∀ y ∈ fo.cEnd.slots.toList, y.1 < QL.ns + 1) (Mt : Mats Cb.Gl.E)
    (hR : ∀ (X : Rows.Pub34 Cb.Gl.E) (G2 : Fork) (t4 : Tape),
      PubAt X { par.P with tokv := L.tokv a.1 } par.hp fo o G2 t4 QL.plan.full.D QL.plan.full.tb
        hS →
      ∀ Fl, Fo.Later G Fl → X.ReadsTrue (Fl.worldOf gl (Sm.mask w) (Sm.entryT o w)) Mt)
    (hcells : cellsOf QL.plan.full.D (cellsAt par.P.y Mt) =
      QL.plan.full.rd (QL.plan.full.msg (part w)))
    (V : Plan4L.ValueIs QL par hS) (V2 : Plan4L.ValueMore QL)
    (h0 : QL.n0 = (L.fork a.1).next) (hSm : Sm.mask w = QL.plan.maskAt (part w)) :
    RowsSay QL.plan.full (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)
      (lateAt QL.plan.full (lateOf (roomK QL.plan par hS))
        (fmOf QL.plan.full (ztS QL.plan.full) (par.P.y.lPd - par.P.y.ls) par.P.y.ls par.P.y.ls)
        (Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ) (part w)) := by
  obtain ⟨hinv, hscl, hvy, _, _, _⟩ :=
    Plan4L.heard_K A Y.hears hF (small_of_all _ _ _ Y.small) V.scl V.L0
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, g7, Ld, I, hc⟩ :=
    Plan4.atYes A (numsK QL.plan.full) L hds a τ Y (fa a).1 hF B.S B.hs B.hg B.hrd B.hmats B.hρ
      B.hc B.hN B.hfl K.hsx K.hsy K.hzk K.he B.hs0 K.hpt B.Zw B.hsL B.hlw B.h4 Rp B.htm B.hNM
      B.hpad hinv hscl hvy (A.lamM (L.tokv a.1)) gl_half (nums4_numsK QL.plan.full) lw hz0 hk0
      hfil
  obtain ⟨Xp, PX, Xrd, Xe⟩ := pubAtMore_of_led Y.hears Ld B K Rp hinv
  obtain ⟨_, ⟨fs₁, F₁, fs₂, F₂, h1, h2, z1, z2⟩, _⟩ :=
    forms_of_behind L Sm Lt par pc a τ o G w hL hB
  have l1 : Fo.Later G F₁ := later_fo (formsFrontWith_later h1)
  have l2 : Fo.Later G F₂ := l1.trans (later_fo (formsBack_later h2))
  have he7 : Plan4.eK A (numsK QL.plan.full) Ex hds (fa a) τ = _ :=
    Plan4.val_of_claims A (numsK QL.plan.full) Ex (L.tokv a.1) hds τ (fa a) _ hc
  rw [he7]
  exact Plan4L.six_led A (L.tokv a.1) hF Y.hears Ld _ _ g7 I hc.c4 (fun _ => rfl) hz0 hk0 hkS hfil
    he hsl Xp PX Xrd Xe hvy hscl hinv lw (part w) (Sm.mask w) (Sm.entryT o w)
    ⟨h0, V.nT, V.nI, V2.numI, fun n _ => (congrFun hSm n).symm, V.room⟩ V2.room7 V2.n4 Ex (fa a).2
    h1 h2 (fun q hq => (z1 q hq).2) (fun q hq => (z2 q hq).2) Mt (hR Xp _ _ PX F₁ l1)
    (hR Xp _ _ PX F₂ l2) hcells _

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4L.rows_at
