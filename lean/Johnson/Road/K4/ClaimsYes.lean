-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/ClaimsYes.lean: AT A YES OF THE PIECE THAT HOLDS K4's BLOCK, IN A GROUP THAT IS NOT
THE FIRST: ONE RECORD FROM WHICH THE PROOFS OF ALL FIELDS OF `Plan4.Pays`
(Johnson/Road/K4/CloseLater.lean) CAN START: the hearing's ledgers and tapes, seven targets that are
the records', and `TailH.Claims` at the states chosen from the front on. A definition and two
theorems. Glue: `own_led7`, `claims_of_led` and `first4_full` (Claim4Full.lean). No draw, no
count.

  `Plan4.AtYes A N L hds a τ fo o G x0`: there are Led7's letters and g7 with: `Led7` at the
    hearing's return on the tape `tapeAt par pc τ` · `TgRec g7` (each target is the record's) ·
    `ClaimsAt` at a7 := `addsOf (tailMK A N) … g7`.
  `Plan4.atYes`: `AtYes` at every `Yes`, under the premises listed below.
  `Plan4.claims_of_atYes`: `AtYes` gives the field `claims` of `Plan4.Pays`.

Limits. PREMISES OF `atYes`, ALL UNPAID HERE: the ledger in front has arrays of the right sizes ·
the premises of `pub34_of_hear_run` (Johnson/Road/K4/PubOfHearTied.lean) to the letter, at the
place's record with the request's tokens laid: public lines of the plan; what the lookup heard
(five); the rotary tables' fit; that the terms' coefficient has an inverse · the table of scales is
the shape's · LamM = ne · the reading of 1/2 · `Nums4` of the numbering's fourth member · the
letters zOf and kTg at the first statement · the lookup's end form names filled slots alone.
`Plan4.Meets` and pc.ds = dsLater par. A group that is not the first.
-/
import Johnson.Road.K4.CloseYes
import Johnson.Road.K4.ClaimsHeard
import Johnson.Road.K4.Claim4Full

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Heard Pub Own layout scalesHeld readsOf HPlan2)
open OnBytes.Desc.First.K4 (Par Seat)
open OnBytes.Desc.First.P1 (gl TailNums Tg7 addsOf)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open Inst.Model (Scl)
open Inst.Model.FFSeg (used lut LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {Q : Plan4 Cb.Gl.E Mm X} {par : Par}
  {hS : Layer.Shape} {pcl : List (List String)}

/-- **What the proofs of all fields start from, at a yes.** -/
def Plan4.AtYes (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) (L : Seat T)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (fo : Forest.Heard) (o : Own) (G : Fork) (x0 : X) : Prop :=
  ∃ (H1 : OnBytes.Model.Layer.Heard) (hd2 : Level) (tT : Tsc)
    (F4 F7 F8 G1 G1' G2 G3 G3' G4 : Fork) (g7 : Tg7),
    Led7 { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G (tapeAt par pc τ) []
      H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 ∧
    TgRec g7 { par.P with tokv := L.tokv a.1 } par.hp o (tapeAt par pc τ) H1 tT F4 G2 G3 G3' ∧
    Plan4.ClaimsAt A N (L.tokv a.1) hds τ x0
      (addsOf (Plan4.tailMK A N) (ksOf { par.P with tokv := L.tokv a.1 } par.hp)
        ((tapeAt par pc τ).drop 1) (Plan4.nzAt A (L.tokv a.1) hds τ _)
        (x0, ptOf Q (tapeAt par pc τ)) g7)

/-- `AtYes` gives the field `claims`. -/
theorem Plan4.claims_of_atYes {A : Q.Meets par hS pcl} {N : TailNums Q.full.own.toOwn.tail}
    {L : Seat T} {pc : Piece (ckP .two) Fr T Cl Wt} {hds : pc.ds = dsLater par}
    {a : T × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)} {fo : Forest.Heard} {o : Own} {G : Fork}
    {x0 : X} (h : Plan4.AtYes A N L hds a τ fo o G x0) :
    ∃ a7, Plan4.ClaimsAt A N (L.tokv a.1) hds τ x0 a7 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := h
  exact ⟨_, hc⟩

/-- **`AtYes` at every yes.** -/
theorem Plan4.atYes (A : Q.Meets par hS pcl) (N : TailNums Q.full.own.toOwn.tail) (L : Seat T)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsLater par) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (x0 : X) (hF : PscRun.Sized (L.fork a.1))
    {s : WsShape} {lk : ℕ} {s0 : Forest.Shape} {tl : HTailF2}
    (S : Switches hS) (hs : scalesHeld hS par.P.sc = .ok ())
    (hg : par.g < par.P.y.NGr) (hrd : readsOf par.P.y = .ok par.P.rd)
    (hmats : ((par.P.tails.getD par.g {}).mats.map fun M => (M.m, M.k)) = matsR par.P.y par.g)
    (hρ : Numerals Reading.gl) (hc : Q.full.D.cap = hS.lidb) (hN : LinesAre par.P.y)
    (hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used Q.full.D k))
    (hsx : fo.zx.size = par.P.y.fo.dT) (hsy : fo.zy.size = par.P.y.fo.rK)
    (hzk : fo.zk = (Array.range par.P.y.fo.NC).map fun q =>
      fo.zy.extract (par.P.y.fo.rK - par.P.y.fo.iota.getD q 0) fo.zy.size ++ fo.zx)
    (he : fo.e = (Array.range par.P.y.fo.NC).map (Forest.callWeight par.P.y.fo fo.zy))
    (hs0 : Forest.shape par.P.y.cl par.P.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (Zw : SizedW s Q.full.D.P) (hsL : s.L = hS.L) (hlw : wsLayOf s true lk = .ok par.P.wsLay)
    (h4 : hS.p4 = true)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt } Q.full.D
        Q.full.tb (par.g * par.P.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR par.P.y par.g) (hNM : tl.NM = tl.mats.size)
    (hpad : ∀ k : Fin 8,
      Reading.gl.val (ofF ((par.P.y.cl.getD k.val {}).tauAt (par.P.y.cl.getD k.val {}).t0)) =
        (((lut Q.full.tb k).pad : ℤ) : Cb.Gl.E))
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam) (hvy : o.v.y = par.P.y)
    (hLam : par.P.y.LamM = Q.full.D.ne) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hN4 : Nums4 Q.full (Plan4.tailMK A N).w4.num) (w : ℕ → LW Cb.Gl.E)
    (hz0 : Q.full.zOf x0 = zAt fo) (hk0 : Q.full.kTg x0 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) :
    Plan4.AtYes A N L hds a τ fo o G x0 := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, Ld⟩ := own_led7 hF Y.hears A.hg
  obtain ⟨g7, I⟩ := tg_exists { par.P with tokv := L.tokv a.1 } par.hp o (tapeAt par pc τ) H1 tT
    F4 G2 G3 G3'
  refine ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, g7, Ld, I, ?_⟩
  exact claims_of_led (Plan4.tailMK A N) Ld _ _ g7 hF A.dimIs A.hg hLam hhalf hN4 I
    (first4_full Q.full (Plan4.tailMK A N) Y.hears Ld A.hy S hs hg hrd hmats hρ A.Z hc hN hfl hsx
      hsy hzk he hs0 hpt Zw hsL hlw h4 Rp htm hNM hpad hinv hscl A.dimIs.lt hvy w _ _ g7 I.t3 I.t4
      hz0 hk0 hfil)

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4.claims_of_atYes
#print axioms OnBytes.Road.K4.Plan4.atYes
