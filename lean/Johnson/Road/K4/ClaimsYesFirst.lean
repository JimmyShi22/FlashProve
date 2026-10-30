-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/Road/K4/ClaimsYesFirst.lean: THE FIRST GROUP's TWIN OF Johnson/Road/K4/ClaimsYes.lean: AT A
YES OF THE PIECE THAT HOLDS K4's BLOCK, IN THE FIRST GROUP: ONE RECORD FROM WHICH THE PROOFS ON THE
FIRST CHAIN's LAST STATEMENT CAN START: the hearing's ledgers and tapes, seven targets that are the
records', and `TailH.Claims` at the states chosen from the front on. A definition and two theorems.
Glue: `own_ledG` (Johnson/Road/K4/OwnLedgersG.lean), `claims_of_ledF`
(Johnson/Road/K4/ClaimsHeardFirst.lean) and `first4_fullF` (Johnson/Road/K4/Claim4FullFirst.lean).
No draw, no count.

  `Plan4F.AtYesF A N L hds a τ fo o G x0`: there are LedG's letters and g7 with: `LedG` at the
    hearing's return on the tape `tapeAt par pc τ` · `TgRecF g7` (each target is the record's) ·
    `ClaimsAtF` (Johnson/Road/K4/CloseYesFirst.lean) at a7 := `addsOf (tailMKF A N) … g7`, on the
    tape behind the three points' rounds.
  `Plan4F.atYesF`: `AtYesF` at every `Yes`, under the premises listed below.
  `Plan4F.claims_of_atYesF`: `AtYesF` gives `ClaimsAtF` at some a7.

By hand: `LedG` and `claims_of_ledF` name the tape `t0.drop (k0 g)`, `ClaimsAtF` names three single
drops (`tb3`): the two are one tape in the first group (`tb3_eq`, CloseValFirst.lean).

Limits. PREMISES OF `atYesF`, ALL UNPAID HERE: those of `Plan4.atYes` (ClaimsYes.lean), to the
letter, at the first group's value: the ledger in front has arrays of the right sizes · the premises
of `pub34_of_hear_run` (Johnson/Road/K4/PubOfHearTied.lean) · the table of scales is the shape's ·
the heard environment's layout is the plan's (hvy) · LamM = ne · the reading of 1/2 · `Nums4` of the
numbering's fourth member · the letters zOf and kTg at the first statement · the lookup's end form
names filled slots alone. `Plan4F.MeetsF` and pc.ds = dsFirst par. By the head of
Johnson/Road/Rows/LayerEnds34.lean the premise hfl fails at the small shipped example: there
`atYesF` says nothing. Nothing on the embedding's claim or on the two further points.
-/
import Johnson.Road.K4.CloseYesFirst
import Johnson.Road.K4.ClaimsHeardFirst
import Johnson.Road.K4.Claim4FullFirst

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace OnBytes.Road.K4
open Iop Cb Cb.Pv.Att Cb.Pv.Lay Cb.Pv.Lay.At
open OnBytes OnBytes.Model OnBytes.K.Kc OnBytes.Flat OnBytes.Maker
open OnBytes.Model.Layer (Heard Pub Own layout scalesHeld readsOf HPlan2)
open OnBytes.Desc.First.K4 (Par Seat k0)
open OnBytes.Desc.First.P1 (gl NzT TailNums Tg7 addsOf tailT)
open _root_.Run (ckP)
open VerifiableInference.Desc.Sound (Frame Piece)
open Inst.Model (Scl)
open Inst.Model.FFSeg (used lut LW)

variable [scl : Scl] {Mm X T Wt Cl : Type} {Fr : Frame} {Q : Plan4F Cb.Gl.E Mm X} {par : Par}
  {hS : Layer.Shape} {pcl : List (List String)}

/-- **What the proofs on the first chain's last statement start from, at a yes.** -/
def Plan4F.AtYesF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail) (L : Seat T)
    {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par) (a : T × Fr.E.Str)
    (τ : Tr (uLT (ckP .two) pc.ds)) (fo : Forest.Heard) (o : Own) (G : Fork) (x0 : X) : Prop :=
  ∃ (H1 : OnBytes.Model.Layer.Heard) (hd2 : Level) (tT : Tsc)
    (F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 : Fork) (u5 : Tape) (g7 : Tg7),
    LedG { par.P with tokv := L.tokv a.1 } par.hp par.g fo o (L.fork a.1) G (tapeAt par pc τ) []
      H1 hd2 tT F4 F7 F8 G1 G1' G2 G3 G3' G4 G5 u5 ∧
    TgRecF g7 { par.P with tokv := L.tokv a.1 } par.hp par.g o (tapeAt par pc τ) H1 tT F4 G2 G3
      G3' ∧
    Plan4F.ClaimsAtF A N (L.tokv a.1) hds τ x0
      (addsOf (Plan4F.tailMKF A N) (ksOf { par.P with tokv := L.tokv a.1 } par.hp)
        (tb3 (tapeAt par pc τ)) (Plan4F.nzAtF A (L.tokv a.1) hds τ _)
        (x3Of Q x0 (tapeAt par pc τ)) g7)

/-- `AtYesF` gives `ClaimsAtF` at some states and targets. -/
theorem Plan4F.claims_of_atYesF {A : Q.MeetsF par hS pcl}
    {N : TailNums Q.fullF.ownF.toOwn.tail} {L : Seat T} {pc : Piece (ckP .two) Fr T Cl Wt}
    {hds : pc.ds = dsFirst par} {a : T × Fr.E.Str} {τ : Tr (uLT (ckP .two) pc.ds)}
    {fo : Forest.Heard} {o : Own} {G : Fork} {x0 : X}
    (h : Plan4F.AtYesF A N L hds a τ fo o G x0) :
    ∃ a7, Plan4F.ClaimsAtF A N (L.tokv a.1) hds τ x0 a7 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hc⟩ := h
  exact ⟨_, hc⟩

/-- **`AtYesF` at every yes.** -/
theorem Plan4F.atYesF (A : Q.MeetsF par hS pcl) (N : TailNums Q.fullF.ownF.toOwn.tail)
    (L : Seat T) {pc : Piece (ckP .two) Fr T Cl Wt} (hds : pc.ds = dsFirst par)
    (a : T × Fr.E.Str) (τ : Tr (uLT (ckP .two) pc.ds)) {fo : Forest.Heard} {o : Own} {G : Fork}
    (Y : Yes L par pc a τ fo o G) (x0 : X) (hF : PscRun.Sized (L.fork a.1))
    {s : WsShape} {lk : ℕ} {s0 : Forest.Shape} {tl : HTailF2}
    (S : Switches hS) (hs : scalesHeld hS par.P.sc = .ok ())
    (hg : par.g < par.P.y.NGr) (hrd : readsOf par.P.y = .ok par.P.rd)
    (hmats : ((par.P.tails.getD par.g {}).mats.map fun M => (M.m, M.k)) = matsR par.P.y par.g)
    (hρ : Numerals Reading.gl) (hc : Q.fullF.D.cap = hS.lidb) (hN : LinesAre par.P.y)
    (hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used Q.fullF.D k))
    (hsx : fo.zx.size = par.P.y.fo.dT) (hsy : fo.zy.size = par.P.y.fo.rK)
    (hzk : fo.zk = (Array.range par.P.y.fo.NC).map fun q =>
      fo.zy.extract (par.P.y.fo.rK - par.P.y.fo.iota.getD q 0) fo.zy.size ++ fo.zx)
    (he : fo.e = (Array.range par.P.y.fo.NC).map (Forest.callWeight par.P.y.fo fo.zy))
    (hs0 : Forest.shape par.P.y.cl par.P.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (Zw : SizedW s Q.fullF.D.P) (hsL : s.L = hS.L) (hlw : wsLayOf s true lk = .ok par.P.wsLay)
    (h4 : hS.p4 = true)
    (Rp : ∀ (rt : Array E) (lam : ℕ), lam < par.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := par.P.wsLay, rope := par.P.rope, rs := o.K.rs, rt := rt } Q.fullF.D
        Q.fullF.tb (par.g * par.P.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR par.P.y par.g) (hNM : tl.NM = tl.mats.size)
    (hpad : ∀ k : Fin 8,
      Reading.gl.val (ofF ((par.P.y.cl.getD k.val {}).tauAt (par.P.y.cl.getD k.val {}).t0)) =
        (((lut Q.fullF.tb k).pad : ℤ) : Cb.Gl.E))
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam) (hvy : o.v.y = par.P.y)
    (hLam : par.P.y.LamM = Q.fullF.D.ne) (hhalf : gl.val (invE (ofNat 2)) * 2 = 1)
    (hN4 : Nums4 Q.fullF.toFullPar (Plan4F.tailMKF A N).w4.num) (w : ℕ → LW Cb.Gl.E)
    (hz0 : Q.fullF.zOf x0 = zAt fo) (hk0 : Q.fullF.kTg x0 = kTgAt fo (L.fork a.1))
    (hfil : Fo.FilledA (L.fork a.1) fo.cEnd) :
    Plan4F.AtYesF A N L hds a τ fo o G x0 := by
  obtain ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, Ld⟩ := own_ledG hF Y.hears
  obtain ⟨g7, I⟩ := tg_existsF { par.P with tokv := L.tokv a.1 } par.hp par.g o (tapeAt par pc τ)
    H1 tT F4 G2 G3 G3'
  refine ⟨H1, hd2, tT, F4, F7, F8, G1, G1', G2, G3, G3', G4, G5, u5, g7, Ld, I, ?_⟩
  have key : ∀ (tR : Tape), (tapeAt par pc τ).drop (k0 par.g) = tR →
      ∀ nz : NzT Q.fullF.ownF.toOwn.tail (ksOf { par.P with tokv := L.tokv a.1 } par.hp) tR,
      (tailT (Plan4F.tailMKF A N) (ksOf { par.P with tokv := L.tokv a.1 } par.hp) tR nz
        (addsOf (Plan4F.tailMKF A N) (ksOf { par.P with tokv := L.tokv a.1 } par.hp) tR nz
          (x3Of Q x0 (tapeAt par pc τ)) g7)).Claims (x3Of Q x0 (tapeAt par pc τ)) := by
    intro tR e
    subst e
    intro nz
    exact claims_of_ledF (Plan4F.tailMKF A N) Ld nz _ g7 hF A.dimIs A.hg hLam hhalf hN4 I
      (first4_fullF Q.fullF (Plan4F.tailMKF A N) Y.hears Ld A.hy S hs hg hrd hmats hρ A.Z hc hN
        hfl hsx hsy hzk he hs0 hpt Zw hsL hlw h4 Rp htm hNM hpad hinv hscl A.dimIs.lt hvy w nz _
        g7 I.t3 I.t4 hz0 hk0 hfil)
  exact key _ (tb3_eq _ A.hg) _

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.Plan4F.claims_of_atYesF
#print axioms OnBytes.Road.K4.Plan4F.atYesF
