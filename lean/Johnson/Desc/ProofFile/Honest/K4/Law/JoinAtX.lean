-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinAtX.lean: CONDITIONAL.

What is here. The hypothesis `JoinWorth` (StackStart.lean: the first pass of the batched sumcheck is
the lookup's join) AT ONE OF THE LIBRARY's PUBLIC STRUCTURES `Pub34`
(Johnson/Road/Rows/LayerEnds34.lean) whose two environments are the honest side's: at its hearing,
its second token sumcheck and its eight factors. It is JoinOne.lean's `joinWorth_one` with much laid
in that such a structure holds or gives. From PartsOfPub.lean: the factors' worth, the calls' points
and weights, the token point. From X's own fields: the verifier's list of claims, its end function's
return, the layout of the weights, the list of places, sizes. NOT ALL IS LAID IN: eight hypotheses
are asked here that X gives too (hd, hfew, hfw, hfef, hNE, hf, hzs, hB): JoinHeard.lean's
`joinWorth_tied` draws them from X. The lookup's own part stands in the library's own word for it:
`Pub34.Join`, the claim that the lookup reads.

  `joinWorth_x`   **the one statement**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X). NOTHING NEW IS SHOWN: calls and
rewritings. LEFT AS HYPOTHESES, ALL:
  on the structure X: it is given, at this reading; its two environments are the honest side's (Xp,
  Xc); its token point is the honest side's (hzt); its laying, its list of tables and its
  sub-proof's matrices, written in the plan's letters (hl, hf, hm); the honest named points are a
  part of its points (hpp); the table of scales is X's (hscl); what the library's law on the panel
  of queries and keys asks (`QKOk`);
  on the world W: its entries are the true ones at X's tables and the matrices Mm (hW); the claim
  that the lookup reads holds (`Join`); the slot of the claimed sum holds the honest job's total
  (hσ);
  on the honest input: `CellsAre`; `TensorIs` twice;
  at each token: `TokAll` (JoinPub.lean);
  public: twelve numbers (`GatedNums`); two equations and four inequalities between the weights'
  shape and the layer sub-proof's; the family "b-bits-0" is found (hB); the calls of the second walk
  are 0, 1, 2, 5 on the honest side (hTS); nl is at most two to lL; the token point's size (hzs);
  the layout has the two tensors of the gated products (hts, htu);
  returns: h, hJ, hstT; the first of the two weights reads 1 (hom).
No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinOne
import Johnson.Desc.ProofFile.Honest.K4.Law.PartsOfPub
import Johnson.Road.Rows.LayerEnds3Y

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World)
open OnBytes.Model.Layer (ClaimEnv stackEnd Ten layTables tableAsks funsOf placePanels)
open OnBytes.Road (pt padOf sclOf cellsAt cellsOf zOf Mats ts_eq admitted_of_layout)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Road.K4.C (sidesEnv stack_panels_at stackIs_of CellsAre PtsPart TensorIs GatedNums)
open Inst.Model (Scl)
open OnBytes.Desc.First.K4.Honest

/-- **`JoinWorth` AT A PUBLIC STRUCTURE.** CONDITIONAL: on every hypothesis named.
THE FULL SIZE ALONE (X). -/
theorem joinWorth_x [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} (h : stackData Q w p shownT = some SD) {J : Job}
    (hJ : jobTermsOn SD.S = some J) {rs : Array E}
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (Xp : X.p = sidesEnv SD.S shownT)
    (Xc : X.c = { SD.S.ce with rs := rs, rt := p.rt }) (hzt : SD.S.zt = X.H.ztF)
    (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm)
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r)
    (hf : funsOf Q.P.y X.H.fo X.pts X.r.2.1 = some X.funs) (hpp : PtsPart (namedPts Q p) X.pts)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hC : CellsAre Q w Mm) {tB0 : ℕ}
    (hB : SD.S.v.tabAt "b-bits-0" = some tB0) {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts)
    (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .sl ts)
    (Su : TensorIs Q w (cellsOf X.D (cellsAt SD.S.v.y Mm)) .up tu) (N : GatedNums Q X.D)
    (hnl : X.D.nl ≤ 2 ^ X.D.lL) (hd : X.s.d = SD.S.v.y.h.d) (hfew : X.s.fe = SD.S.v.y.h.fe)
    (hdq : X.s.dq ≤ SD.S.v.y.dq) (hfw : X.s.f ≤ SD.S.v.y.h.f) (hfef : X.s.fe ≤ SD.S.v.y.h.f)
    (hNE : X.s.NE ≤ SD.S.v.y.h.NE) (hTS : SD.S.TS = [0, 1, 2, 5])
    (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    (hstT : ∀ sh bl places, SD.S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd SD.S.v.y bl rs lam om H1 V sA sB = some s')
    (hzs : SD.S.zt.size = SD.S.v.y.h.lt) (hQK : X.QKOk)
    (Htok : ∀ i, i < 2 ^ X.D.lT → TokAll SD.S X.D (cellsOf X.D (cellsAt SD.S.v.y Mm)) X.tb
      (SD.S.ce.v.g * SD.S.ce.v.y.Lam) X.lk (zOf Reading.gl X.H.fo.zx X.H.fo.zy) i)
    (hJoin : X.Join W Mm (wmOf w.w))
    (hσ : W.slot X.tT.sCl = Reading.gl.val J.cube.total) :
    JoinWorth X.H X.tT X.parts W SD := by
  have ey : X.p.v.y = SD.S.v.y := by rw [Xp]; rfl
  have eTS : X.TS = SD.S.TS := by
    rw [hTS]
    exact ts_eq X.hy X.S.p3 X.hN X.hrd X.hTS
  obtain ⟨pans, hpan, hbl, _⟩ := stack_panels_at h
  have ep : X.pans = pans := by
    have q := X.hp
    rw [Xp, eTS] at q
    exact Option.some.inj (q.symm.trans hpan)
  have hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS =
      some X.cl := by
    have q := X.hcl
    rw [Xc, eTS] at q
    exact q
  have hst : stackEnd SD.S.v.y SD.bl X.c.rs X.lam X.om X.H1 X.V X.shownA X.shownB =
      some X.fin := by
    have q := X.hst
    rw [ey, ep, ← hbl] at q
    exact q
  have hlw : OnBytes.Model.wsLayOf X.s true X.lk = .ok Q.P.wsLay := by
    have q := X.hlw
    rw [Xc] at q
    rw [← sides_lay h]
    exact q
  have hv : SD.S.v.tab = X.r.1 := by
    have q := X.ht
    rw [Xp] at q
    exact q
  have hlt : X.D.lT = SD.S.v.y.h.lt := by
    rw [X.Z.lT, ← (admitted_of_layout X.hy X.S.p3).shape, ey]
  obtain ⟨_, tbI, I⟩ := stackIs_of h
  have hTT : SD.S.v.y.T = 2 ^ SD.S.v.y.h.lt := by
    have e : SD.S.v.y.T = 2 ^ X.D.lT := by rw [I.y]; exact N.T
    rw [e, hlt]
  have hf2 : X.D.f = 2 * X.D.fe := X.f2
  obtain ⟨hlen, hpw, Lz, Lw, Lp, hcap⟩ := parts_of_pub X Xρ hscl W Mm hW
    (SD.S.ce.v.g * SD.S.ce.v.y.Lam)
    (fun l => Inst.Model.FFSeg.layerR X.D.P X.lk (wmOf w.w) (SD.S.ce.v.g * SD.S.ce.v.y.Lam + l))
  rw [ey] at hpw
  obtain ⟨C, hk⟩ : X.D.ChOK ∧ ∀ l, l < X.D.nl → (X.D.Pl l).kq = (X.D.Pl l).kk ∨
      (16 ≤ (X.D.Pl l).kq ∧ 16 ≤ (X.D.Pl l).kk) := by
    subst hscl
    exact hQK
  have hB1 : (∑ q : Fin 8, Reading.gl.val (X.H.fo.e.getD q.val zeroE) *
        (Reading.gl.val X.alpha - (q.val : Cb.Gl.E) * Reading.gl.val X.theta -
          Blocks.ext (Inst.Model.FFSeg.aC X.D q)
            (Inst.Model.FFSeg.keyVec X.D (cellsOf X.D (cellsAt SD.S.v.y Mm)) X.tb
              (SD.S.ce.v.g * SD.S.ce.v.y.Lam)
              (fun l => Inst.Model.FFSeg.layerR X.D.P X.lk (wmOf w.w)
                (SD.S.ce.v.g * SD.S.ce.v.y.Lam + l)) q)
            (pt Reading.gl (X.p.v.zk.getD q.val #[])))) +
      Reading.gl.val (padOf X.H) - X.H.fo.cEnd.value Reading.gl W = 0 := by
    have q := hJoin
    unfold OnBytes.Road.Rows.Pub34.Join OnBytes.Road.Rows.Pub34.joinK at q
    rw [← hscl, Xρ, Xc, ey] at q
    have q' : X.H.fo.cEnd.value Reading.gl W =
        (∑ c : Fin 8, Inst.Model.FFSeg.wc X.D (zOf Reading.gl X.H.fo.zx X.H.fo.zy) c *
          (Reading.gl.val X.alpha - (c.val : Cb.Gl.E) * Reading.gl.val X.theta -
            Blocks.ext (Inst.Model.FFSeg.aC X.D c)
              (Inst.Model.FFSeg.keyVec X.D (cellsOf X.D (cellsAt SD.S.v.y Mm)) X.tb
                (SD.S.ce.v.g * SD.S.ce.v.y.Lam)
                (fun l => Inst.Model.FFSeg.layerR X.D.P X.lk (wmOf w.w)
                  (SD.S.ce.v.g * SD.S.ce.v.y.Lam + l)) c)
              (Inst.Model.FFSeg.zc X.D (zOf Reading.gl X.H.fo.zx X.H.fo.zy) c))) +
          Reading.gl.val (padOf X.H) := q
    rw [q', Finset.sum_congr rfl fun c _ => by
      rw [Lw c, OnBytes.Road.ext_congr_pt _ _ (Lz c)]]
    exact sub_self _
  exact joinWorth_one h hJ hcl X Xρ hscl Xp Xc W Mm hW hl hf hpp hm X.hNM hC hv hB rfl rfl rfl rfl
    rfl rfl hts htu Ss Su N hnl hlw hd hfew hdq hfw hfef hNE hTS hom hst hstT hzs hTT hf2 hlt
    (fun j hj => by rw [hzt]; exact Lp j hj) C hk Htok
    (fun q => pt Reading.gl (X.p.v.zk.getD q.val #[])) X.H X.parts X.hT hlen X.alpha X.theta hpw
    hcap (by omega) (fun q _ => Lz q) (fun q _ => Lw q) hB1 hσ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinWorth_x
