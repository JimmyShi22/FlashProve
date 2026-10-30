-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinOne.lean: CONDITIONAL.

What is here. The hypothesis `JoinWorth` (StackStart.lean: the first pass of the batched sumcheck is
the lookup's join) IN ONE WORLD: JoinPub.lean's `joinWorth_pub` with the world of the first pass's
panels taken to be the world W of the start form, and three of its hypotheses paid there. `SigFits`
comes from SigOfPub.lean's `sig_of_pub`, of one of the library's public structures `Pub34` whose two
environments are the honest side's. That the honest value of each form of a panel is the form's
value comes from HvalOf.lean's `hval_true`. That the never-sent vector number 0 is the library's
vector of the gated products comes from GatedOf.lean's `hv0_gated`. The first two ask of W its
entries alone: they are the true ones at X's tables and the matrices Mm; its slots are free. The
third names no world.

  `joinWorth_one`   **the one statement**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (X; hpw). NOTHING NEW IS SHOWN: one call of
each. LEFT AS HYPOTHESES, ALL:
  on the lookup: (B1) its own part is worth 0 at the library's key vectors;
  on the world W: its entries are the true ones (hW); the slot of the claimed sum holds the honest
  job's total (hσ); each of the eight factors is worth what the library's `joinPart_keyVec'`
  concludes (hpw, hlen);
  on the structure X: it is given, at this reading; its two environments are the honest side's (Xp,
  Xc); its list of tables is the verifier's at points of which the honest named points are a part
  (hf, hpp); its sub-proof's matrices are the plan's (hm, hNM); the table of scales is X's (hscl);
  on the honest input: on every matrix but that of the lookup's planes Mm holds its cells
  (`CellsAre`); its two tensors of the gated products read as the library's values (`TensorIs`);
  on the lookup's points and weights: hzq, hwc, hzp, hzs;
  at each token: `TokAll` (JoinPub.lean);
  public: the layout of the weights with two equations and four inequalities; twelve numbers
  (`GatedNums`); the environment's list of places (hv, hB); the calls of the second walk; the layout
  has the two tensors of the gated products (hts, htu); sizes;
  returns: h, hJ, hcl, hl, hst, hstT; the hearing holds the second token sumcheck's structure (hTs);
  the first of the two weights reads 1 (hom).
No example of the hypotheses together is known.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinPub
import Johnson.Desc.ProofFile.Honest.K4.Law.SigOfPub
import Johnson.Desc.ProofFile.Honest.K4.Law.HvalOf
import Johnson.Desc.ProofFile.Honest.K4.Law.GatedOf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE)
open OnBytes.Model (Reading Aff World Tsc WsShape WsClaim wsLayOf)
open OnBytes.Model.Layer (Heard ClaimEnv StackEnd stackEnd Ten TableAsk TableAt layTables tableAsks
  funsOf)
open OnBytes.Road (pt padOf elP ACCP TSP sclOf cellsAt cellsOf zOf Mats)
open OnBytes.Road.K4 (entryOf)
open OnBytes.Road.K4.C (sidesEnv stack_open stack_panels_at CellsAre PtsPart TensorIs GatedNums)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim Cell wc famsIn zpos zc aC keyVec layerR)
open OnBytes.Desc.First.K4.Honest

/-- **`JoinWorth`, IN ONE WORLD.** CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE. Six
letters are named by equations (D, lk, L0, t, z, tb: X's); the rest reads as `joinWorth_pub`. -/
theorem joinWorth_one [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} (h : stackData Q w p shownT = some SD) {J : Job}
    (hJ : jobTermsOn SD.S = some J) {rs : Array E} {cl : List WsClaim}
    (hcl : ({ SD.S.ce with rs := rs, rt := p.rt } : ClaimEnv).weightClaims SD.S.TS = some cl)
    (X : OnBytes.Road.Rows.Pub34 Cb.Gl.E) (Xρ : X.ρ = Reading.gl)
    (hscl : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam) (Xp : X.p = sidesEnv SD.S shownT)
    (Xc : X.c = { SD.S.ce with rs := rs, rt := p.rt }) (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm)
    {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    (hl : layTables (matsOf Q) (tableAsks Q.P.y Q.P.rd Q.g) 0 = some r)
    {fo' : OnBytes.Model.Forest.Heard} {pts : List (String × Array E)}
    (hf : funsOf Q.P.y fo' pts r.2.1 = some X.funs) (hpp : PtsPart (namedPts Q p) pts)
    (hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q) (hNM : X.tl.NM = X.tl.mats.size)
    (hC : CellsAre Q w Mm) (hv : SD.S.v.tab = r.1) {tB0 : ℕ}
    (hB : SD.S.v.tabAt "b-bits-0" = some tB0)
    {D : Dim} (hD : D = X.D) {lk : ℕ} (hlk : lk = X.lk) {L0 : ℕ}
    (hL0 : L0 = SD.S.ce.v.g * SD.S.ce.v.y.Lam) {t : Cell → Cb.Gl.E}
    (ht : t = cellsOf X.D (cellsAt SD.S.v.y Mm)) {z : ℕ → Cb.Gl.E}
    (hz : z = zOf Reading.gl X.H.fo.zx X.H.fo.zy) {tb : Tables} (htb : tb = X.tb)
    {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts) (htu : Q.P.y.T_ "u" = some tu)
    (Ss : TensorIs Q w t .sl ts) (Su : TensorIs Q w t .up tu) (N : GatedNums Q D)
    (hnl : D.nl ≤ 2 ^ D.lL)
    {sw : WsShape} {lkw : ℕ} (hlw : wsLayOf sw true lkw = .ok Q.P.wsLay)
    (hd : sw.d = SD.S.v.y.h.d) (hfew : sw.fe = SD.S.v.y.h.fe) (hdq : sw.dq ≤ SD.S.v.y.dq)
    (hfw : sw.f ≤ SD.S.v.y.h.f) (hfef : sw.fe ≤ SD.S.v.y.h.f) (hNE : sw.NE ≤ SD.S.v.y.h.NE)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    {rs' H1 V om : Array E} {lam : ℕ} {sA sB : E} {s' : StackEnd}
    (hst : stackEnd SD.S.v.y SD.bl rs' lam om H1 V sA sB = some s')
    (hstT : ∀ sh bl places, SD.S.panels sh = some (bl, places) → ∃ rs om H1 V lam sA sB s',
      stackEnd SD.S.v.y bl rs lam om H1 V sA sB = some s')
    (hzs : SD.S.zt.size = SD.S.v.y.h.lt) (hTT : SD.S.v.y.T = 2 ^ SD.S.v.y.h.lt)
    (hf2 : D.f = 2 * D.fe) (hlt : D.lT = SD.S.v.y.h.lt)
    (hzp : ∀ j, j < D.lT → zpos D z j = pt Reading.gl SD.S.zt j) (C : D.ChOK)
    (hk : ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (Htok : ∀ i, i < 2 ^ D.lT → TokAll SD.S D t tb L0 lk z i)
    (ζ : Fin 8 → ℕ → Cb.Gl.E) (H : Heard) (parts : List Aff) {tT : Tsc}
    (hTs : H.tT = some tT) (hlen : parts.length = 8) (alpha theta : E)
    (hpw : ∀ (q : Fin 8) (f : Aff), parts[q.val]? = some f →
      f.value Reading.gl W = Reading.gl.val alpha - (q.val : Cb.Gl.E) * Reading.gl.val theta -
        Blocks.ext (aC D q)
          (keyVec D t tb L0 (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) q) (ζ q) +
        TSP D t tb L0 (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) q (ζ q) +
        ∑ l ∈ Finset.range D.nl, elP D (ζ q) l * ((famsIn q l).map fun s =>
          ACCP D t (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) (ζ q) s l).sum)
    (hcap : D.lT ≤ D.cap) (hfe2 : D.fe ≤ D.f)
    (hzq : ∀ q : Fin 8, q ∈ [(0 : Fin 8), 1, 2, 5] → ∀ j, j < aC D q → ζ q j = zc D z q j)
    (hwc : ∀ q : Fin 8, q ∈ [(0 : Fin 8), 1, 2, 5] →
      Reading.gl.val (H.fo.e.getD q.val zeroE) = wc D z q)
    (hB1 : (∑ q : Fin 8, Reading.gl.val (H.fo.e.getD q.val zeroE) *
        (Reading.gl.val alpha - (q.val : Cb.Gl.E) * Reading.gl.val theta -
          Blocks.ext (aC D q)
            (keyVec D t tb L0 (fun l => layerR D.P lk (wmOf w.w) (L0 + l)) q) (ζ q))) +
      Reading.gl.val (padOf H) - H.fo.cEnd.value Reading.gl W = 0)
    (hσ : W.slot tT.sCl = Reading.gl.val J.cube.total) :
    JoinWorth H tT parts W SD := by
  subst hD hlk hL0 ht hz htb
  obtain ⟨pans, hpan, hbl, _⟩ := stack_panels_at h
  have hW' : W.entry = entryOf Reading.gl X.tl X.funs (sidesEnv SD.S shownT).v.iU3
      (sidesEnv SD.S shownT).v.K3 Mm := by
    rw [hW, Xρ, Xp]
  have hval : ∀ b ∈ SD.bl.toList, b.claim = 0 → ∀ a, FormOf b a → ∀ y,
      valAff? SD.S.v SD.R (fun _ => zeroE) a = some y →
        Reading.gl.val y = a.value Reading.gl W := fun b hb _ =>
    hval_true (stack_open h).2.1 hl hf hpp hm hNM hC (pe := sidesEnv SD.S shownT) hv hB hpan hW' b
      (by rw [← hbl]; exact hb)
  exact joinWorth_pub h hJ hcl hlw hd hfew hdq hfw hfef hNE W hval
    (sig_of_pub X Xρ hscl Xp Xc W Mm hW) hTS hom hst hstT hzs hTT hf2 hlt hzp C hk Htok ζ W H parts
    hTs hlen alpha theta hpw hcap hfe2 hzq hwc
    (hv0_gated h hts htu Ss Su N (hzs.trans hlt.symm) _ hzp hnl hfe2) hB1 hσ

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinWorth_one
