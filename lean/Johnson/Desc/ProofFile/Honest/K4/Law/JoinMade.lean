-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/JoinMade.lean: CONDITIONAL.

What is here. `JoinWorth` at a hearing of K4's own text, in the shape in which StackWhole.lean's
`stack_whole` asks it, WITH NO PUBLIC STRUCTURE AMONG THE HYPOTHESES: the library's maker
`pub34_of_hear_run` (Johnson/Road/K4/PubOfHearTied.lean) is called, and JoinRun.lean's
`joinWorth_run` at what it returns. Every hypothesis stands in the letters of the hearing (o), of
the plan (Q) and of the library's sizes and tables (hS pc D s lk tb s0 tl). The lookup's own part
stands in the heard letters: JoinSpell.lean's `join_iff_part` turns it into the library's `Join`.

  `joinWorth_made`   **`JoinWorth` in `stack_whole`'s shape; no public structure among the
     hypotheses**

Limits. At the reading `Reading.gl`. THE FULL SIZE ALONE (hfl). NOTHING NEW IS SHOWN: calls and
rewritings. HYPOTHESES, ALL:
  the maker's own, to the letter, at this reading and at the plan with the tokens tk laid in: public
  lines of the plan; what the lookup heard (hsx hsy hzk he hpt); the rotary tables fit at every end
  point (R: no more than at one: RopeAny.lean's `ropeFits_rt`); hinv;
  six ties of the honest side to the hearing: tv te tz hfo; what stands for the shown values is what
  the ledger shows at which the batched sumcheck's stretch began (hsh); the end point (trt);
  on the world W: its entries are the true ones at what the hearing returned (hW); the lookup's own
  part is worth 0 at the library's key vectors (hB1); the slot of the claimed sum holds the honest
  job's total (hσ);
  on the honest input: `CellsAre`; `TensorIs` twice;
  public: the honest named points are a part of the verifier's (hpp); the table of scales (hscl);
  what the library's law on the panel of queries and keys asks (hQK); `GatedNums`; hdq (it follows
  from Zw, Z and the layout, as in Johnson/Road/K4/C/WsFacts.lean's `ws_facts`; asked all the same)
  hTS hnl hne;
  the two tensors are found;
  returns: h hJ hH; hom.
No example of the hypotheses together is known. WHAT THIS FILE's IMPORTS REACH, by a program's walk
over import lines that stops, unopened, at every module under Johnson/Goal/, Johnson/D/,
Johnson/Bridge/, Cb/Bridge* or ThirdParty/: it stopped at two modules under Johnson/Bridge/ and at
none under the others; it saw seven modules whose names hold RecCompile, none of them
RecCompile.Honest…, RecCompile.Both… or RecCompile.PassH…. What lies behind the two is not counted:
the numbers are floors. A LAW, NOT A PART: no file that defines a part of the proof file's
description may import this one.

No property is claimed.
-/
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinRun
import Johnson.Desc.ProofFile.Honest.K4.Law.JoinSpell
import Johnson.Road.K4.PubOfHearTied

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4
open OnBytes (E zeroE negE invE ofF)
open OnBytes.Model (Reading Aff World Tsc Fork WsShape HTailF2 wsLayOf)
open OnBytes.Model.Layer (Own Ten Heard layout scalesHeld pointsOf nEndT)
open OnBytes.Road (pt padOf sclOf cellsAt cellsOf Mats RopeFits Switches Numerals Sized SizedW
  LinesAre matsR)
open OnBytes.Road.K4 (entryOf pub34_of_hear_run env_of_hear)
open OnBytes.Road.K4.C (CellsAre PtsPart TensorIs GatedNums)
open OnBytes.Desc.First.K4 (engFl hear hearNorms hearTerms)
open Inst.Model (Scl Tables)
open Inst.Model.FFSeg (Dim used lut aC keyVec layerR)
open OnBytes.Desc.First.K4.Honest

/-- **`JoinWorth` AT A HEARING, IN `stack_whole`'s SHAPE; NO PUBLIC STRUCTURE IS ASKED.**
CONDITIONAL: on every hypothesis named. THE FULL SIZE ALONE (hfl). The first block is the library's
maker's, at the plan with the tokens tk laid in ({ Q.P with tokv := tk }). -/
theorem joinWorth_made [scl : Scl] {Q : K4Pub} {w : K4In} {p : Pts} {shownT : Array E}
    {SD : StackData} {tk : Array ℕ} {fo : OnBytes.Model.Forest.Heard} {F G : Fork}
    {t u : OnBytes.K.Kc.Tape} {o : Own}
    (hH : hear engFl { Q.P with tokv := tk } Q.hp Q.g fo F t = some (o, G, u))
    {hS : OnBytes.Model.Layer.Shape} {pc : List (List String)} {D : Dim} {s : WsShape} {lk : ℕ}
    {tb : Tables} {s0 : OnBytes.Model.Forest.Shape} {tl : HTailF2}
    (hy : layout hS pc = .ok Q.P.y) (S : Switches hS) (hs : scalesHeld hS Q.P.sc = .ok ())
    (hg : Q.g < Q.P.y.NGr) (hrd : OnBytes.Model.Layer.readsOf Q.P.y = .ok Q.P.rd)
    (hmats : ((Q.P.tails.getD Q.g {}).mats.map fun M => (M.m, M.k)) = matsR Q.P.y Q.g)
    (hρ : Numerals Reading.gl) (Z : Sized hS D) (hc : D.cap = hS.lidb) (hN : LinesAre Q.P.y)
    (hfl : ∀ k : Fin 8, hS.nmin - hS.ll - hS.lt ≤ Nat.clog 2 (used D k))
    (hsx : fo.zx.size = Q.P.y.fo.dT) (hsy : fo.zy.size = Q.P.y.fo.rK)
    (hzk : fo.zk = (Array.range Q.P.y.fo.NC).map fun q =>
      fo.zy.extract (Q.P.y.fo.rK - Q.P.y.fo.iota.getD q 0) fo.zy.size ++ fo.zx)
    (he : fo.e = (Array.range Q.P.y.fo.NC).map (OnBytes.Model.Forest.callWeight Q.P.y.fo fo.zy))
    (hs0 : OnBytes.Model.Forest.shape Q.P.y.cl Q.P.y.h.lidb = .ok s0)
    (hpt : ((List.range s0.NC).all fun q =>
      (fo.zk.getD q #[]).size == ((s0.calls[q]?).map (·.n)).getD 0) = true)
    (Zw : SizedW s D.P) (hsL : s.L = hS.L) (hlw : wsLayOf s true lk = .ok Q.P.wsLay)
    (h4 : hS.p4 = true)
    (R : ∀ (rt : Array E) (lam : ℕ), lam < Q.P.y.Lam →
      RopeFits Reading.gl
        { v := o.v, wsLay := Q.P.wsLay, rope := Q.P.rope, rs := o.K.rs, rt := rt } D tb
        (Q.g * Q.P.y.Lam) lam)
    (htm : (tl.mats.map fun M => (M.m, M.k)) = matsR Q.P.y Q.g) (hNM : tl.NM = tl.mats.size)
    (hpad : ∀ k : Fin 8,
      Reading.gl.val (ofF ((Q.P.y.cl.getD k.val {}).tauAt (Q.P.y.cl.getD k.val {}).t0)) =
        (((lut tb k).pad : ℤ) : Cb.Gl.E))
    (hinv : ∀ tT, o.H.tT = some tT →
      Reading.gl.val (negE (invE tT.p.eps)) * Reading.gl.val tT.p.eps = -1)
    -- the honest side
    (h : stackData Q w p shownT = some SD) {J : Job} (hJ : jobTermsOn SD.S = some J)
    (tv : SD.S.v = o.v) (te : SD.S.fo.e = o.H.fo.e) (tz : SD.S.zt = o.H.ztF)
    (hfo : p.fo.zx = o.H.fo.zx)
    (hsh : ∀ (H1 : Heard) (G1 G2 : Fork) (u1 u2 : OnBytes.K.Kc.Tape) (tT' : Tsc) (a : Array E),
      hearNorms engFl { Q.P with tokv := tk } Q.g fo F t = some (H1, G1, u1) →
      hearTerms engFl { Q.P with tokv := tk } H1 G1 u1 = some (o.H, G2, u2) →
      o.H.tT = some tT' →
      ((Array.range (nEndT Q.P.y)).mapM fun i => G2.shown (tT'.sEnd + i)) = some a → a = shownT)
    (trt : ∀ tT', o.H.tT = some tT' → p.rt = tT'.r)
    (hscl : scl = sclOf hS o.v.sc o.v.g o.v.y.Lam) (W : World Cb.Gl.E) (Mm : Mats Cb.Gl.E)
    (hW : W.entry = entryOf Reading.gl tl o.funs o.v.iU3 o.v.K3 Mm)
    (hpp : ∀ pts, pointsOf Q.P.y o.H o.hd o.hd2 = some pts → PtsPart (namedPts Q p) pts)
    (hC : CellsAre Q w Mm) {ts tu : Ten} (hts : Q.P.y.T_ "s" = some ts)
    (htu : Q.P.y.T_ "u" = some tu) (Ss : TensorIs Q w (cellsOf D (cellsAt SD.S.v.y Mm)) .sl ts)
    (Su : TensorIs Q w (cellsOf D (cellsAt SD.S.v.y Mm)) .up tu) (N : GatedNums Q D)
    (hnl : D.nl ≤ 2 ^ D.lL) (hne : 2 * D.ne ≤ 2 ^ D.lL) (hdq : s.dq ≤ SD.S.v.y.dq)
    (hTS : SD.S.TS = [0, 1, 2, 5]) (hom : Reading.gl.val (SD.om.getD 0 zeroE) = 1)
    (hQK : D.ChOK ∧ ∀ l, l < D.nl →
      (D.Pl l).kq = (D.Pl l).kk ∨ (16 ≤ (D.Pl l).kq ∧ 16 ≤ (D.Pl l).kk))
    (hB1 : (∑ q : Fin 8, Reading.gl.val (o.H.fo.e.getD q.val zeroE) *
        (Reading.gl.val o.H.fo.alpha - (q.val : Cb.Gl.E) * Reading.gl.val o.H.fo.theta -
          Blocks.ext (aC D q)
            (keyVec D (cellsOf D (cellsAt o.v.y Mm)) tb (o.v.g * o.v.y.Lam)
              (fun l => layerR D.P lk (wmOf w.w) (o.v.g * o.v.y.Lam + l)) q)
            (pt Reading.gl (o.v.zk.getD q.val #[])))) +
      Reading.gl.val (padOf o.H) - o.H.fo.cEnd.value Reading.gl W = 0)
    (hσ : ∀ tT', o.H.tT = some tT' → W.slot tT'.sCl = Reading.gl.val J.cube.total) :
    ∀ (weighed : Array _) (parts : List Aff) (tT' : Tsc),
      o.v.y.calls.mapM o.v.weighedOf = some weighed →
      ((o.v.y.calls.zip weighed).toList.zipIdx.mapM fun x =>
        o.v.joinPart o.H.fo.alpha o.H.fo.theta x.2 x.1.1 x.1.2) = some parts →
      o.H.tT = some tT' → JoinWorth o.H tT' parts W SD := by
  obtain ⟨X, eρ, eH, ev, _, _, _, _, _, _, ehd, ehd2, efun, _, erd, eD, eh, _, es, elk, etb, _, etl,
    eα, eθ, eT, ec, ep, _, H1, G1, G2, _, _, u1, u2, _, n1, n2, _, _, _, esh, _⟩ :=
    pub34_of_hear_run Reading.gl hH hy S hs hg hrd hmats hρ Z hc hN hfl hsx hsy hzk he hs0 hpt Zw
      hsL hlw h4 R htm hNM hpad hinv
  obtain ⟨vy, _, vg, _⟩ := env_of_hear hH
  have vy' : o.v.y = Q.P.y := vy
  have T : HeardX X { Q.P with tokv := tk } o := ⟨eρ, eH, ev, eα, eθ, eT, ec, ep⟩
  have hscl' : scl = sclOf X.h X.p.v.sc X.p.v.g X.p.v.y.Lam := by rw [eh, ev]; exact hscl
  have hW' : W.entry = entryOf X.ρ X.tl X.funs X.p.v.iU3 X.p.v.K3 Mm := by
    rw [eρ, etl, efun, ev]
    exact hW
  have hl : OnBytes.Model.Layer.layTables (matsOf Q)
      (OnBytes.Model.Layer.tableAsks Q.P.y Q.P.rd Q.g) 0 = some X.r := by
    have q := X.hl
    rw [ev, vy', vg, erd, ← hmats] at q
    exact q
  have hpp' : PtsPart (namedPts Q p) X.pts := by
    refine hpp X.pts ?_
    have q := X.hpts
    rw [ev, vy', eH, ehd, ehd2] at q
    exact q
  have hm : (X.tl.mats.map fun M => (M.m, M.k)) = matsOf Q := by
    rw [etl, htm, ← hmats]
    rfl
  have hQK' : X.QKOk := by
    unfold OnBytes.Road.Rows.Pub34.QKOk
    rw [← hscl', eD]
    exact hQK
  have hJoin : X.Join W Mm (wmOf w.w) := by
    refine (join_iff_part X eρ hscl' W Mm (wmOf w.w)).2 ?_
    rw [eH, eα, eθ, eD, etb, elk, ev, ec]
    exact hB1
  rw [← eD] at Ss Su N hnl hne
  rw [← es] at hdq
  exact joinWorth_run h hJ hH T tv te tz (hsh H1 G1 G2 u1 u2 X.tT X.p.shownT n1 n2 eT esh)
    (trt _ eT) hscl' W Mm hW' hl hpp' hm hC hts htu Ss Su N hnl hne hdq hTS hom hQK' hfo hJoin
    (hσ _ eT)

end ProofFile.Honest.K4

#print axioms ProofFile.Honest.K4.joinWorth_made
